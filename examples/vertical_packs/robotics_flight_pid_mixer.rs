#![no_std]

//! Vertical Pack 6 — Safety-Critical Robotics / Aerospace Control
//! (Stateful Inductive IEEE-754 `QF_ABVFP` Flight PID Controller + `f32x4` Quadrotor 4-Motor Mixer)
//!
//! Exercises Gnomon's exact IEEE-754 `QF_ABVFP` bit-precise floating-point + `v128` SIMD engine
//! on safety-critical cyber-physical control software:
//! 1. **Stateful Flight PID + Anti-Windup + Slew-Rate + E-Stop Controller (`globals: 0`):**
//!    - Persistent IEEE-754 `f32` state stored in static linear memory (`INTEGRATOR_BITS`,
//!      `PREV_OUT_BITS`, `ESTOP_LATCH` via `AtomicU32`, zero shadow stack).
//!    - Inductive safety invariant `inv_pid_safe()` proved across arbitrary sequences of
//!      `step_pid` and `clear_estop` over ALL `f32` inputs (including `NaN`, `±Inf`, subnormals, `-0.0`):
//!      - `INTEGRATOR` is always finite, never `NaN`, never `-0.0`, strictly in `[-10.0, +10.0]`
//!      - `PREV_OUT` is always finite, never `NaN`, never `-0.0`, strictly in `[-1.0, +1.0]`
//!      - Latched E-stop guarantees `PREV_OUT == +0.0` and `INTEGRATOR == +0.0`.
//!    - Inline contracts:
//!      - `contract_estop_forces_zero`: `estop != 0` ALWAYS returns `+0.0` even under `NaN`/`±Inf`
//!        sensors AND remains latched at `+0.0` on subsequent ticks when `estop_in == 0`!
//!      - `contract_nan_sensor_never_poisons`: `NaN`/`±Inf` sensor faults NEVER taint `INTEGRATOR`!
//!      - `contract_slew_rate_bounded`: valid control steps obey the mathematically sharp IEEE-754
//!        1-ULP bound `|out - old_prev| <= 0.25 + 2^-25` (`0x3E80_0001`; `0.25` is `FALSIFIED`)!
//! 2. **Quadrotor X-Frame 4-Motor PWM Mixer (`quad_mixer_4_scalar` vs `quad_mixer_4_v128` & `quad_mixer_4_opt`):**
//!    - Mixes `(thrust, roll, pitch, yaw)` into 4× 12-bit PWM commands `[0..=4095]` packed in `u64`.
//!    - Proved bit-exact equivalent (`quad_mixer_4_v128 ≡ quad_mixer_4_scalar` AND
//!      `quad_mixer_4_opt ≡ quad_mixer_4_scalar`) across ALL `2^160` IEEE-754 inputs in `QF_ABVFP`.
//!    - Proved `ens_quad_mixer_safe`: every motor PWM is in `0..=4095`, `estop != 0 => 0`,
//!      and any `NaN`/`±Inf` sensor input deterministically yields safe idle `0` (never full throttle!).
//!    - Portable native profile pair (`quad_mixer_4_scalar` vs `quad_mixer_4_opt`) profiled on
//!      x86-64 (`skylake`) & ARM64 (`neoverse-v2` NEON) + live host `--bench`.

use core::sync::atomic::{AtomicU32, Ordering};

#[cfg(target_arch = "wasm32")]
use core::arch::wasm32::*;

#[cfg(target_arch = "wasm32")]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

#[cfg(target_arch = "wasm32")]
#[link(wasm_import_module = "gnomon")]
unsafe extern "C" {
    fn gnomon_assume(cond: i32);
    fn gnomon_assert(cond: i32);
}

#[cfg(target_arch = "wasm32")]
#[inline(always)]
fn assume(cond: bool) {
    unsafe {
        gnomon_assume(if cond { 1 } else { 0 });
    }
}

#[cfg(target_arch = "wasm32")]
#[inline(always)]
fn assert_prop(cond: bool) {
    unsafe {
        gnomon_assert(if cond { 1 } else { 0 });
    }
}

// ============================================================================
// Part 1: Stateful Inductive IEEE-754 Flight PID + Anti-Windup + E-Stop
// ============================================================================

const KP: f32 = 0.5;
const KI: f32 = 0.125;
const I_MAX: f32 = 10.0;
const U_MAX: f32 = 1.0;
const MAX_SLEW: f32 = 0.25;
const SENSOR_LIM: f32 = 1000.0;
const DT_MAX: f32 = 0.5;

// Persistent flight-controller state in fixed linear-memory slots (globals: 0).
static INTEGRATOR_BITS: AtomicU32 = AtomicU32::new(0);
static PREV_OUT_BITS: AtomicU32 = AtomicU32::new(0);
static ESTOP_LATCH: AtomicU32 = AtomicU32::new(0);

/// NaN-safe, `-0.0`-normalized IEEE-754 clamp onto `[lo, hi]` (for `lo <= 0.0 <= hi`).
/// Unlike naive `if v > hi { hi } else if v < lo { lo } else { v }`, a `NaN` input NEVER
/// escapes this clamp and deterministically yields `+0.0`.
#[inline(always)]
fn clamp_nan_safe(v: f32, lo: f32, hi: f32) -> f32 {
    let out = if v >= lo && v <= hi {
        v
    } else if v > hi {
        hi
    } else if v < lo {
        lo
    } else {
        0.0
    };
    if out == 0.0 { 0.0 } else { out }
}

/// Initialize flight PID controller to armed neutral state (`I = +0.0, prev = +0.0, estop = 0`).
#[unsafe(no_mangle)]
pub extern "C" fn init_pid() -> i32 {
    INTEGRATOR_BITS.store(0, Ordering::Relaxed);
    PREV_OUT_BITS.store(0, Ordering::Relaxed);
    ESTOP_LATCH.store(0, Ordering::Relaxed);
    1
}

/// Inductive IEEE-754 safety invariant for the stateful flight PID controller:
/// - `ESTOP_LATCH` is boolean (`0` or `1`)
/// - `INTEGRATOR` is finite, not `NaN`, not `-0.0`, and strictly in `[-10.0, +10.0]`
/// - `PREV_OUT` is finite, not `NaN`, not `-0.0`, and strictly in `[-1.0, +1.0]`
/// - If `ESTOP_LATCH == 1`, both `INTEGRATOR` and `PREV_OUT` are strictly `+0.0`.
#[unsafe(no_mangle)]
pub extern "C" fn inv_pid_safe() -> i32 {
    // SAFETY: Volatile reads emit plain Wasm loads while preventing LLVM GlobalOpt
    // from folding away symbolic pre-state checks on private statics (`globals: 0`).
    let (i_bits, p_bits, estop) = unsafe {
        (
            core::ptr::read_volatile(INTEGRATOR_BITS.as_ptr()),
            core::ptr::read_volatile(PREV_OUT_BITS.as_ptr()),
            core::ptr::read_volatile(ESTOP_LATCH.as_ptr()),
        )
    };
    let integ = f32::from_bits(i_bits);
    let prev = f32::from_bits(p_bits);

    let estop_bool = (estop == 0) | (estop == 1);
    let integ_ok = (integ >= -I_MAX) & (integ <= I_MAX) & (i_bits != 0x8000_0000);
    let prev_ok = (prev >= -U_MAX) & (prev <= U_MAX) & (p_bits != 0x8000_0000);
    let latch_zero = (estop == 0) | ((i_bits == 0) & (p_bits == 0));

    if estop_bool & integ_ok & prev_ok & latch_zero {
        1
    } else {
        0
    }
}

/// Execute one closed-loop flight PID step with anti-windup, slew-rate limiting, sensor fault
/// isolation, and latching emergency stop (`estop_in != 0`).
#[unsafe(no_mangle)]
pub extern "C" fn step_pid(setpoint: f32, measured: f32, dt: f32, estop_in: i32) -> f32 {
    let latched = ESTOP_LATCH.load(Ordering::Relaxed);
    if estop_in != 0 || latched != 0 {
        ESTOP_LATCH.store(1, Ordering::Relaxed);
        INTEGRATOR_BITS.store(0, Ordering::Relaxed);
        PREV_OUT_BITS.store(0, Ordering::Relaxed);
        return 0.0;
    }

    // Reject NaN, ±Inf, out-of-range IMU readings, or non-positive/excessive dt without
    // poisoning `INTEGRATOR_BITS`.
    let sensor_ok = (setpoint >= -SENSOR_LIM)
        & (setpoint <= SENSOR_LIM)
        & (measured >= -SENSOR_LIM)
        & (measured <= SENSOR_LIM)
        & (dt > 0.0)
        & (dt <= DT_MAX);
    if !sensor_ok {
        PREV_OUT_BITS.store(0, Ordering::Relaxed);
        return 0.0;
    }

    let integ = f32::from_bits(INTEGRATOR_BITS.load(Ordering::Relaxed));
    let prev = f32::from_bits(PREV_OUT_BITS.load(Ordering::Relaxed));

    let err = setpoint - measured;
    let next_i = clamp_nan_safe(integ + (err * dt) * KI, -I_MAX, I_MAX);
    let raw_u = clamp_nan_safe(err * KP + next_i, -U_MAX, U_MAX);
    let delta = clamp_nan_safe(raw_u - prev, -MAX_SLEW, MAX_SLEW);
    let next_u = clamp_nan_safe(prev + delta, -U_MAX, U_MAX);

    INTEGRATOR_BITS.store(next_i.to_bits(), Ordering::Relaxed);
    PREV_OUT_BITS.store(next_u.to_bits(), Ordering::Relaxed);
    next_u
}

/// Explicitly disarm E-stop latch after operator reset (starts cleanly from neutral `+0.0`).
#[unsafe(no_mangle)]
pub extern "C" fn clear_estop() -> i32 {
    ESTOP_LATCH.store(0, Ordering::Relaxed);
    INTEGRATOR_BITS.store(0, Ordering::Relaxed);
    PREV_OUT_BITS.store(0, Ordering::Relaxed);
    1
}

// ============================================================================
// Inline Cyber-Physical Safety Contracts (`gnomon_assume` / `gnomon_assert`)
// ============================================================================

/// Proves that whenever `estop_in != 0` — EVEN with `NaN`/`±Inf` sensor inputs —
/// `step_pid` deterministically outputs `+0.0`, latches `ESTOP_LATCH = 1`, zeroes `INTEGRATOR`,
/// preserves `inv_pid_safe()`, AND remains latched at `+0.0` on a subsequent tick with
/// `estop_in == 0` and arbitrary new sensor readings `(sp2, meas2, dt2)`.
#[cfg(target_arch = "wasm32")]
#[unsafe(no_mangle)]
pub extern "C" fn contract_estop_forces_zero(
    setpoint: f32,
    measured: f32,
    dt: f32,
    estop_in: i32,
    sp2: f32,
    meas2: f32,
    dt2: f32,
) -> i32 {
    assume(inv_pid_safe() == 1);
    assume(estop_in != 0);
    let out = step_pid(setpoint, measured, dt, estop_in);
    assert_prop(out.to_bits() == 0);
    assert_prop(ESTOP_LATCH.load(Ordering::Relaxed) == 1);
    assert_prop(INTEGRATOR_BITS.load(Ordering::Relaxed) == 0);
    assert_prop(inv_pid_safe() == 1);

    // Latched persistence: even after `estop_in` drops to `0`, output stays `+0.0` until `clear_estop()`.
    let out_latched = step_pid(sp2, meas2, dt2, 0);
    assert_prop(out_latched.to_bits() == 0);
    assert_prop(ESTOP_LATCH.load(Ordering::Relaxed) == 1);
    assert_prop(INTEGRATOR_BITS.load(Ordering::Relaxed) == 0);
    assert_prop(inv_pid_safe() == 1);
    1
}

/// Proves that ANY `NaN` or `±Inf` sensor glitch NEVER poisons `INTEGRATOR` (remains unchanged
/// and finite in `[-10.0, 10.0]`), returns safe `+0.0`, and preserves `inv_pid_safe()`.
#[cfg(target_arch = "wasm32")]
#[unsafe(no_mangle)]
pub extern "C" fn contract_nan_sensor_never_poisons(setpoint: f32, measured: f32, dt: f32) -> i32 {
    assume(inv_pid_safe() == 1);
    assume(ESTOP_LATCH.load(Ordering::Relaxed) == 0);
    let old_i_bits = INTEGRATOR_BITS.load(Ordering::Relaxed);
    let faulty = !(setpoint >= -SENSOR_LIM && setpoint <= SENSOR_LIM)
        || !(measured >= -SENSOR_LIM && measured <= SENSOR_LIM)
        || !(dt > 0.0 && dt <= DT_MAX);
    assume(faulty);

    let out = step_pid(setpoint, measured, dt, 0);
    assert_prop(out.to_bits() == 0);
    assert_prop(INTEGRATOR_BITS.load(Ordering::Relaxed) == old_i_bits);
    assert_prop(inv_pid_safe() == 1);
    1
}

/// Proves that during armed normal operation, actuator slew rate obeys the mathematically sharp
/// IEEE-754 `f32` 1-ULP bound `|out - old_prev| <= MAX_SLEW + 2^-25` (`0x3E80_0001`, where
/// `|out - old_prev| <= MAX_SLEW` itself is `FALSIFIED` due to rounding of `prev + delta` in
/// `[0.5, 1.0)` with `0.5 * ULP = 2^-25`) and `|out| <= 1.0`.
#[cfg(target_arch = "wasm32")]
#[unsafe(no_mangle)]
pub extern "C" fn contract_slew_rate_bounded(setpoint: f32, measured: f32, dt: f32) -> i32 {
    assume(inv_pid_safe() == 1);
    assume(ESTOP_LATCH.load(Ordering::Relaxed) == 0);
    assume(setpoint >= -SENSOR_LIM && setpoint <= SENSOR_LIM);
    assume(measured >= -SENSOR_LIM && measured <= SENSOR_LIM);
    assume(dt > 0.0 && dt <= DT_MAX);

    let old_prev = f32::from_bits(PREV_OUT_BITS.load(Ordering::Relaxed));
    let out = step_pid(setpoint, measured, dt, 0);
    let diff = (out - old_prev).abs();
    // Exact sharp IEEE-754 bound: `next_up(0.25f32) = 0.25 + 2^-25` (`0x3E80_0001`).
    let sharp_slew_limit = f32::from_bits(0x3E80_0001);
    assert_prop(!out.is_nan() && out >= -U_MAX && out <= U_MAX);
    assert_prop(!diff.is_nan() && diff <= sharp_slew_limit);
    assert_prop(inv_pid_safe() == 1);
    1
}

// ============================================================================
// Part 2: Quadrotor X-Frame 4-Motor Mixer (`f32x4` SIMD128 + Native Profile Pair)
// ============================================================================

#[inline(always)]
fn is_finite_f32(x: f32) -> bool {
    (x.to_bits() & 0x7FFF_FFFF) < 0x7F80_0000
}

/// Scalar branchy reference PX4 X-frame 4-motor mixer:
/// Converts `(thrust, roll, pitch, yaw, estop)` into 4× 12-bit PWM values `[0..=4095]` packed
/// into `u64` (`m0 | (m1 << 16) | (m2 << 32) | (m3 << 48)`).
/// Returns `0` (all motors idle) if `estop != 0` or any control axis is `NaN`/`±Inf`.
#[unsafe(no_mangle)]
pub extern "C" fn quad_mixer_4_scalar(
    thrust: f32,
    roll: f32,
    pitch: f32,
    yaw: f32,
    estop: i32,
) -> u64 {
    if estop != 0 {
        return 0;
    }
    if !is_finite_f32(thrust) {
        return 0;
    }
    if !is_finite_f32(roll) {
        return 0;
    }
    if !is_finite_f32(pitch) {
        return 0;
    }
    if !is_finite_f32(yaw) {
        return 0;
    }

    let raw = [
        (thrust + roll) + (pitch - yaw),
        (thrust - roll) + (pitch + yaw),
        (thrust - roll) + ((-pitch) - yaw),
        (thrust + roll) + ((-pitch) + yaw),
    ];

    let mut packed = 0u64;
    let mut i = 0usize;
    while i < 4 {
        let x = raw[i];
        let c0 = if x > 0.0 { x } else { 0.0 };
        let c1 = if c0 < 1.0 { c0 } else { 1.0 };
        // Portable `#![no_std]` IEEE-754 round-to-nearest-even (ties-to-even) over `[0.0, 4095.0]`.
        let scaled = c1 * 4095.0;
        let base_i = scaled as u32;
        let frac = scaled - (base_i as f32);
        let pwm = if frac > 0.5 || (frac == 0.5 && (base_i & 1) != 0) {
            base_i + 1
        } else {
            base_i
        };
        packed |= (pwm as u64) << (i * 16);
        i += 1;
    }
    packed
}

/// Portable branchless vectorized 4-motor mixer using the IEEE-754 `2^23` magic-bias
/// round-to-nearest-even conversion (`(c1 * 4095.0 + 8_388_608.0).to_bits() & 0xFFFF`):
/// - Zero conditional branches AND zero `fptosi.sat` scalarization on x64 & ARM64
/// - Proved bit-for-bit identical to `quad_mixer_4_scalar` across ALL `2^160` IEEE-754 inputs
///   in Gnomon `QF_ABVFP`!
/// - Profiled directly via `gnomon profile --compare --targets x64,arm64 --bench`.
#[unsafe(no_mangle)]
pub extern "C" fn quad_mixer_4_opt(
    thrust: f32,
    roll: f32,
    pitch: f32,
    yaw: f32,
    estop: i32,
) -> u64 {
    let finite_mask = is_finite_f32(thrust) as u32
        & is_finite_f32(roll) as u32
        & is_finite_f32(pitch) as u32
        & is_finite_f32(yaw) as u32
        & (estop == 0) as u32;
    let out_mask = 0u64.wrapping_sub(finite_mask as u64);

    let tr_p = thrust + roll;
    let tr_m = thrust - roll;
    let py_m = pitch - yaw;
    let py_p = pitch + yaw;
    let npy_m = (-pitch) - yaw;
    let npy_p = (-pitch) + yaw;

    let a = [tr_p, tr_m, tr_m, tr_p];
    let b = [py_m, py_p, npy_m, npy_p];

    // IEEE-754 `2^23 = 8_388_608.0` (`0x4B00_0000`) magic bias: for any `y in [0.0, 4095.0]`,
    // `(y + 2^23).to_bits() & 0xFFFF` yields exact hardware round-to-nearest-even in `0..=4095`!
    const MAGIC_RNE_BIAS: f32 = 8_388_608.0;
    let mut pwm = [0u32; 4];
    let mut i = 0usize;
    while i < 4 {
        let m = a[i] + b[i];
        let c0 = if m > 0.0 { m } else { 0.0 };
        let c1 = if c0 < 1.0 { c0 } else { 1.0 };
        pwm[i] = (c1 * 4095.0 + MAGIC_RNE_BIAS).to_bits() & 0xFFFF;
        i += 1;
    }

    let lo = pwm[0] | (pwm[1] << 16);
    let hi = pwm[2] | (pwm[3] << 16);
    let packed = (lo as u64) | ((hi as u64) << 32);
    packed & out_mask
}

/// Explicit Wasm `f32x4` SIMD128 quadrotor 4-motor mixer using `f32x4_add`, `f32x4_gt`/`f32x4_lt`
/// + `v128_bitselect` NaN-safe clamp, `f32x4_mul`, `f32x4_nearest`, and `u32x4_trunc_sat_f32x4`.
/// Proved bit-for-bit identical to `quad_mixer_4_opt` (and `quad_mixer_4_scalar`) in `QF_ABVFP`!
#[cfg(target_arch = "wasm32")]
#[unsafe(no_mangle)]
pub extern "C" fn quad_mixer_4_v128(
    thrust: f32,
    roll: f32,
    pitch: f32,
    yaw: f32,
    estop: i32,
) -> u64 {
    let finite_ok =
        is_finite_f32(thrust) & is_finite_f32(roll) & is_finite_f32(pitch) & is_finite_f32(yaw);
    if estop != 0 || !finite_ok {
        return 0;
    }

    let tr_p = thrust + roll;
    let tr_m = thrust - roll;
    let av = f32x4(tr_p, tr_m, tr_m, tr_p);
    let bv = f32x4(pitch - yaw, pitch + yaw, (-pitch) - yaw, (-pitch) + yaw);

    let raw = f32x4_add(av, bv);
    let zero = f32x4_splat(0.0);
    let one = f32x4_splat(1.0);
    let c0 = v128_bitselect(raw, zero, f32x4_gt(raw, zero));
    let c1 = v128_bitselect(c0, one, f32x4_lt(c0, one));
    let scaled = f32x4_mul(c1, f32x4_splat(4095.0));
    let rounded = f32x4_nearest(scaled);
    let pwms = u32x4_trunc_sat_f32x4(rounded);

    let m0 = u32x4_extract_lane::<0>(pwms) as u64;
    let m1 = u32x4_extract_lane::<1>(pwms) as u64;
    let m2 = u32x4_extract_lane::<2>(pwms) as u64;
    let m3 = u32x4_extract_lane::<3>(pwms) as u64;
    m0 | (m1 << 16) | (m2 << 32) | (m3 << 48)
}

/// Postcondition proving quadrotor 4-motor mixer safety across ALL `2^160` inputs:
/// - All 4 packed 16-bit PWM commands lie strictly in `0..=4095`
/// - `estop != 0` => all 4 motors strictly `0` (`ret == 0`)
/// - Any `NaN` or `±Inf` axis input => all 4 motors strictly `0` (NEVER full throttle!).
#[cfg(target_arch = "wasm32")]
#[unsafe(no_mangle)]
pub extern "C" fn ens_quad_mixer_safe(
    thrust: f32,
    roll: f32,
    pitch: f32,
    yaw: f32,
    estop: i32,
    ret: u64,
) -> i32 {
    let m0 = (ret & 0xFFFF) as u32;
    let m1 = ((ret >> 16) & 0xFFFF) as u32;
    let m2 = ((ret >> 32) & 0xFFFF) as u32;
    let m3 = ((ret >> 48) & 0xFFFF) as u32;

    if m0 > 4095 || m1 > 4095 || m2 > 4095 || m3 > 4095 {
        return 0;
    }
    let axes = f32x4(thrust, roll, pitch, yaw);
    let all_finite = i32x4_bitmask(f32x4_le(f32x4_abs(axes), f32x4_splat(f32::MAX))) == 0xF;
    if (estop != 0 || !all_finite) && ret != 0 {
        return 0;
    }
    1
}
