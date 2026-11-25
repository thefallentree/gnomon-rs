#![no_std]

//! Vertical Pack 6 Buggy Mutants — Safety-Critical Robotics / Aerospace Control
//!
//! 1. `step_pid_buggy_nan_clamp`: classic flight-controller brick bug! Uses the naive IEEE-754
//!    clamp `if v > hi { hi } else if v < lo { lo } else { v }` without guarding `NaN` sensor
//!    inputs. Both `NaN > hi` and `NaN < lo` are `false`, so `NaN` flows straight into
//!    `INTEGRATOR_BITS`, permanently poisoning the controller and violating `inv_pid_safe`!
//! 2. `quad_mixer_buggy_nan_full_throttle`: classic drone full-throttle crash bug! Omits finite
//!    input checks and clamps with `if m < 0.0 { 0.0 } else if m <= 1.0 { m } else { 1.0 }`.
//!    On a `NaN` IMU glitch, BOTH `< 0.0` and `<= 1.0` are `false`, sending `1.0` (4095 = 100%
//!    FULL THROTTLE) to all 4 motors — caught immediately by `ens_quad_mixer_safe`!

use core::arch::wasm32::*;
use core::sync::atomic::{AtomicU32, Ordering};

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

#[link(wasm_import_module = "gnomon")]
unsafe extern "C" {
    fn gnomon_assume(cond: i32);
    fn gnomon_assert(cond: i32);
}

#[inline(always)]
fn assume(cond: bool) {
    unsafe {
        gnomon_assume(if cond { 1 } else { 0 });
    }
}

#[inline(always)]
fn assert_prop(cond: bool) {
    unsafe {
        gnomon_assert(if cond { 1 } else { 0 });
    }
}

const KP: f32 = 0.5;
const KI: f32 = 0.125;
const I_MAX: f32 = 10.0;
const U_MAX: f32 = 1.0;
const MAX_SLEW: f32 = 0.25;
const SENSOR_LIM: f32 = 1000.0;
const DT_MAX: f32 = 0.5;

static INTEGRATOR_BITS: AtomicU32 = AtomicU32::new(0);
static PREV_OUT_BITS: AtomicU32 = AtomicU32::new(0);
static ESTOP_LATCH: AtomicU32 = AtomicU32::new(0);

/// BUGGY naive clamp: `NaN > hi` is false and `NaN < lo` is false, so `NaN` passes right through!
#[inline(always)]
fn buggy_clamp_passes_nan(v: f32, lo: f32, hi: f32) -> f32 {
    if v > hi {
        hi
    } else if v < lo {
        lo
    } else {
        v
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn init_pid() -> i32 {
    INTEGRATOR_BITS.store(0, Ordering::Relaxed);
    PREV_OUT_BITS.store(0, Ordering::Relaxed);
    ESTOP_LATCH.store(0, Ordering::Relaxed);
    1
}

#[unsafe(no_mangle)]
pub extern "C" fn inv_pid_safe() -> i32 {
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

/// Buggy Mutant 1: omits sensor NaN/Inf rejection and uses `buggy_clamp_passes_nan`,
/// allowing a single `NaN` IMU sample to permanently poison `INTEGRATOR_BITS = NaN`!
#[unsafe(no_mangle)]
pub extern "C" fn step_pid_buggy_nan_clamp(
    setpoint: f32,
    measured: f32,
    dt: f32,
    estop_in: i32,
) -> f32 {
    let latched = ESTOP_LATCH.load(Ordering::Relaxed);
    if estop_in != 0 || latched != 0 {
        ESTOP_LATCH.store(1, Ordering::Relaxed);
        INTEGRATOR_BITS.store(0, Ordering::Relaxed);
        PREV_OUT_BITS.store(0, Ordering::Relaxed);
        return 0.0;
    }

    let integ = f32::from_bits(INTEGRATOR_BITS.load(Ordering::Relaxed));
    let prev = f32::from_bits(PREV_OUT_BITS.load(Ordering::Relaxed));

    // BUG: no finite sensor check + `buggy_clamp_passes_nan` lets NaN poison INTEGRATOR!
    let err = setpoint - measured;
    let next_i = buggy_clamp_passes_nan(integ + (err * dt) * KI, -I_MAX, I_MAX);
    let raw_u = buggy_clamp_passes_nan(err * KP + next_i, -U_MAX, U_MAX);
    let delta = buggy_clamp_passes_nan(raw_u - prev, -MAX_SLEW, MAX_SLEW);
    let next_u = buggy_clamp_passes_nan(prev + delta, -U_MAX, U_MAX);

    INTEGRATOR_BITS.store(next_i.to_bits(), Ordering::Relaxed);
    PREV_OUT_BITS.store(next_u.to_bits(), Ordering::Relaxed);
    next_u
}

#[unsafe(no_mangle)]
pub extern "C" fn clear_estop() -> i32 {
    ESTOP_LATCH.store(0, Ordering::Relaxed);
    INTEGRATOR_BITS.store(0, Ordering::Relaxed);
    PREV_OUT_BITS.store(0, Ordering::Relaxed);
    1
}

/// Inline contract catching NaN integrator poisoning (`FALSIFIED`).
#[unsafe(no_mangle)]
pub extern "C" fn contract_nan_sensor_never_poisons(setpoint: f32, measured: f32, dt: f32) -> i32 {
    assume(inv_pid_safe() == 1);
    assume(ESTOP_LATCH.load(Ordering::Relaxed) == 0);
    let old_i_bits = INTEGRATOR_BITS.load(Ordering::Relaxed);
    let faulty = !(setpoint >= -SENSOR_LIM && setpoint <= SENSOR_LIM)
        || !(measured >= -SENSOR_LIM && measured <= SENSOR_LIM)
        || !(dt > 0.0 && dt <= DT_MAX);
    assume(faulty);

    let out = step_pid_buggy_nan_clamp(setpoint, measured, dt, 0);
    assert_prop(out.to_bits() == 0);
    assert_prop(INTEGRATOR_BITS.load(Ordering::Relaxed) == old_i_bits);
    assert_prop(inv_pid_safe() == 1);
    1
}

/// Buggy Mutant 2: omits finite axis check and clamps with `if m < 0.0 ... else if m <= 1.0 ... else 1.0`,
/// turning a `NaN` axis input into `1.0` -> `4095` (100% FULL THROTTLE) on all 4 motors!
#[unsafe(no_mangle)]
pub extern "C" fn quad_mixer_buggy_nan_full_throttle(
    thrust: f32,
    roll: f32,
    pitch: f32,
    yaw: f32,
    estop: i32,
) -> u64 {
    if estop != 0 {
        return 0;
    }
    let raw = [
        (thrust + roll) + (pitch + (-yaw)),
        (thrust + (-roll)) + (pitch + yaw),
        (thrust + (-roll)) + ((-pitch) + (-yaw)),
        (thrust + roll) + ((-pitch) + yaw),
    ];

    let mut packed = 0u64;
    let mut i = 0usize;
    while i < 4 {
        let m = raw[i];
        // BUG: when `m` is NaN, `m < 0.0` is false AND `m <= 1.0` is false -> returns `1.0` (4095 PWM)!
        let c = if m < 0.0 {
            0.0
        } else if m <= 1.0 {
            m
        } else {
            1.0
        };
        let pwm = (c * 4095.0) as u32;
        packed |= (pwm as u64) << (i * 16);
        i += 1;
    }
    packed
}

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
