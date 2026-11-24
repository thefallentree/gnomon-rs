#![no_std]

//! Vertical Pack 1 Buggy Mutants — AI Inference (`Q8_0` Block Quantization)
//!
//! 1. `q8_0_buggy_zero_nan`: forgets the `amax == 0.0` guard and computes `127.0 / amax` directly,
//!    producing `0.0 * +Inf = NaN` on an all-zero block (which corrupts clamping to `-127` and
//!    violates both `ens_q8_0_safe` and `q8_0_quant_4_ref` equivalence!).
//! 2. `q8_0_buggy_trunc_bias`: omits `f32x4_nearest` and truncates toward zero directly,
//!    introducing systematic quantization bias (`FALSIFIED` against `q8_0_quant_4_ref`!).

use core::arch::wasm32::*;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

#[inline(always)]
fn pack_i32_pair(lo: i32, hi: i32) -> i64 {
    ((((hi as u32) as u64) << 32) | ((lo as u32) as u64)) as i64
}

#[inline(always)]
fn pack_4_i8(q0: i32, q1: i32, q2: i32, q3: i32) -> i32 {
    (q0 & 0xFF) | ((q1 & 0xFF) << 8) | ((q2 & 0xFF) << 16) | ((q3 & 0xFF) << 24)
}

#[inline(always)]
fn buggy_float_clamp_i8(v: f32) -> i32 {
    // Classic C/Rust buggy float clamp: NaN fails `>= -127.0` and silently falls into `-127`!
    if v >= -127.0 {
        if v <= 127.0 {
            v as i32
        } else {
            127
        }
    } else {
        -127
    }
}

/// Buggy Mutant 1: omits the `amax == 0.0` guard -> `inv_scale = 127.0 / 0.0 = +Inf`,
/// so `x_i * inv_scale = 0.0 * +Inf = NaN` on an all-zero block!
#[unsafe(no_mangle)]
pub extern "C" fn q8_0_buggy_zero_nan(x0: f32, x1: f32, x2: f32, x3: f32) -> i64 {
    let xv = f32x4(x0, x1, x2, x3);
    let av = f32x4_abs(xv);

    let even = f32x4(
        f32x4_extract_lane::<0>(av),
        f32x4_extract_lane::<2>(av),
        0.0,
        0.0,
    );
    let odd = f32x4(
        f32x4_extract_lane::<1>(av),
        f32x4_extract_lane::<3>(av),
        0.0,
        0.0,
    );
    let pair_max = f32x4_max(even, odd);
    let m01 = f32x4_extract_lane::<0>(pair_max);
    let m23 = f32x4_extract_lane::<1>(pair_max);
    let amax = f32x4_extract_lane::<0>(f32x4_max(f32x4_splat(m01), f32x4_splat(m23)));

    // BUG: no guard when `amax == 0.0` -> `127.0 / 0.0 = +Inf` -> `0.0 * +Inf = NaN`!
    let scale = amax / 127.0;
    let inv_scale = 127.0 / amax;

    let scaled = f32x4_mul(xv, f32x4_splat(inv_scale));
    let rounded = f32x4_nearest(scaled);

    let q0 = buggy_float_clamp_i8(f32x4_extract_lane::<0>(rounded));
    let q1 = buggy_float_clamp_i8(f32x4_extract_lane::<1>(rounded));
    let q2 = buggy_float_clamp_i8(f32x4_extract_lane::<2>(rounded));
    let q3 = buggy_float_clamp_i8(f32x4_extract_lane::<3>(rounded));

    let packed_q = pack_4_i8(q0, q1, q2, q3);
    pack_i32_pair(scale.to_bits() as i32, packed_q)
}

/// Buggy Mutant 2: uses truncation toward zero (`i32x4_trunc_sat_f32x4(scaled)`)
/// instead of round-to-nearest-even (`f32x4_nearest`), causing systematic quantization bias!
#[unsafe(no_mangle)]
pub extern "C" fn q8_0_buggy_trunc_bias(x0: f32, x1: f32, x2: f32, x3: f32) -> i64 {
    let xv = f32x4(x0, x1, x2, x3);
    let av = f32x4_abs(xv);

    let even = f32x4(
        f32x4_extract_lane::<0>(av),
        f32x4_extract_lane::<2>(av),
        0.0,
        0.0,
    );
    let odd = f32x4(
        f32x4_extract_lane::<1>(av),
        f32x4_extract_lane::<3>(av),
        0.0,
        0.0,
    );
    let pair_max = f32x4_max(even, odd);
    let m01 = f32x4_extract_lane::<0>(pair_max);
    let m23 = f32x4_extract_lane::<1>(pair_max);
    let amax = f32x4_extract_lane::<0>(f32x4_max(f32x4_splat(m01), f32x4_splat(m23)));

    if !(amax > 0.0) {
        return 0;
    }
    let scale = amax / 127.0;
    let inv_scale = 127.0 / amax;
    if !(scale < f32::INFINITY) || !(inv_scale < f32::INFINITY) {
        return 0;
    }

    let scaled = f32x4_mul(xv, f32x4_splat(inv_scale));
    // BUG: omits `f32x4_nearest` and truncates toward zero directly!
    let trunc = i32x4_trunc_sat_f32x4(scaled);
    let clamped = i32x4_max(i32x4_min(trunc, i32x4_splat(127)), i32x4_splat(-127));

    let q0 = i32x4_extract_lane::<0>(clamped);
    let q1 = i32x4_extract_lane::<1>(clamped);
    let q2 = i32x4_extract_lane::<2>(clamped);
    let q3 = i32x4_extract_lane::<3>(clamped);

    let packed_q = pack_4_i8(q0, q1, q2, q3);
    pack_i32_pair(scale.to_bits() as i32, packed_q)
}

#[unsafe(no_mangle)]
pub extern "C" fn req_finite_block(x0: f32, x1: f32, x2: f32, x3: f32) -> i32 {
    let xv = f32x4(x0, x1, x2, x3);
    let lim = f32x4_splat(f32::MAX);
    let ok = f32x4_le(f32x4_abs(xv), lim);
    if i32x4_bitmask(ok) == 0xF { 1 } else { 0 }
}

#[unsafe(no_mangle)]
pub extern "C" fn ens_q8_0_safe(x0: f32, x1: f32, x2: f32, x3: f32, ret: i64) -> i32 {
    let scale = f32::from_bits(ret as u32);
    let packed_q = (ret >> 32) as u32;

    if scale.is_nan() || !(scale >= 0.0) || !(scale < f32::INFINITY) || scale.to_bits() == 0x8000_0000
    {
        return 0;
    }

    let q0 = (packed_q & 0xFF) as u8 as i8;
    let q1 = ((packed_q >> 8) & 0xFF) as u8 as i8;
    let q2 = ((packed_q >> 16) & 0xFF) as u8 as i8;
    let q3 = ((packed_q >> 24) & 0xFF) as u8 as i8;

    if q0 < -127 || q1 < -127 || q2 < -127 || q3 < -127 {
        return 0;
    }

    if x0 == 0.0 && x1 == 0.0 && x2 == 0.0 && x3 == 0.0 && ret != 0 {
        return 0;
    }

    1
}
