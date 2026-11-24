//! Exact deterministic `#![no_std]` IEEE-754 `f32`/`f64` and `v128` SIMD semantics
//! following the WebAssembly 2.0 + Fixed-Width SIMD specification.
//!
//! All non-bitwise NaN-producing operations canonicalize NaN outputs to the WebAssembly
//! canonical quiet NaN (`0x7fc0_0000` for `f32`, `0x7ff8_0000_0000_0000` for `f64`),
//! while bitwise sign operations (`abs`, `neg`, `copysign`) and pseudo-min/max
//! (`pmin`, `pmax`) preserve exact payload bit patterns.

use crate::ir::TrapCode;

pub const F32_CANON_NAN: u32 = 0x7fc0_0000;
pub const F64_CANON_NAN: u64 = 0x7ff8_0000_0000_0000;

const F32_SIGN_MASK: u32 = 0x8000_0000;
const F32_MAG_MASK: u32 = 0x7fff_ffff;
const F32_EXP_INF: u32 = 0x7f80_0000;
const F32_FRAC_MASK: u32 = 0x007f_ffff;
const F32_ONE: u32 = 0x3f80_0000;

const F64_SIGN_MASK: u64 = 0x8000_0000_0000_0000;
const F64_MAG_MASK: u64 = 0x7fff_ffff_ffff_ffff;
const F64_EXP_INF: u64 = 0x7ff0_0000_0000_0000;
const F64_FRAC_MASK: u64 = 0x000f_ffff_ffff_ffff;
const F64_ONE: u64 = 0x3ff0_0000_0000_0000;

#[inline]
pub const fn f32_is_nan(bits: u32) -> bool {
    (bits & F32_MAG_MASK) > F32_EXP_INF
}

#[inline]
pub const fn f64_is_nan(bits: u64) -> bool {
    (bits & F64_MAG_MASK) > F64_EXP_INF
}

#[inline]
pub fn f32_canon(v: f32) -> u32 {
    let b = v.to_bits();
    if f32_is_nan(b) { F32_CANON_NAN } else { b }
}

#[inline]
pub fn f64_canon(v: f64) -> u64 {
    let b = v.to_bits();
    if f64_is_nan(b) { F64_CANON_NAN } else { b }
}

/// Total order key for non-NaN `f32` bit patterns with `-0.0 < +0.0`.
#[inline]
const fn f32_ord_key(bits: u32) -> i32 {
    if (bits as i32) < 0 { !((bits & F32_MAG_MASK) as i32) } else { bits as i32 }
}

/// Total order key for non-NaN `f64` bit patterns with `-0.0 < +0.0`.
#[inline]
const fn f64_ord_key(bits: u64) -> i64 {
    if (bits as i64) < 0 { !((bits & F64_MAG_MASK) as i64) } else { bits as i64 }
}

// ---------------------------------------------------------------------------
// Bitwise sign operations (preserve NaN payload verbatim)
// ---------------------------------------------------------------------------

#[inline]
pub const fn f32_abs(a: u32) -> u32 {
    a & F32_MAG_MASK
}

#[inline]
pub const fn f32_neg(a: u32) -> u32 {
    a ^ F32_SIGN_MASK
}

#[inline]
pub const fn f32_copysign(a: u32, b: u32) -> u32 {
    (a & F32_MAG_MASK) | (b & F32_SIGN_MASK)
}

#[inline]
pub const fn f64_abs(a: u64) -> u64 {
    a & F64_MAG_MASK
}

#[inline]
pub const fn f64_neg(a: u64) -> u64 {
    a ^ F64_SIGN_MASK
}

#[inline]
pub const fn f64_copysign(a: u64, b: u64) -> u64 {
    (a & F64_MAG_MASK) | (b & F64_SIGN_MASK)
}

// ---------------------------------------------------------------------------
// Arithmetic & Comparisons
// ---------------------------------------------------------------------------

#[inline]
pub fn f32_add(a: u32, b: u32) -> u32 {
    f32_canon(f32::from_bits(a) + f32::from_bits(b))
}

#[inline]
pub fn f32_sub(a: u32, b: u32) -> u32 {
    f32_canon(f32::from_bits(a) - f32::from_bits(b))
}

#[inline]
pub fn f32_mul(a: u32, b: u32) -> u32 {
    f32_canon(f32::from_bits(a) * f32::from_bits(b))
}

#[inline]
pub fn f32_div(a: u32, b: u32) -> u32 {
    f32_canon(f32::from_bits(a) / f32::from_bits(b))
}

#[inline]
pub fn f64_add(a: u64, b: u64) -> u64 {
    f64_canon(f64::from_bits(a) + f64::from_bits(b))
}

#[inline]
pub fn f64_sub(a: u64, b: u64) -> u64 {
    f64_canon(f64::from_bits(a) - f64::from_bits(b))
}

#[inline]
pub fn f64_mul(a: u64, b: u64) -> u64 {
    f64_canon(f64::from_bits(a) * f64::from_bits(b))
}

#[inline]
pub fn f64_div(a: u64, b: u64) -> u64 {
    f64_canon(f64::from_bits(a) / f64::from_bits(b))
}

#[inline]
pub const fn f32_min(a: u32, b: u32) -> u32 {
    if f32_is_nan(a) || f32_is_nan(b) {
        return F32_CANON_NAN;
    }
    if f32_ord_key(a) <= f32_ord_key(b) { a } else { b }
}

#[inline]
pub const fn f32_max(a: u32, b: u32) -> u32 {
    if f32_is_nan(a) || f32_is_nan(b) {
        return F32_CANON_NAN;
    }
    if f32_ord_key(a) >= f32_ord_key(b) { a } else { b }
}

#[inline]
pub const fn f64_min(a: u64, b: u64) -> u64 {
    if f64_is_nan(a) || f64_is_nan(b) {
        return F64_CANON_NAN;
    }
    if f64_ord_key(a) <= f64_ord_key(b) { a } else { b }
}

#[inline]
pub const fn f64_max(a: u64, b: u64) -> u64 {
    if f64_is_nan(a) || f64_is_nan(b) {
        return F64_CANON_NAN;
    }
    if f64_ord_key(a) >= f64_ord_key(b) { a } else { b }
}

#[inline]
pub const fn f32_eq(a: u32, b: u32) -> bool {
    if f32_is_nan(a) || f32_is_nan(b) {
        return false;
    }
    if ((a | b) & F32_MAG_MASK) == 0 {
        return true;
    }
    a == b
}

#[inline]
pub const fn f32_ne(a: u32, b: u32) -> bool {
    !f32_eq(a, b)
}

#[inline]
pub const fn f32_lt(a: u32, b: u32) -> bool {
    if f32_is_nan(a) || f32_is_nan(b) || ((a | b) & F32_MAG_MASK) == 0 {
        return false;
    }
    f32_ord_key(a) < f32_ord_key(b)
}

#[inline]
pub const fn f32_gt(a: u32, b: u32) -> bool {
    f32_lt(b, a)
}

#[inline]
pub const fn f32_le(a: u32, b: u32) -> bool {
    if f32_is_nan(a) || f32_is_nan(b) {
        return false;
    }
    if ((a | b) & F32_MAG_MASK) == 0 {
        return true;
    }
    f32_ord_key(a) <= f32_ord_key(b)
}

#[inline]
pub const fn f32_ge(a: u32, b: u32) -> bool {
    f32_le(b, a)
}

#[inline]
pub const fn f32_pmin(a: u32, b: u32) -> u32 {
    if f32_lt(b, a) { b } else { a }
}

#[inline]
pub const fn f32_pmax(a: u32, b: u32) -> u32 {
    if f32_lt(a, b) { b } else { a }
}

#[inline]
pub const fn f64_eq(a: u64, b: u64) -> bool {
    if f64_is_nan(a) || f64_is_nan(b) {
        return false;
    }
    if ((a | b) & F64_MAG_MASK) == 0 {
        return true;
    }
    a == b
}

#[inline]
pub const fn f64_ne(a: u64, b: u64) -> bool {
    !f64_eq(a, b)
}

#[inline]
pub const fn f64_lt(a: u64, b: u64) -> bool {
    if f64_is_nan(a) || f64_is_nan(b) || ((a | b) & F64_MAG_MASK) == 0 {
        return false;
    }
    f64_ord_key(a) < f64_ord_key(b)
}

#[inline]
pub const fn f64_gt(a: u64, b: u64) -> bool {
    f64_lt(b, a)
}

#[inline]
pub const fn f64_le(a: u64, b: u64) -> bool {
    if f64_is_nan(a) || f64_is_nan(b) {
        return false;
    }
    if ((a | b) & F64_MAG_MASK) == 0 {
        return true;
    }
    f64_ord_key(a) <= f64_ord_key(b)
}

#[inline]
pub const fn f64_ge(a: u64, b: u64) -> bool {
    f64_le(b, a)
}

#[inline]
pub const fn f64_pmin(a: u64, b: u64) -> u64 {
    if f64_lt(b, a) { b } else { a }
}

#[inline]
pub const fn f64_pmax(a: u64, b: u64) -> u64 {
    if f64_lt(a, b) { b } else { a }
}

// ---------------------------------------------------------------------------
// Rounding (`ceil`, `floor`, `trunc`, `nearest` / RNE) — exact `#![no_std]`
// ---------------------------------------------------------------------------

#[derive(Clone, Copy)]
enum RoundMode {
    Ceil,
    Floor,
    Trunc,
    Nearest,
}

const fn round_f32(bits: u32, mode: RoundMode) -> u32 {
    let sign = bits & F32_SIGN_MASK;
    let mag = bits & F32_MAG_MASK;
    if mag >= F32_EXP_INF {
        return if mag > F32_EXP_INF { F32_CANON_NAN } else { bits };
    }
    if mag == 0 {
        return bits;
    }
    let exp = ((mag >> 23) as i32) - 127;
    if exp >= 23 {
        return bits;
    }
    if exp < 0 {
        return match mode {
            RoundMode::Trunc => sign,
            RoundMode::Floor => if sign != 0 { F32_SIGN_MASK | F32_ONE } else { 0 },
            RoundMode::Ceil => if sign == 0 { F32_ONE } else { F32_SIGN_MASK },
            RoundMode::Nearest => {
                // |x| > 0.5 iff exp == -1 and frac != 0; ties at ±0.5 round to even (±0.0).
                if exp == -1 && (bits & F32_FRAC_MASK) != 0 { sign | F32_ONE } else { sign }
            }
        };
    }
    let frac_shift = (23 - exp) as u32;
    let ulp = 1u32 << frac_shift;
    let frac_mask = ulp - 1;
    let rem = bits & frac_mask;
    if rem == 0 {
        return bits;
    }
    let truncated = bits & !frac_mask;
    match mode {
        RoundMode::Trunc => truncated,
        RoundMode::Floor => if sign != 0 { truncated + ulp } else { truncated },
        RoundMode::Ceil => if sign == 0 { truncated + ulp } else { truncated },
        RoundMode::Nearest => {
            let half = 1u32 << (frac_shift - 1);
            if rem > half || (rem == half && (truncated & ulp) != 0) {
                truncated + ulp
            } else {
                truncated
            }
        }
    }
}

const fn round_f64(bits: u64, mode: RoundMode) -> u64 {
    let sign = bits & F64_SIGN_MASK;
    let mag = bits & F64_MAG_MASK;
    if mag >= F64_EXP_INF {
        return if mag > F64_EXP_INF { F64_CANON_NAN } else { bits };
    }
    if mag == 0 {
        return bits;
    }
    let exp = ((mag >> 52) as i32) - 1023;
    if exp >= 52 {
        return bits;
    }
    if exp < 0 {
        return match mode {
            RoundMode::Trunc => sign,
            RoundMode::Floor => if sign != 0 { F64_SIGN_MASK | F64_ONE } else { 0 },
            RoundMode::Ceil => if sign == 0 { F64_ONE } else { F64_SIGN_MASK },
            RoundMode::Nearest => {
                if exp == -1 && (bits & F64_FRAC_MASK) != 0 { sign | F64_ONE } else { sign }
            }
        };
    }
    let frac_shift = (52 - exp) as u32;
    let ulp = 1u64 << frac_shift;
    let frac_mask = ulp - 1;
    let rem = bits & frac_mask;
    if rem == 0 {
        return bits;
    }
    let truncated = bits & !frac_mask;
    match mode {
        RoundMode::Trunc => truncated,
        RoundMode::Floor => if sign != 0 { truncated + ulp } else { truncated },
        RoundMode::Ceil => if sign == 0 { truncated + ulp } else { truncated },
        RoundMode::Nearest => {
            let half = 1u64 << (frac_shift - 1);
            if rem > half || (rem == half && (truncated & ulp) != 0) {
                truncated + ulp
            } else {
                truncated
            }
        }
    }
}

pub const fn f32_ceil(a: u32) -> u32 {
    round_f32(a, RoundMode::Ceil)
}
pub const fn f32_floor(a: u32) -> u32 {
    round_f32(a, RoundMode::Floor)
}
pub const fn f32_trunc(a: u32) -> u32 {
    round_f32(a, RoundMode::Trunc)
}
pub const fn f32_nearest(a: u32) -> u32 {
    round_f32(a, RoundMode::Nearest)
}

pub const fn f64_ceil(a: u64) -> u64 {
    round_f64(a, RoundMode::Ceil)
}
pub const fn f64_floor(a: u64) -> u64 {
    round_f64(a, RoundMode::Floor)
}
pub const fn f64_trunc(a: u64) -> u64 {
    round_f64(a, RoundMode::Trunc)
}
pub const fn f64_nearest(a: u64) -> u64 {
    round_f64(a, RoundMode::Nearest)
}

// ---------------------------------------------------------------------------
// Exact IEEE-754 Square Root (round-to-nearest-even) — `#![no_std]`
// ---------------------------------------------------------------------------

pub const fn f32_sqrt(bits: u32) -> u32 {
    let mag = bits & F32_MAG_MASK;
    if mag > F32_EXP_INF {
        return F32_CANON_NAN;
    }
    if mag == 0 {
        return bits; // sqrt(+0.0) = +0.0, sqrt(-0.0) = -0.0
    }
    if (bits & F32_SIGN_MASK) != 0 {
        return F32_CANON_NAN;
    }
    if mag == F32_EXP_INF {
        return bits; // sqrt(+Inf) = +Inf
    }
    let exp_raw = mag >> 23;
    let frac = mag & F32_FRAC_MASK;
    let (mut m, mut e) = if exp_raw == 0 {
        let shift = frac.leading_zeros() - 8;
        (frac << shift, -126 - (shift as i32))
    } else {
        ((1u32 << 23) | frac, (exp_raw as i32) - 127)
    };
    if (e & 1) != 0 {
        m <<= 1;
        e -= 1;
    }
    let e_out = e >> 1;
    let radicand = (m as u64) << 25;
    let q = radicand.isqrt() as u32;
    // Since radicand is even, q^2 < radicand whenever q is odd (sticky bit is 1),
    // and radicand < (q+1)^2 whenever q is even (strictly below midpoint).
    let sig = (q >> 1) + (q & 1);
    (((e_out + 127) as u32) << 23) | (sig & F32_FRAC_MASK)
}

pub const fn f64_sqrt(bits: u64) -> u64 {
    let mag = bits & F64_MAG_MASK;
    if mag > F64_EXP_INF {
        return F64_CANON_NAN;
    }
    if mag == 0 {
        return bits;
    }
    if (bits & F64_SIGN_MASK) != 0 {
        return F64_CANON_NAN;
    }
    if mag == F64_EXP_INF {
        return bits;
    }
    let exp_raw = mag >> 52;
    let frac = mag & F64_FRAC_MASK;
    let (mut m, mut e) = if exp_raw == 0 {
        let shift = frac.leading_zeros() - 11;
        (frac << shift, -1022 - (shift as i32))
    } else {
        ((1u64 << 52) | frac, (exp_raw as i32) - 1023)
    };
    if (e & 1) != 0 {
        m <<= 1;
        e -= 1;
    }
    let e_out = e >> 1;
    let radicand = (m as u128) << 54;
    let q = radicand.isqrt() as u64;
    let sig = (q >> 1) + (q & 1);
    (((e_out + 1023) as u64) << 52) | (sig & F64_FRAC_MASK)
}

// ---------------------------------------------------------------------------
// Float <-> Int Conversions (Trapping & Saturating) and Promote / Demote
// ---------------------------------------------------------------------------

pub const fn i32_trunc_f32_s(bits: u32) -> Result<i32, TrapCode> {
    let sign = (bits & F32_SIGN_MASK) != 0;
    let exp = (((bits & F32_MAG_MASK) >> 23) as i32) - 127;
    let frac = bits & F32_FRAC_MASK;
    if exp == 128 {
        return Err(TrapCode::IntOverflow);
    }
    if exp < 0 {
        return Ok(0);
    }
    if exp >= 31 {
        if sign && exp == 31 && frac == 0 {
            return Ok(i32::MIN);
        }
        return Err(TrapCode::IntOverflow);
    }
    let sig = (1u32 << 23) | frac;
    let mag = if exp >= 23 { sig << (exp - 23) } else { sig >> (23 - exp) };
    Ok(if sign { (mag as i32).wrapping_neg() } else { mag as i32 })
}

pub const fn i32_trunc_f32_u(bits: u32) -> Result<i32, TrapCode> {
    let sign = (bits & F32_SIGN_MASK) != 0;
    let exp = (((bits & F32_MAG_MASK) >> 23) as i32) - 127;
    let frac = bits & F32_FRAC_MASK;
    if exp == 128 {
        return Err(TrapCode::IntOverflow);
    }
    if exp < 0 {
        return Ok(0); // (-1.0, 1.0) truncates to 0
    }
    if sign || exp >= 32 {
        return Err(TrapCode::IntOverflow);
    }
    let sig = (1u32 << 23) | frac;
    let mag = if exp >= 23 { sig << (exp - 23) } else { sig >> (23 - exp) };
    Ok(mag as i32)
}

pub const fn i32_trunc_f64_s(bits: u64) -> Result<i32, TrapCode> {
    let sign = (bits & F64_SIGN_MASK) != 0;
    let exp = (((bits & F64_MAG_MASK) >> 52) as i32) - 1023;
    let frac = bits & F64_FRAC_MASK;
    if exp == 1024 {
        return Err(TrapCode::IntOverflow);
    }
    if exp < 0 {
        return Ok(0);
    }
    if exp >= 31 {
        // (-2147483649.0, -2147483648.0] has exp == 31 and integer part == 2^31.
        if sign && exp == 31 && (frac >> 21) == 0 {
            return Ok(i32::MIN);
        }
        return Err(TrapCode::IntOverflow);
    }
    let sig = (1u64 << 52) | frac;
    let mag = (sig >> (52 - exp)) as u32;
    Ok(if sign { (mag as i32).wrapping_neg() } else { mag as i32 })
}

pub const fn i32_trunc_f64_u(bits: u64) -> Result<i32, TrapCode> {
    let sign = (bits & F64_SIGN_MASK) != 0;
    let exp = (((bits & F64_MAG_MASK) >> 52) as i32) - 1023;
    let frac = bits & F64_FRAC_MASK;
    if exp == 1024 {
        return Err(TrapCode::IntOverflow);
    }
    if exp < 0 {
        return Ok(0);
    }
    if sign || exp >= 32 {
        return Err(TrapCode::IntOverflow);
    }
    let sig = (1u64 << 52) | frac;
    let mag = (sig >> (52 - exp)) as u32;
    Ok(mag as i32)
}

pub const fn i64_trunc_f32_s(bits: u32) -> Result<i64, TrapCode> {
    let sign = (bits & F32_SIGN_MASK) != 0;
    let exp = (((bits & F32_MAG_MASK) >> 23) as i32) - 127;
    let frac = bits & F32_FRAC_MASK;
    if exp == 128 {
        return Err(TrapCode::IntOverflow);
    }
    if exp < 0 {
        return Ok(0);
    }
    if exp >= 63 {
        if sign && exp == 63 && frac == 0 {
            return Ok(i64::MIN);
        }
        return Err(TrapCode::IntOverflow);
    }
    let sig = ((1u32 << 23) | frac) as u64;
    let mag = if exp >= 23 { sig << (exp - 23) } else { sig >> (23 - exp) };
    Ok(if sign { (mag as i64).wrapping_neg() } else { mag as i64 })
}

pub const fn i64_trunc_f32_u(bits: u32) -> Result<i64, TrapCode> {
    let sign = (bits & F32_SIGN_MASK) != 0;
    let exp = (((bits & F32_MAG_MASK) >> 23) as i32) - 127;
    let frac = bits & F32_FRAC_MASK;
    if exp == 128 {
        return Err(TrapCode::IntOverflow);
    }
    if exp < 0 {
        return Ok(0);
    }
    if sign || exp >= 64 {
        return Err(TrapCode::IntOverflow);
    }
    let sig = ((1u32 << 23) | frac) as u64;
    let mag = if exp >= 23 { sig << (exp - 23) } else { sig >> (23 - exp) };
    Ok(mag as i64)
}

pub const fn i64_trunc_f64_s(bits: u64) -> Result<i64, TrapCode> {
    let sign = (bits & F64_SIGN_MASK) != 0;
    let exp = (((bits & F64_MAG_MASK) >> 52) as i32) - 1023;
    let frac = bits & F64_FRAC_MASK;
    if exp == 1024 {
        return Err(TrapCode::IntOverflow);
    }
    if exp < 0 {
        return Ok(0);
    }
    if exp >= 63 {
        if sign && exp == 63 && frac == 0 {
            return Ok(i64::MIN);
        }
        return Err(TrapCode::IntOverflow);
    }
    let sig = (1u64 << 52) | frac;
    let mag = if exp >= 52 { sig << (exp - 52) } else { sig >> (52 - exp) };
    Ok(if sign { (mag as i64).wrapping_neg() } else { mag as i64 })
}

pub const fn i64_trunc_f64_u(bits: u64) -> Result<i64, TrapCode> {
    let sign = (bits & F64_SIGN_MASK) != 0;
    let exp = (((bits & F64_MAG_MASK) >> 52) as i32) - 1023;
    let frac = bits & F64_FRAC_MASK;
    if exp == 1024 {
        return Err(TrapCode::IntOverflow);
    }
    if exp < 0 {
        return Ok(0);
    }
    if sign || exp >= 64 {
        return Err(TrapCode::IntOverflow);
    }
    let sig = (1u64 << 52) | frac;
    let mag = if exp >= 52 { sig << (exp - 52) } else { sig >> (52 - exp) };
    Ok(mag as i64)
}

pub const fn i32_trunc_sat_f32_s(bits: u32) -> i32 {
    if f32_is_nan(bits) {
        return 0;
    }
    match i32_trunc_f32_s(bits) {
        Ok(v) => v,
        Err(_) => if (bits & F32_SIGN_MASK) != 0 { i32::MIN } else { i32::MAX },
    }
}

pub const fn i32_trunc_sat_f32_u(bits: u32) -> i32 {
    if f32_is_nan(bits) {
        return 0;
    }
    match i32_trunc_f32_u(bits) {
        Ok(v) => v,
        Err(_) => if (bits & F32_SIGN_MASK) != 0 { 0 } else { u32::MAX as i32 },
    }
}

pub const fn i32_trunc_sat_f64_s(bits: u64) -> i32 {
    if f64_is_nan(bits) {
        return 0;
    }
    match i32_trunc_f64_s(bits) {
        Ok(v) => v,
        Err(_) => if (bits & F64_SIGN_MASK) != 0 { i32::MIN } else { i32::MAX },
    }
}

pub const fn i32_trunc_sat_f64_u(bits: u64) -> i32 {
    if f64_is_nan(bits) {
        return 0;
    }
    match i32_trunc_f64_u(bits) {
        Ok(v) => v,
        Err(_) => if (bits & F64_SIGN_MASK) != 0 { 0 } else { u32::MAX as i32 },
    }
}

pub const fn i64_trunc_sat_f32_s(bits: u32) -> i64 {
    if f32_is_nan(bits) {
        return 0;
    }
    match i64_trunc_f32_s(bits) {
        Ok(v) => v,
        Err(_) => if (bits & F32_SIGN_MASK) != 0 { i64::MIN } else { i64::MAX },
    }
}

pub const fn i64_trunc_sat_f32_u(bits: u32) -> i64 {
    if f32_is_nan(bits) {
        return 0;
    }
    match i64_trunc_f32_u(bits) {
        Ok(v) => v,
        Err(_) => if (bits & F32_SIGN_MASK) != 0 { 0 } else { u64::MAX as i64 },
    }
}

pub const fn i64_trunc_sat_f64_s(bits: u64) -> i64 {
    if f64_is_nan(bits) {
        return 0;
    }
    match i64_trunc_f64_s(bits) {
        Ok(v) => v,
        Err(_) => if (bits & F64_SIGN_MASK) != 0 { i64::MIN } else { i64::MAX },
    }
}

pub const fn i64_trunc_sat_f64_u(bits: u64) -> i64 {
    if f64_is_nan(bits) {
        return 0;
    }
    match i64_trunc_f64_u(bits) {
        Ok(v) => v,
        Err(_) => if (bits & F64_SIGN_MASK) != 0 { 0 } else { u64::MAX as i64 },
    }
}

#[inline]
pub fn f32_demote_f64(bits: u64) -> u32 {
    if f64_is_nan(bits) { F32_CANON_NAN } else { f32_canon(f64::from_bits(bits) as f32) }
}

#[inline]
pub fn f64_promote_f32(bits: u32) -> u64 {
    if f32_is_nan(bits) { F64_CANON_NAN } else { f64_canon(f32::from_bits(bits) as f64) }
}

// ---------------------------------------------------------------------------
// Portable `v128` Lane Helpers
// ---------------------------------------------------------------------------

#[inline]
pub const fn splat_u8(x: u8) -> u128 {
    u128::from_le_bytes([x; 16])
}

#[inline]
pub const fn splat_u16(x: u16) -> u128 {
    let b = x.to_le_bytes();
    u128::from_le_bytes([
        b[0], b[1], b[0], b[1], b[0], b[1], b[0], b[1],
        b[0], b[1], b[0], b[1], b[0], b[1], b[0], b[1],
    ])
}

#[inline]
pub const fn splat_u32(x: u32) -> u128 {
    let lo = (x as u64) | ((x as u64) << 32);
    (lo as u128) | ((lo as u128) << 64)
}

#[inline]
pub const fn splat_u64(x: u64) -> u128 {
    (x as u128) | ((x as u128) << 64)
}

#[inline]
pub const fn unpack_u32x4(v: u128) -> [u32; 4] {
    [v as u32, (v >> 32) as u32, (v >> 64) as u32, (v >> 96) as u32]
}

#[inline]
pub const fn pack_u32x4(lanes: [u32; 4]) -> u128 {
    (lanes[0] as u128)
        | ((lanes[1] as u128) << 32)
        | ((lanes[2] as u128) << 64)
        | ((lanes[3] as u128) << 96)
}

#[inline]
pub const fn unpack_u64x2(v: u128) -> [u64; 2] {
    [v as u64, (v >> 64) as u64]
}

#[inline]
pub const fn pack_u64x2(lanes: [u64; 2]) -> u128 {
    (lanes[0] as u128) | ((lanes[1] as u128) << 64)
}

#[inline]
pub fn map_u32x4(v: u128, mut f: impl FnMut(u32) -> u32) -> u128 {
    let a = unpack_u32x4(v);
    pack_u32x4([f(a[0]), f(a[1]), f(a[2]), f(a[3])])
}

#[inline]
pub fn zip_u32x4(lhs: u128, rhs: u128, mut f: impl FnMut(u32, u32) -> u32) -> u128 {
    let a = unpack_u32x4(lhs);
    let b = unpack_u32x4(rhs);
    pack_u32x4([f(a[0], b[0]), f(a[1], b[1]), f(a[2], b[2]), f(a[3], b[3])])
}

#[inline]
pub fn map_u64x2(v: u128, mut f: impl FnMut(u64) -> u64) -> u128 {
    let a = unpack_u64x2(v);
    pack_u64x2([f(a[0]), f(a[1])])
}

#[inline]
pub fn zip_u64x2(lhs: u128, rhs: u128, mut f: impl FnMut(u64, u64) -> u64) -> u128 {
    let a = unpack_u64x2(lhs);
    let b = unpack_u64x2(rhs);
    pack_u64x2([f(a[0], b[0]), f(a[1], b[1])])
}

#[inline]
pub const fn i8x16_bitmask(v: u128) -> i32 {
    let b = v.to_le_bytes();
    let mut mask = 0u32;
    let mut i = 0;
    while i < 16 {
        mask |= (((b[i] >> 7) & 1) as u32) << i;
        i += 1;
    }
    mask as i32
}

#[inline]
pub const fn i16x8_bitmask(v: u128) -> i32 {
    let mut mask = 0u32;
    let mut i = 0;
    while i < 8 {
        mask |= (((v >> (i * 16 + 15)) & 1) as u32) << i;
        i += 1;
    }
    mask as i32
}

#[inline]
pub const fn i32x4_bitmask(v: u128) -> i32 {
    let mut mask = 0u32;
    let mut i = 0;
    while i < 4 {
        mask |= (((v >> (i * 32 + 31)) & 1) as u32) << i;
        i += 1;
    }
    mask as i32
}

#[inline]
pub const fn i64x2_bitmask(v: u128) -> i32 {
    let b0 = ((v >> 63) & 1) as u32;
    let b1 = ((v >> 127) & 1) as u32;
    (b0 | (b1 << 1)) as i32
}

#[inline]
pub const fn i8x16_swizzle(a: u128, s: u128) -> u128 {
    let ab = a.to_le_bytes();
    let sb = s.to_le_bytes();
    let mut out = [0u8; 16];
    let mut i = 0;
    while i < 16 {
        let idx = sb[i];
        if idx < 16 {
            out[i] = ab[idx as usize];
        }
        i += 1;
    }
    u128::from_le_bytes(out)
}

#[inline]
pub const fn i8x16_shuffle(lhs: u128, rhs: u128, lanes: [u8; 16]) -> Result<u128, TrapCode> {
    let lb = lhs.to_le_bytes();
    let rb = rhs.to_le_bytes();
    let mut out = [0u8; 16];
    let mut i = 0;
    while i < 16 {
        let idx = lanes[i];
        if idx < 16 {
            out[i] = lb[idx as usize];
        } else if idx < 32 {
            out[i] = rb[(idx - 16) as usize];
        } else {
            return Err(TrapCode::Unreachable);
        }
        i += 1;
    }
    Ok(u128::from_le_bytes(out))
}
