#![no_std]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

/// Exact 64x64 -> (hi, lo) unsigned widening multiplication using 32-bit limbs.
/// Division-free, zero overflow, zero `i128` shadow-stack spills on `wasm32`.
#[inline(always)]
fn mul_u64_wide(a: u64, b: u64) -> (u64, u64) {
    let a_lo = a & 0xFFFF_FFFF;
    let a_hi = a >> 32;
    let b_lo = b & 0xFFFF_FFFF;
    let b_hi = b >> 32;

    let p0 = a_lo.wrapping_mul(b_lo);
    let p1 = a_lo.wrapping_mul(b_hi);
    let p2 = a_hi.wrapping_mul(b_lo);
    let p3 = a_hi.wrapping_mul(b_hi);

    let mid = (p0 >> 32)
        .wrapping_add(p1 & 0xFFFF_FFFF)
        .wrapping_add(p2 & 0xFFFF_FFFF);
    let hi = p3
        .wrapping_add(p1 >> 32)
        .wrapping_add(p2 >> 32)
        .wrapping_add(mid >> 32);
    let lo = (mid << 32) | (p0 & 0xFFFF_FFFF);
    (hi, lo)
}

/// Exact unsigned absolute difference `|a - b|` for `i64` without signed overflow.
#[inline(always)]
fn abs_diff_i64(a: i64, b: i64) -> u64 {
    if a >= b {
        (a as u64).wrapping_sub(b as u64)
    } else {
        (b as u64).wrapping_sub(a as u64)
    }
}

/// S1.1 Checked Notional (safe, overflow-free, guarded division):
/// Returns 1 iff `price > 0`, `qty > 0`, `max_notional > 0`, and exact
/// mathematical `price * qty <= max_notional` with zero 64-bit wraparound.
#[unsafe(no_mangle)]
pub extern "C" fn checked_notional(price: i64, qty: i64, max_notional: i64) -> i32 {
    if price <= 0 || qty <= 0 || max_notional <= 0 {
        return 0;
    }
    let u_price = price as u64;
    let u_qty = qty as u64;
    let u_max = max_notional as u64;
    let max_price = match u_max.checked_div(u_qty) {
        Some(q) => q,
        None => return 0,
    };
    if u_price > max_price {
        return 0;
    }
    let prod = price.wrapping_mul(qty);
    if prod > 0 && prod <= max_notional {
        1
    } else {
        0
    }
}

/// Precondition for `checked_notional`: configured risk cap is positive,
/// while incoming order `price` and `qty` remain completely unconstrained `i64`s.
#[unsafe(no_mangle)]
pub extern "C" fn req_notional(_price: i64, _qty: i64, max_notional: i64) -> i32 {
    if max_notional > 0 { 1 } else { 0 }
}

/// Relational postcondition for `checked_notional`:
/// - `ret` is boolean (`0` or `1`).
/// - Non-positive `price`, `qty`, or `max_notional` MUST be rejected (`ret == 0`).
/// - When positive:
///   - `ret == 1` iff `price <= max_notional / qty` AND `0 < price.wrapping_mul(qty) <= max_notional`.
///   - Whenever `ret == 1`, both `price <= max_notional` and `qty <= max_notional`
///     (ruling out 64-bit wraparound fat-finger bypasses and trivial always-reject stubs).
#[unsafe(no_mangle)]
pub extern "C" fn ens_notional(price: i64, qty: i64, max_notional: i64, ret: i32) -> i32 {
    if ret != 0 && ret != 1 {
        return 0;
    }
    if price <= 0 || qty <= 0 || max_notional <= 0 {
        return if ret == 0 { 1 } else { 0 };
    }
    let u_price = price as u64;
    let u_qty = qty as u64;
    let u_max = max_notional as u64;
    let max_price = match u_max.checked_div(u_qty) {
        Some(q) => q,
        None => return 0,
    };
    let prod = price.wrapping_mul(qty);
    let safe_within_cap = u_price <= max_price && prod > 0 && prod <= max_notional;
    if (ret == 1) != safe_within_cap {
        return 0;
    }
    if ret == 1 && (u_price > u_max || u_qty > u_max) {
        return 0;
    }
    1
}

/// Buggy mutant for `checked_notional`:
/// Naively checks `price.wrapping_mul(qty) <= max_notional`, reproducing the
/// classic 64-bit signed overflow wraparound fat-finger risk bypass.
#[unsafe(no_mangle)]
pub extern "C" fn checked_notional_buggy_overflow(
    price: i64,
    qty: i64,
    max_notional: i64,
) -> i32 {
    if price <= 0 || qty <= 0 || max_notional <= 0 {
        return 0;
    }
    if price.wrapping_mul(qty) <= max_notional {
        1
    } else {
        0
    }
}

/// S1.1 Price Collar Check (safe, overflow-free, division-free):
/// Returns 1 iff `price > 0`, `ref_price > 0`, `collar_bps >= 0`, and
/// exact mathematical `|price - ref_price| * 10_000 <= ref_price * collar_bps`.
/// Uses O(1) fast-path guards (`price == ref_price`, `collar_bps == 0`,
/// `collar_bps <= 10_000 && diff > ref_price`) followed by exact 64x64->128 widening mul.
#[unsafe(no_mangle)]
pub extern "C" fn price_collar_ok(price: i64, ref_price: i64, collar_bps: i64) -> i32 {
    if price <= 0 || ref_price <= 0 || collar_bps < 0 {
        return 0;
    }
    if price == ref_price {
        return 1;
    }
    if collar_bps == 0 {
        return 0;
    }
    let diff = abs_diff_i64(price, ref_price);
    if collar_bps <= 10_000 && diff > (ref_price as u64) {
        return 0;
    }
    let (lhs_hi, lhs_lo) = mul_u64_wide(diff, 10_000);
    let (rhs_hi, rhs_lo) = mul_u64_wide(ref_price as u64, collar_bps as u64);
    if lhs_hi < rhs_hi || (lhs_hi == rhs_hi && lhs_lo <= rhs_lo) {
        1
    } else {
        0
    }
}

/// Precondition for `price_collar_ok`: realistic basis-point collar `0 <= collar_bps <= 10_000`
/// (0% to 100%), leaving `price` and `ref_price` completely unconstrained `i64`s (including `0`
/// and negatives so `ref_price == 0` div0 bugs are caught!).
#[unsafe(no_mangle)]
pub extern "C" fn req_price_collar(_price: i64, _ref_price: i64, collar_bps: i64) -> i32 {
    if collar_bps >= 0 && collar_bps <= 10_000 {
        1
    } else {
        0
    }
}

/// Relational postcondition for `price_collar_ok`:
/// - `ret` is boolean (`0` or `1`).
/// - Rejects `price <= 0 || ref_price <= 0 || collar_bps < 0`.
/// - Guarantees `price == ref_price => ret == 1`, `collar_bps == 0 => (ret == 1) == (price == ref_price)`,
///   `collar_bps <= 10_000 && |price - ref_price| > ref_price => ret == 0`,
///   and exact 128-bit collar inequality `|price - ref_price| * 10_000 <= ref_price * collar_bps`.
#[unsafe(no_mangle)]
pub extern "C" fn ens_price_collar(
    price: i64,
    ref_price: i64,
    collar_bps: i64,
    ret: i32,
) -> i32 {
    if ret != 0 && ret != 1 {
        return 0;
    }
    if price <= 0 || ref_price <= 0 || collar_bps < 0 {
        return if ret == 0 { 1 } else { 0 };
    }
    let diff = abs_diff_i64(price, ref_price);
    if price == ref_price {
        return if ret == 1 { 1 } else { 0 };
    }
    if collar_bps == 0 {
        return if ret == 0 { 1 } else { 0 };
    }
    if collar_bps <= 10_000 && diff > (ref_price as u64) {
        return if ret == 0 { 1 } else { 0 };
    }
    let (lhs_hi, lhs_lo) = mul_u64_wide(diff, 10_000);
    let (rhs_hi, rhs_lo) = mul_u64_wide(ref_price as u64, collar_bps as u64);
    let should_pass = lhs_hi < rhs_hi || (lhs_hi == rhs_hi && lhs_lo <= rhs_lo);
    if (ret == 1) == should_pass { 1 } else { 0 }
}

/// Buggy mutant 1 for `price_collar_ok`:
/// Divides by `ref_price` without guarding `ref_price == 0` -> traps with DivByZero!
#[unsafe(no_mangle)]
pub extern "C" fn price_collar_buggy_div0(price: i64, ref_price: i64, collar_bps: i64) -> i32 {
    if collar_bps < 0 {
        return 0;
    }
    let diff = abs_diff_i64(price, ref_price) as i64;
    let bps_deviation = diff.wrapping_mul(10_000) / ref_price;
    if bps_deviation <= collar_bps { 1 } else { 0 }
}

/// Buggy mutant 2 for `price_collar_ok`:
/// Guards `price > 0`, `ref_price > 0`, `collar_bps >= 0`, but naively multiplies in
/// 64-bit signed arithmetic so large `price` wraps `diff * 10_000` negative and
/// silently bypasses the price collar!
#[unsafe(no_mangle)]
pub extern "C" fn price_collar_buggy_overflow(
    price: i64,
    ref_price: i64,
    collar_bps: i64,
) -> i32 {
    if price <= 0 || ref_price <= 0 || collar_bps < 0 {
        return 0;
    }
    let diff = if price >= ref_price {
        price - ref_price
    } else {
        ref_price - price
    };
    if diff.wrapping_mul(10_000) <= ref_price.wrapping_mul(collar_bps) {
        1
    } else {
        0
    }
}
