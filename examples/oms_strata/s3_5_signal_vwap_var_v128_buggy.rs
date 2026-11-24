#![no_std]

use core::arch::wasm32::*;

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

#[inline(always)]
fn pack_i32_pair(lo: i32, hi: i32) -> i64 {
    ((((hi as u32) as u64) << 32) | ((lo as u32) as u64)) as i64
}

#[inline(always)]
fn f32_same_bits_or_nan(a: f32, b: f32) -> bool {
    (a.is_nan() && b.is_nan()) || (a.to_bits() == b.to_bits())
}

// ============================================================================
// Mutant 1: `vwap_4_buggy_nan_empty` (`0.0 / 0.0 = NaN` quote poison on empty book)
// ============================================================================

/// Clean scalar reference (guards `!(total_q > 0.0)` and normalizes `-0.0`).
#[unsafe(no_mangle)]
pub extern "C" fn vwap_4_ref(
    p0: f32,
    p1: f32,
    p2: f32,
    p3: f32,
    q0: f32,
    q1: f32,
    q2: f32,
    q3: f32,
) -> f32 {
    let pq0 = p0 * q0;
    let pq1 = p1 * q1;
    let pq2 = p2 * q2;
    let pq3 = p3 * q3;

    let num = (pq0 + pq1) + (pq2 + pq3);
    let total_q = (q0 + q1) + (q2 + q3);

    if !(total_q > 0.0) {
        return 0.0;
    }

    let raw = num / total_q;
    if raw == 0.0 { 0.0 } else { raw }
}

/// Buggy Mutant 1: omits `if !(total_q > 0.0)` guard and divides `num / total_q` directly.
/// When all 4 quantities are `0.0`, evaluates `0.0 / 0.0 = NaN` (quote poison!).
#[unsafe(no_mangle)]
pub extern "C" fn vwap_4_buggy_nan_empty(
    p0: f32,
    p1: f32,
    p2: f32,
    p3: f32,
    q0: f32,
    q1: f32,
    q2: f32,
    q3: f32,
) -> f32 {
    let p_vec = f32x4(p0, p1, p2, p3);
    let q_vec = f32x4(q0, q1, q2, q3);
    let pq = f32x4_mul(p_vec, q_vec);

    let even = f32x4(
        f32x4_extract_lane::<0>(pq),
        f32x4_extract_lane::<2>(pq),
        f32x4_extract_lane::<0>(q_vec),
        f32x4_extract_lane::<2>(q_vec),
    );
    let odd = f32x4(
        f32x4_extract_lane::<1>(pq),
        f32x4_extract_lane::<3>(pq),
        f32x4_extract_lane::<1>(q_vec),
        f32x4_extract_lane::<3>(q_vec),
    );
    let pair = f32x4_add(even, odd);

    let num = f32x4_extract_lane::<0>(pair) + f32x4_extract_lane::<1>(pair);
    let total_q = f32x4_extract_lane::<2>(pair) + f32x4_extract_lane::<3>(pair);

    // BUG: no guard for `total_q <= 0.0` -> `0.0 / 0.0 = NaN` when book is empty!
    let raw = num / total_q;
    if raw == 0.0 { 0.0 } else { raw }
}

#[unsafe(no_mangle)]
pub extern "C" fn ens_vwap_4_eq(
    p0: f32,
    p1: f32,
    p2: f32,
    p3: f32,
    q0: f32,
    q1: f32,
    q2: f32,
    q3: f32,
    ret: f32,
) -> i32 {
    let r = vwap_4_ref(p0, p1, p2, p3, q0, q1, q2, q3);
    if f32_same_bits_or_nan(ret, r) { 1 } else { 0 }
}

#[unsafe(no_mangle)]
pub extern "C" fn req_vwap_4_nonneg_finite(
    p0: f32,
    p1: f32,
    p2: f32,
    p3: f32,
    q0: f32,
    q1: f32,
    q2: f32,
    q3: f32,
) -> i32 {
    let pv = f32x4(p0, p1, p2, p3);
    let qv = f32x4(q0, q1, q2, q3);
    let lo = f32x4_splat(0.0);
    let hi = f32x4_splat(1_000_000.0);
    let p_ok = v128_and(f32x4_ge(pv, lo), f32x4_le(pv, hi));
    let q_ok = v128_and(f32x4_ge(qv, lo), f32x4_le(qv, hi));
    if i32x4_bitmask(v128_and(p_ok, q_ok)) == 0xF {
        1
    } else {
        0
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn ens_vwap_4_safe(
    _p0: f32,
    _p1: f32,
    _p2: f32,
    _p3: f32,
    _q0: f32,
    _q1: f32,
    _q2: f32,
    _q3: f32,
    ret: f32,
) -> i32 {
    if !ret.is_nan()
        && ret >= 0.0
        && ret < f32::INFINITY
        && ret.to_bits() != 0x8000_0000
    {
        1
    } else {
        0
    }
}

/// Inline contract harness (FALSIFIED by Mutant 1 on `q0 = q1 = q2 = q3 = 0.0`).
#[unsafe(no_mangle)]
pub extern "C" fn contract_vwap_4_safe_buggy(
    p0: f32,
    p1: f32,
    p2: f32,
    p3: f32,
    q0: f32,
    q1: f32,
    q2: f32,
    q3: f32,
) -> i32 {
    assume(req_vwap_4_nonneg_finite(p0, p1, p2, p3, q0, q1, q2, q3) == 1);
    let v = vwap_4_buggy_nan_empty(p0, p1, p2, p3, q0, q1, q2, q3);
    assert_prop(ens_vwap_4_safe(p0, p1, p2, p3, q0, q1, q2, q3, v) == 1);
    1
}

// ============================================================================
// Mutant 2: `signal_dir_buggy_neg_zero` (sign-bit check treats `-0.0` as `-1` short!)
// ============================================================================

/// Buggy Mutant 2: inspects IEEE-754 sign bit (`to_bits() >> 31`) instead of numeric `< 0.0`.
/// Handles `+0.0` (`bits == 0`) and `NaN`, but falsely classifies `-0.0` (`0x8000_0000`) as `-1`!
#[unsafe(no_mangle)]
pub extern "C" fn signal_dir_buggy_neg_zero(imbalance: f32) -> i32 {
    if imbalance.is_nan() {
        return 0;
    }
    let bits = imbalance.to_bits();
    if bits == 0 {
        0
    } else if (bits >> 31) != 0 {
        // BUG: `-0.0` has `bits == 0x8000_0000` -> returns `-1` (short) instead of `0` (flat)!
        -1
    } else {
        1
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn ens_signal_dir(imbalance: f32, ret: i32) -> i32 {
    if imbalance > 0.0 {
        if ret == 1 { 1 } else { 0 }
    } else if imbalance < 0.0 {
        if ret == -1 { 1 } else { 0 }
    } else {
        if ret == 0 { 1 } else { 0 }
    }
}

/// Inline contract harness (FALSIFIED by Mutant 2 with exact counterexample `imbalance = -0.0`).
#[unsafe(no_mangle)]
pub extern "C" fn contract_signal_dir_buggy(imbalance: f32) -> i32 {
    let d = signal_dir_buggy_neg_zero(imbalance);
    assert_prop(ens_signal_dir(imbalance, d) == 1);
    1
}

// ============================================================================
// Mutant 3: `quote_ticks_buggy_trunc_cross` (trunc + half-spread truncation -> self-cross!)
// ============================================================================

/// Buggy Mutant 3: uses `f32x4_trunc` for both sides AND shifts `half_spread_ticks >> 1`
/// (truncating `half_spread_ticks == 1` down to `0`), emitting self-crossed `bid_tick == ask_tick`!
#[unsafe(no_mangle)]
pub extern "C" fn quote_ticks_buggy_trunc_cross(fair_f32: f32, half_spread_ticks: i32) -> i64 {
    let v = f32x4_splat(fair_f32);
    let tr_f = f32x4_extract_lane::<0>(f32x4_trunc(v));
    let tr_i = tr_f as i32;

    // BUG: `half_spread_ticks >> 1` becomes `0` when `half_spread_ticks == 1`, and using
    // `trunc` on both bid and ask collapses `bid_tick == ask_tick` (self-crossed quote!).
    let half = half_spread_ticks >> 1;
    let bid_tick = tr_i.wrapping_sub(half);
    let ask_tick = tr_i.wrapping_add(half);
    pack_i32_pair(bid_tick, ask_tick)
}

#[unsafe(no_mangle)]
pub extern "C" fn req_fair_valid(fair_f32: f32, half_spread_ticks: i32) -> i32 {
    if fair_f32 >= -1_000_000_000.0
        && fair_f32 <= 1_000_000_000.0
        && half_spread_ticks >= 1
        && half_spread_ticks <= 100_000_000
    {
        1
    } else {
        0
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn ens_quotes_non_crossed(
    _fair_f32: f32,
    half_spread_ticks: i32,
    packed: i64,
) -> i32 {
    let bid_tick = packed as i32;
    let ask_tick = (packed >> 32) as i32;
    let spread = (ask_tick as i64) - (bid_tick as i64);
    let min_spread = 2i64 * (half_spread_ticks as i64);

    if bid_tick < ask_tick && spread >= min_spread && spread <= min_spread + 1 {
        1
    } else {
        0
    }
}

/// Inline contract harness (FALSIFIED by Mutant 3 when `half_spread_ticks == 1`).
#[unsafe(no_mangle)]
pub extern "C" fn contract_quote_ticks_buggy(fair_f32: f32, half_spread_ticks: i32) -> i32 {
    assume(req_fair_valid(fair_f32, half_spread_ticks) == 1);
    let packed = quote_ticks_buggy_trunc_cross(fair_f32, half_spread_ticks);
    assert_prop(ens_quotes_non_crossed(fair_f32, half_spread_ticks, packed) == 1);
    1
}
