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

/// Scalar Wasm-compatible `max` over non-negative (`sign_bit == 0`) or `NaN` `f32` operands.
/// Propagates `NaN` identically to Wasm `f32.max` / `f32x4.max`.
#[inline(always)]
fn wasm_f32_max_nonneg(a: f32, b: f32) -> f32 {
    if a.is_nan() || b.is_nan() {
        a + b
    } else if a >= b {
        a
    } else {
        b
    }
}

// ============================================================================
// Kernel A: 4-Level Vectorized `f32x4` VWAP, Safe Direction & Non-Crossed Quotes
// ============================================================================

/// Scalar 4-level VWAP reference using explicit `((a + b) + (c + d))` reduction tree
/// so floating-point rounding is bit-identical to `vwap_4_v128`.
/// - Guards `!(total_q > 0.0)` -> returns `+0.0` (prevents `0.0 / 0.0 = NaN` poison).
/// - Normalizes `-0.0` -> `+0.0`.
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

/// Vectorized `f32x4` 4-level VWAP using `f32x4_mul`, `f32x4_add`, and `f32x4_extract_lane`.
/// Bit-identical to `vwap_4_ref` across all IEEE-754 `f32` inputs (up to NaN payload).
#[unsafe(no_mangle)]
pub extern "C" fn vwap_4_v128(
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

    let total_q = f32x4_extract_lane::<2>(pair) + f32x4_extract_lane::<3>(pair);
    if !(total_q > 0.0) {
        return 0.0;
    }

    let num = f32x4_extract_lane::<0>(pair) + f32x4_extract_lane::<1>(pair);
    let raw = num / total_q;
    if raw == 0.0 { 0.0 } else { raw }
}

/// Relational postcondition proving exact equivalence between `vwap_4_v128` and `vwap_4_ref`
/// (including exact `+0.0` vs `-0.0` bit identity).
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

/// Precondition for finite non-negative order-book prices and quantities (including empty `q_i == 0.0`).
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

/// Postcondition proving `vwap_4_v128` never produces `NaN`, `+Inf`, `-0.0`, or a negative quote
/// under `req_vwap_4_nonneg_finite` (including when all quantities are `0.0`).
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

/// Compute non-crossed integer bid/ask quote ticks from a floating-point fair value:
/// - `bid_tick = floor(fair_f32) - half_spread_ticks`
/// - `ask_tick = ceil(fair_f32) + half_spread_ticks`
/// Uses Wasm `f32x4.floor` / `f32x4.ceil` + `i32.trunc_sat_f32_s` (never traps on `NaN`/`Inf`).
/// Returns packed `i64`: low 32 bits = `bid_tick`, high 32 bits = `ask_tick`.
#[unsafe(no_mangle)]
pub extern "C" fn quote_ticks_from_fair(fair_f32: f32, half_spread_ticks: i32) -> i64 {
    let v = f32x4_splat(fair_f32);
    let fl_f = f32x4_extract_lane::<0>(f32x4_floor(v));
    let cl_f = f32x4_extract_lane::<0>(f32x4_ceil(v));
    let fl_i = fl_f as i32;
    let cl_i = cl_f as i32;

    let bid_tick = fl_i.wrapping_sub(half_spread_ticks);
    let ask_tick = cl_i.wrapping_add(half_spread_ticks);
    pack_i32_pair(bid_tick, ask_tick)
}

/// Precondition for valid finite fair value and strictly positive half-spread (`>= 1` tick).
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

/// Postcondition proving `quote_ticks_from_fair` ALWAYS produces non-crossed quotes
/// (`bid_tick < ask_tick`) with exact spread in `[2 * half_spread, 2 * half_spread + 1]`.
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

/// Signed order-book imbalance direction signal:
/// - `+1` for `imbalance > 0.0`
/// - `-1` for `imbalance < 0.0`
/// - `0` for `+0.0`, `-0.0`, AND `NaN` (never mistakes `-0.0` for a short signal!).
#[unsafe(no_mangle)]
pub extern "C" fn signal_dir_safe(imbalance: f32) -> i32 {
    if imbalance > 0.0 {
        1
    } else if imbalance < 0.0 {
        -1
    } else {
        0
    }
}

/// Postcondition verifying exact IEEE-754 direction semantics across `+0.0`, `-0.0`, `NaN`, `±Inf`.
#[unsafe(no_mangle)]
pub extern "C" fn ens_signal_dir(imbalance: f32, ret: i32) -> i32 {
    if imbalance > 0.0 {
        if ret == 1 { 1 } else { 0 }
    } else if imbalance < 0.0 {
        if ret == -1 { 1 } else { 0 }
    } else {
        // Covers +0.0, -0.0, and NaN.
        if ret == 0 { 1 } else { 0 }
    }
}

// ============================================================================
// Kernel B: 4-Instrument `f32x4` Portfolio Gross Notional & Peak Exposure
// ============================================================================

/// Scalar reference for 4-instrument gross notional and peak single-name exposure.
/// Returns packed `i64`:
/// - low 32 bits  = `total_gross_notional.to_bits()` = `(n0 + n1) + (n2 + n3)`
/// - high 32 bits = `peak_single_exposure.to_bits()` = `max(max(n0, n1), max(n2, n3))`
/// where `n_i = |pos_i * px_i|`.
#[unsafe(no_mangle)]
pub extern "C" fn portfolio_notional_4_ref(
    pos0: f32,
    pos1: f32,
    pos2: f32,
    pos3: f32,
    px0: f32,
    px1: f32,
    px2: f32,
    px3: f32,
) -> i64 {
    let n0 = (pos0 * px0).abs();
    let n1 = (pos1 * px1).abs();
    let n2 = (pos2 * px2).abs();
    let n3 = (pos3 * px3).abs();

    let total = (n0 + n1) + (n2 + n3);
    let m01 = wasm_f32_max_nonneg(n0, n1);
    let m23 = wasm_f32_max_nonneg(n2, n3);
    let peak = wasm_f32_max_nonneg(m01, m23);

    pack_i32_pair(total.to_bits() as i32, peak.to_bits() as i32)
}

/// Vectorized `f32x4` 4-instrument gross notional & peak single-name exposure
/// using `f32x4_mul`, `f32x4_abs`, `f32x4_add`, `f32x4_max`, and `f32x4_extract_lane`.
/// Bit-identical to `portfolio_notional_4_ref` (up to NaN payload).
#[unsafe(no_mangle)]
pub extern "C" fn portfolio_notional_4_v128(
    pos0: f32,
    pos1: f32,
    pos2: f32,
    pos3: f32,
    px0: f32,
    px1: f32,
    px2: f32,
    px3: f32,
) -> i64 {
    let pos_v = f32x4(pos0, pos1, pos2, pos3);
    let px_v = f32x4(px0, px1, px2, px3);
    let gross = f32x4_abs(f32x4_mul(pos_v, px_v));

    let even = f32x4(
        f32x4_extract_lane::<0>(gross),
        f32x4_extract_lane::<2>(gross),
        0.0,
        0.0,
    );
    let odd = f32x4(
        f32x4_extract_lane::<1>(gross),
        f32x4_extract_lane::<3>(gross),
        0.0,
        0.0,
    );

    let pair_sum = f32x4_add(even, odd);
    let total = f32x4_extract_lane::<0>(pair_sum) + f32x4_extract_lane::<1>(pair_sum);

    let pair_max = f32x4_max(even, odd);
    let m01 = f32x4_extract_lane::<0>(pair_max);
    let m23 = f32x4_extract_lane::<1>(pair_max);
    let peak = f32x4_extract_lane::<0>(f32x4_max(f32x4_splat(m01), f32x4_splat(m23)));

    pack_i32_pair(total.to_bits() as i32, peak.to_bits() as i32)
}

/// Relational postcondition proving bit-exact equivalence between `portfolio_notional_4_v128`
/// and `portfolio_notional_4_ref` for both total gross notional and peak single-name exposure.
#[unsafe(no_mangle)]
pub extern "C" fn ens_portfolio_notional_4_eq(
    pos0: f32,
    pos1: f32,
    pos2: f32,
    pos3: f32,
    px0: f32,
    px1: f32,
    px2: f32,
    px3: f32,
    ret: i64,
) -> i32 {
    let r = portfolio_notional_4_ref(pos0, pos1, pos2, pos3, px0, px1, px2, px3);
    let ret_total = f32::from_bits(ret as u32);
    let ret_peak = f32::from_bits((ret >> 32) as u32);
    let ref_total = f32::from_bits(r as u32);
    let ref_peak = f32::from_bits((r >> 32) as u32);

    if f32_same_bits_or_nan(ret_total, ref_total) && f32_same_bits_or_nan(ret_peak, ref_peak) {
        1
    } else {
        0
    }
}

/// Precondition for finite bounded portfolio positions and mark prices (`|v| <= 1e6`).
#[unsafe(no_mangle)]
pub extern "C" fn req_portfolio_4_finite(
    pos0: f32,
    pos1: f32,
    pos2: f32,
    pos3: f32,
    px0: f32,
    px1: f32,
    px2: f32,
    px3: f32,
) -> i32 {
    let pos_v = f32x4(pos0, pos1, pos2, pos3);
    let px_v = f32x4(px0, px1, px2, px3);
    let lim = f32x4_splat(1_000_000.0);
    let pos_ok = f32x4_le(f32x4_abs(pos_v), lim);
    let px_ok = f32x4_le(f32x4_abs(px_v), lim);
    if i32x4_bitmask(v128_and(pos_ok, px_ok)) == 0xF {
        1
    } else {
        0
    }
}

/// Risk invariant postcondition: for finite bounded positions/prices, gross notional and peak
/// exposure are finite, non-negative, non-`-0.0`, and `peak <= total`.
#[unsafe(no_mangle)]
pub extern "C" fn ens_portfolio_notional_4_safe(
    _pos0: f32,
    _pos1: f32,
    _pos2: f32,
    _pos3: f32,
    _px0: f32,
    _px1: f32,
    _px2: f32,
    _px3: f32,
    ret: i64,
) -> i32 {
    let total = f32::from_bits(ret as u32);
    let peak = f32::from_bits((ret >> 32) as u32);

    if !total.is_nan()
        && !peak.is_nan()
        && total >= 0.0
        && peak >= 0.0
        && total < f32::INFINITY
        && peak <= total
        && total.to_bits() != 0x8000_0000
        && peak.to_bits() != 0x8000_0000
    {
        1
    } else {
        0
    }
}

// ============================================================================
// Inline Verification Harnesses (`gnomon_assume` / `gnomon_assert`)
// ============================================================================

#[unsafe(no_mangle)]
pub extern "C" fn contract_vwap_4_equiv(
    p0: f32,
    p1: f32,
    p2: f32,
    p3: f32,
    q0: f32,
    q1: f32,
    q2: f32,
    q3: f32,
) -> i32 {
    let r = vwap_4_ref(p0, p1, p2, p3, q0, q1, q2, q3);
    let v = vwap_4_v128(p0, p1, p2, p3, q0, q1, q2, q3);
    assert_prop(f32_same_bits_or_nan(v, r));
    1
}

#[unsafe(no_mangle)]
pub extern "C" fn contract_quote_ticks_non_crossed(fair_f32: f32, half_spread_ticks: i32) -> i32 {
    assume(req_fair_valid(fair_f32, half_spread_ticks) == 1);
    let packed = quote_ticks_from_fair(fair_f32, half_spread_ticks);
    assert_prop(ens_quotes_non_crossed(fair_f32, half_spread_ticks, packed) == 1);
    1
}

#[unsafe(no_mangle)]
pub extern "C" fn contract_signal_dir_safe(imbalance: f32) -> i32 {
    let d = signal_dir_safe(imbalance);
    assert_prop(ens_signal_dir(imbalance, d) == 1);
    1
}

#[unsafe(no_mangle)]
pub extern "C" fn contract_portfolio_notional_4_equiv(
    pos0: f32,
    pos1: f32,
    pos2: f32,
    pos3: f32,
    px0: f32,
    px1: f32,
    px2: f32,
    px3: f32,
) -> i32 {
    let v = portfolio_notional_4_v128(pos0, pos1, pos2, pos3, px0, px1, px2, px3);
    assert_prop(ens_portfolio_notional_4_eq(pos0, pos1, pos2, pos3, px0, px1, px2, px3, v) == 1);
    1
}
