#![no_std]

use core::arch::wasm32::*;
use core::sync::atomic::{AtomicI32, Ordering};

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

// ============================================================================
// Mutant 1: `sweep_ask_4_v128_buggy_strict_lt` (strict `<` misses `p_i == limit_px`)
// ============================================================================

/// Reference scalar 4-level ask sweep (inclusive `p_i <= limit_px && q_i > 0`).
#[unsafe(no_mangle)]
pub extern "C" fn sweep_ask_4_ref(
    p0: i32,
    p1: i32,
    p2: i32,
    p3: i32,
    q0: i32,
    q1: i32,
    q2: i32,
    q3: i32,
    limit_px: i32,
) -> i64 {
    let e0 = p0 <= limit_px && q0 > 0;
    let e1 = p1 <= limit_px && q1 > 0;
    let e2 = p2 <= limit_px && q2 > 0;
    let e3 = p3 <= limit_px && q3 > 0;

    let mask = (if e0 { 1 } else { 0 })
        | (if e1 { 2 } else { 0 })
        | (if e2 { 4 } else { 0 })
        | (if e3 { 8 } else { 0 });

    let a0 = if e0 { q0 } else { 0 };
    let a1 = if e1 { q1 } else { 0 };
    let a2 = if e2 { q2 } else { 0 };
    let a3 = if e3 { q3 } else { 0 };
    let total = a0.wrapping_add(a1).wrapping_add(a2).wrapping_add(a3);

    pack_i32_pair(total, mask)
}

/// Buggy Mutant 1: uses `i32x4_lt` instead of `i32x4_le`, silently dropping ask
/// liquidity resting right at `limit_px`.
#[unsafe(no_mangle)]
pub extern "C" fn sweep_ask_4_v128_buggy_strict_lt(
    p0: i32,
    p1: i32,
    p2: i32,
    p3: i32,
    q0: i32,
    q1: i32,
    q2: i32,
    q3: i32,
    limit_px: i32,
) -> i64 {
    let px = i32x4(p0, p1, p2, p3);
    let qty = i32x4(q0, q1, q2, q3);
    let lim = i32x4_splat(limit_px);
    let zero = i32x4_splat(0);

    // BUG: strict `<` instead of `<=` (`i32x4_lt` instead of `i32x4_le`).
    let px_ok = i32x4_lt(px, lim);
    let qty_ok = i32x4_gt(qty, zero);
    let elig = v128_and(px_ok, qty_ok);

    let mask = i32x4_bitmask(elig) as i32;
    let avail = v128_and(qty, elig);

    let sum01 = i32x4_extract_lane::<0>(avail).wrapping_add(i32x4_extract_lane::<1>(avail));
    let sum23 = i32x4_extract_lane::<2>(avail).wrapping_add(i32x4_extract_lane::<3>(avail));
    let total = sum01.wrapping_add(sum23);

    pack_i32_pair(total, mask)
}

/// Relational postcondition (FALSIFIED by `sweep_ask_4_v128_buggy_strict_lt`).
#[unsafe(no_mangle)]
pub extern "C" fn ens_sweep_ask_4_eq(
    p0: i32,
    p1: i32,
    p2: i32,
    p3: i32,
    q0: i32,
    q1: i32,
    q2: i32,
    q3: i32,
    limit_px: i32,
    ret: i64,
) -> i32 {
    let mask = (ret >> 32) as i32;
    if mask < 0 || mask > 15 {
        return 0;
    }
    if ret == sweep_ask_4_ref(p0, p1, p2, p3, q0, q1, q2, q3, limit_px) {
        1
    } else {
        0
    }
}

/// Inline contract harness (FALSIFIED by Mutant 1 when any `p_i == limit_px && q_i > 0`).
#[unsafe(no_mangle)]
pub extern "C" fn contract_sweep_ask_4_equiv_buggy(
    p0: i32,
    p1: i32,
    p2: i32,
    p3: i32,
    q0: i32,
    q1: i32,
    q2: i32,
    q3: i32,
    limit_px: i32,
) -> i32 {
    let r = sweep_ask_4_ref(p0, p1, p2, p3, q0, q1, q2, q3, limit_px);
    let v = sweep_ask_4_v128_buggy_strict_lt(p0, p1, p2, p3, q0, q1, q2, q3, limit_px);
    assert_prop(v == r);
    1
}

// ============================================================================
// Mutant 2: `book_set_bid_buggy_allows_cross` (allows `bid >= best_ask`)
// ============================================================================

const DEPTH: i32 = 8;
const LEVEL_MASK: i32 = 7;

#[repr(C, align(16))]
struct BookSide8([AtomicI32; 8]);

const fn zero_book_side() -> BookSide8 {
    BookSide8([
        AtomicI32::new(0),
        AtomicI32::new(0),
        AtomicI32::new(0),
        AtomicI32::new(0),
        AtomicI32::new(0),
        AtomicI32::new(0),
        AtomicI32::new(0),
        AtomicI32::new(0),
    ])
}

static BID_PX: BookSide8 = zero_book_side();
static BID_QTY: BookSide8 = zero_book_side();
static ASK_PX: BookSide8 = zero_book_side();
static ASK_QTY: BookSide8 = zero_book_side();

static BID_MASK: AtomicI32 = AtomicI32::new(0);
static ASK_MASK: AtomicI32 = AtomicI32::new(0);

#[inline(always)]
fn load_v4(arr: &BookSide8, base: usize) -> v128 {
    unsafe { v128_load(arr.0.as_ptr().add(base) as *const v128) }
}

#[inline(always)]
fn max_i32(a: i32, b: i32) -> i32 {
    if a >= b { a } else { b }
}

#[inline(always)]
fn min_i32(a: i32, b: i32) -> i32 {
    if a <= b { a } else { b }
}

#[inline(always)]
fn best_bid_v128() -> i32 {
    let zero = i32x4_splat(0);
    let neg_inf = i32x4_splat(i32::MIN);

    let act_lo = i32x4_gt(load_v4(&BID_QTY, 0), zero);
    let act_hi = i32x4_gt(load_v4(&BID_QTY, 4), zero);

    let cand_lo = v128_bitselect(load_v4(&BID_PX, 0), neg_inf, act_lo);
    let cand_hi = v128_bitselect(load_v4(&BID_PX, 4), neg_inf, act_hi);
    let m4 = i32x4_max(cand_lo, cand_hi);

    let m01 = max_i32(i32x4_extract_lane::<0>(m4), i32x4_extract_lane::<1>(m4));
    let m23 = max_i32(i32x4_extract_lane::<2>(m4), i32x4_extract_lane::<3>(m4));
    max_i32(m01, m23)
}

#[inline(always)]
fn best_ask_v128() -> i32 {
    let zero = i32x4_splat(0);
    let pos_inf = i32x4_splat(i32::MAX);

    let act_lo = i32x4_gt(load_v4(&ASK_QTY, 0), zero);
    let act_hi = i32x4_gt(load_v4(&ASK_QTY, 4), zero);

    let cand_lo = v128_bitselect(load_v4(&ASK_PX, 0), pos_inf, act_lo);
    let cand_hi = v128_bitselect(load_v4(&ASK_PX, 4), pos_inf, act_hi);
    let m4 = i32x4_min(cand_lo, cand_hi);

    let m01 = min_i32(i32x4_extract_lane::<0>(m4), i32x4_extract_lane::<1>(m4));
    let m23 = min_i32(i32x4_extract_lane::<2>(m4), i32x4_extract_lane::<3>(m4));
    min_i32(m01, m23)
}

#[inline(always)]
fn active_mask_8_v128(qty_arr: &BookSide8) -> i32 {
    let zero = i32x4_splat(0);
    let lo = i32x4_bitmask(i32x4_gt(load_v4(qty_arr, 0), zero)) as i32;
    let hi = i32x4_bitmask(i32x4_gt(load_v4(qty_arr, 4), zero)) as i32;
    lo | (hi << 4)
}

/// Clean initializer (shared baseline for buggy L2 book).
#[unsafe(no_mangle)]
pub extern "C" fn init_l2_book() {
    let mut i = 0usize;
    while i < 8 {
        BID_PX.0[i].store(0, Ordering::Relaxed);
        BID_QTY.0[i].store(0, Ordering::Relaxed);
        ASK_PX.0[i].store(0, Ordering::Relaxed);
        ASK_QTY.0[i].store(0, Ordering::Relaxed);
        i += 1;
    }
    BID_MASK.store(0, Ordering::Relaxed);
    ASK_MASK.store(0, Ordering::Relaxed);
}

/// Buggy Mutant 2: omits the `px >= best_ask` non-crossing check when setting a bid,
/// allowing a crossed book (`best_bid >= best_ask`) that violates `inv_l2_book()`.
#[unsafe(no_mangle)]
pub extern "C" fn book_set_bid_buggy_allows_cross(level: i32, px: i32, qty: i32) -> i32 {
    if level < 0 || level >= DEPTH || qty < 0 {
        return 0;
    }
    let idx = (level & LEVEL_MASK) as usize;
    let bit = 1i32 << (level & LEVEL_MASK);

    if qty == 0 {
        BID_PX.0[idx].store(0, Ordering::Relaxed);
        BID_QTY.0[idx].store(0, Ordering::Relaxed);
        let m = BID_MASK.load(Ordering::Relaxed);
        BID_MASK.store(m & !bit, Ordering::Relaxed);
        return 1;
    }

    if px <= 0 {
        return 0;
    }

    // BUG: missing `if ask_m != 0 && px >= best_ask_v128() { return 0; }` guard!
    BID_PX.0[idx].store(px, Ordering::Relaxed);
    BID_QTY.0[idx].store(qty, Ordering::Relaxed);
    let m = BID_MASK.load(Ordering::Relaxed);
    BID_MASK.store(m | bit, Ordering::Relaxed);
    1
}

/// Clean ask setter (shared baseline).
#[unsafe(no_mangle)]
pub extern "C" fn book_set_ask(level: i32, px: i32, qty: i32) -> i32 {
    if level < 0 || level >= DEPTH || qty < 0 {
        return 0;
    }
    let idx = (level & LEVEL_MASK) as usize;
    let bit = 1i32 << (level & LEVEL_MASK);

    if qty == 0 {
        ASK_PX.0[idx].store(0, Ordering::Relaxed);
        ASK_QTY.0[idx].store(0, Ordering::Relaxed);
        let m = ASK_MASK.load(Ordering::Relaxed);
        ASK_MASK.store(m & !bit, Ordering::Relaxed);
        return 1;
    }

    if px <= 0 {
        return 0;
    }

    let bid_m = BID_MASK.load(Ordering::Relaxed);
    if bid_m != 0 && px <= best_bid_v128() {
        return 0;
    }

    ASK_PX.0[idx].store(px, Ordering::Relaxed);
    ASK_QTY.0[idx].store(qty, Ordering::Relaxed);
    let m = ASK_MASK.load(Ordering::Relaxed);
    ASK_MASK.store(m | bit, Ordering::Relaxed);
    1
}

/// Inductive L2 book invariant (violated by `book_set_bid_buggy_allows_cross`).
#[unsafe(no_mangle)]
pub extern "C" fn inv_l2_book() -> i32 {
    let bid_m = BID_MASK.load(Ordering::Relaxed);
    let ask_m = ASK_MASK.load(Ordering::Relaxed);

    if (bid_m & !0xFF) != 0 || (ask_m & !0xFF) != 0 {
        return 0;
    }

    if bid_m != active_mask_8_v128(&BID_QTY) || ask_m != active_mask_8_v128(&ASK_QTY) {
        return 0;
    }

    let mut i = 0usize;
    while i < 8 {
        let bp = BID_PX.0[i].load(Ordering::Relaxed);
        let bq = BID_QTY.0[i].load(Ordering::Relaxed);
        let ap = ASK_PX.0[i].load(Ordering::Relaxed);
        let aq = ASK_QTY.0[i].load(Ordering::Relaxed);

        if bq < 0 || aq < 0 {
            return 0;
        }
        if bq > 0 && bp <= 0 {
            return 0;
        }
        if bq == 0 && bp != 0 {
            return 0;
        }
        if aq > 0 && ap <= 0 {
            return 0;
        }
        if aq == 0 && ap != 0 {
            return 0;
        }
        i += 1;
    }

    if bid_m != 0 && ask_m != 0 && best_bid_v128() >= best_ask_v128() {
        return 0;
    }

    1
}

/// Inline contract harness (FALSIFIED by Mutant 2 when ask side is non-empty and `px >= best_ask`).
#[unsafe(no_mangle)]
pub extern "C" fn contract_book_set_bid_preserves_inv_buggy(
    level: i32,
    px: i32,
    qty: i32,
) -> i32 {
    assume(inv_l2_book() == 1);
    let ok = book_set_bid_buggy_allows_cross(level, px, qty);
    assert_prop(inv_l2_book() == 1);
    ok
}
