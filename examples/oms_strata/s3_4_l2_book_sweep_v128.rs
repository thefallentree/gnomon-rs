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
// Part 1: Pure 4-Level v128 (1x i32x4) Ask-Side Price-Level Sweep
// ============================================================================

/// Reference scalar 4-level ask sweep (pure, total, zero memory).
/// Level `i` is eligible iff `p_i <= limit_px && q_i > 0`.
/// Returns packed `i64`: high 32 bits = 4-bit `eligible_mask`, low 32 bits = wrapping `total_avail_qty`.
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

/// Vectorized `v128` (`i32x4`) 4-level ask sweep using `i32x4_le`, `i32x4_gt`,
/// `v128_and`, `i32x4_bitmask`, and lane horizontal sum.
/// Bit-identical to `sweep_ask_4_ref` over all 2^(32*9) inputs.
#[unsafe(no_mangle)]
pub extern "C" fn sweep_ask_4_v128(
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

    let px_ok = i32x4_le(px, lim);
    let qty_ok = i32x4_gt(qty, zero);
    let elig = v128_and(px_ok, qty_ok);

    let mask = i32x4_bitmask(elig) as i32;
    let avail = v128_and(qty, elig);

    let sum01 = i32x4_extract_lane::<0>(avail).wrapping_add(i32x4_extract_lane::<1>(avail));
    let sum23 = i32x4_extract_lane::<2>(avail).wrapping_add(i32x4_extract_lane::<3>(avail));
    let total = sum01.wrapping_add(sum23);

    pack_i32_pair(total, mask)
}

/// Relational postcondition proving exact equivalence between `sweep_ask_4_v128` and `sweep_ask_4_ref`.
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

/// Inline equivalence contract harness for 4-level ask sweep.
#[unsafe(no_mangle)]
pub extern "C" fn contract_sweep_ask_4_equiv(
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
    let v = sweep_ask_4_v128(p0, p1, p2, p3, q0, q1, q2, q3, limit_px);
    assert_prop(v == r);
    1
}

// ============================================================================
// Part 2: Pure 4-Level Widening Notional Sweep (1x i32x4 + 2x i64x2)
// ============================================================================

/// Scalar reference for 4-level widening 64-bit sweep notional `sum(px_i * qty_i)`
/// across all eligible levels (`p_i <= limit_px && q_i > 0`).
#[unsafe(no_mangle)]
pub extern "C" fn sweep_ask_4_notional_ref(
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
    let n0 = if p0 <= limit_px && q0 > 0 {
        (p0 as i64).wrapping_mul(q0 as i64)
    } else {
        0
    };
    let n1 = if p1 <= limit_px && q1 > 0 {
        (p1 as i64).wrapping_mul(q1 as i64)
    } else {
        0
    };
    let n2 = if p2 <= limit_px && q2 > 0 {
        (p2 as i64).wrapping_mul(q2 as i64)
    } else {
        0
    };
    let n3 = if p3 <= limit_px && q3 > 0 {
        (p3 as i64).wrapping_mul(q3 as i64)
    } else {
        0
    };
    n0.wrapping_add(n1).wrapping_add(n2.wrapping_add(n3))
}

/// Vectorized `2x i64x2` widening 64-bit sweep notional using `i32x4` masking
/// followed by `i64x2_mul` and `i64x2_add`.
#[unsafe(no_mangle)]
pub extern "C" fn sweep_ask_4_notional_v128(
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
    let elig = v128_and(i32x4_le(px, i32x4_splat(limit_px)), i32x4_gt(qty, i32x4_splat(0)));
    let avail = v128_and(qty, elig);

    let px_lo = i64x2(p0 as i64, p1 as i64);
    let px_hi = i64x2(p2 as i64, p3 as i64);
    let q_lo = i64x2(
        i32x4_extract_lane::<0>(avail) as i64,
        i32x4_extract_lane::<1>(avail) as i64,
    );
    let q_hi = i64x2(
        i32x4_extract_lane::<2>(avail) as i64,
        i32x4_extract_lane::<3>(avail) as i64,
    );

    let n_lo = i64x2_mul(px_lo, q_lo);
    let n_hi = i64x2_mul(px_hi, q_hi);
    let n_sum = i64x2_add(n_lo, n_hi);

    i64x2_extract_lane::<0>(n_sum).wrapping_add(i64x2_extract_lane::<1>(n_sum))
}

/// Relational postcondition proving exact equivalence for 4-level widening notional sweep.
#[unsafe(no_mangle)]
pub extern "C" fn ens_sweep_ask_4_notional_eq(
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
    if ret == sweep_ask_4_notional_ref(p0, p1, p2, p3, q0, q1, q2, q3, limit_px) {
        1
    } else {
        0
    }
}

// ============================================================================
// Part 3: Stateful 8-Level (2x i32x4) L2 Order Book & Non-Crossed Invariant
// ============================================================================

const DEPTH: i32 = 8;
const LEVEL_MASK: i32 = 7;

// Fixed 16-byte-aligned linear-memory L2 order book slots (`globals: 0`, zero shadow stack).
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
    // SAFETY: `BookSide8` is 16-byte aligned with 8 contiguous `AtomicI32` slots (32 bytes),
    // and callers only pass `base == 0` or `base == 4` (16-byte aligned 4-lane chunks).
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

/// Vectorized (`2x i32x4`) best bid price across active levels (`qty > 0`).
/// Returns `i32::MIN` when the bid side is empty.
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

/// Vectorized (`2x i32x4`) best ask price across active levels (`qty > 0`).
/// Returns `i32::MAX` when the ask side is empty.
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

/// Vectorized (`2x i32x4`) 8-bit active level mask (`bit i <=> qty[i] > 0`).
#[inline(always)]
fn active_mask_8_v128(qty_arr: &BookSide8) -> i32 {
    let zero = i32x4_splat(0);
    let lo = i32x4_bitmask(i32x4_gt(load_v4(qty_arr, 0), zero)) as i32;
    let hi = i32x4_bitmask(i32x4_gt(load_v4(qty_arr, 4), zero)) as i32;
    lo | (hi << 4)
}

/// Initialize an empty 8-level L2 order book (establishes `inv_l2_book() == 1`).
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

/// Update or clear a bid price level (`0 <= level < 8`).
/// - `qty == 0` clears the level (`px = 0, qty = 0`, clears bit `level` in `BID_MASK`).
/// - `qty > 0` requires `px > 0` and, if asks are non-empty, `px < best_ask`.
/// Returns `1` if accepted, `0` if rejected (state unchanged).
#[unsafe(no_mangle)]
pub extern "C" fn book_set_bid(level: i32, px: i32, qty: i32) -> i32 {
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

    let ask_m = ASK_MASK.load(Ordering::Relaxed);
    if ask_m != 0 && px >= best_ask_v128() {
        return 0;
    }

    BID_PX.0[idx].store(px, Ordering::Relaxed);
    BID_QTY.0[idx].store(qty, Ordering::Relaxed);
    let m = BID_MASK.load(Ordering::Relaxed);
    BID_MASK.store(m | bit, Ordering::Relaxed);
    1
}

/// Update or clear an ask price level (`0 <= level < 8`).
/// - `qty == 0` clears the level (`px = 0, qty = 0`, clears bit `level` in `ASK_MASK`).
/// - `qty > 0` requires `px > 0` and, if bids are non-empty, `px > best_bid`.
/// Returns `1` if accepted, `0` if rejected (state unchanged).
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

/// Scalar reference 8-level ask sweep over the stateful L2 book.
/// Returns packed `i64`: high 32 bits = 8-bit `eligible_mask`, low 32 bits = wrapping `total_avail_qty`.
#[unsafe(no_mangle)]
pub extern "C" fn book_sweep_ask_8_ref(limit_px: i32) -> i64 {
    let mut mask = 0i32;
    let mut total = 0i32;
    let mut i = 0usize;
    while i < 8 {
        let p = ASK_PX.0[i].load(Ordering::Relaxed);
        let q = ASK_QTY.0[i].load(Ordering::Relaxed);
        if p <= limit_px && q > 0 {
            mask |= 1i32 << (i as i32);
            total = total.wrapping_add(q);
        }
        i += 1;
    }
    pack_i32_pair(total, mask)
}

/// Vectorized (`2x i32x4`) 8-level ask sweep over the stateful L2 book.
/// Bit-identical to `book_sweep_ask_8_ref(limit_px)`.
#[unsafe(no_mangle)]
pub extern "C" fn book_sweep_ask_8_v128(limit_px: i32) -> i64 {
    let lim = i32x4_splat(limit_px);
    let zero = i32x4_splat(0);

    let px_lo = load_v4(&ASK_PX, 0);
    let qty_lo = load_v4(&ASK_QTY, 0);
    let elig_lo = v128_and(i32x4_le(px_lo, lim), i32x4_gt(qty_lo, zero));
    let mask_lo = i32x4_bitmask(elig_lo) as i32;
    let avail_lo = v128_and(qty_lo, elig_lo);

    let px_hi = load_v4(&ASK_PX, 4);
    let qty_hi = load_v4(&ASK_QTY, 4);
    let elig_hi = v128_and(i32x4_le(px_hi, lim), i32x4_gt(qty_hi, zero));
    let mask_hi = i32x4_bitmask(elig_hi) as i32;
    let avail_hi = v128_and(qty_hi, elig_hi);

    let mask = mask_lo | (mask_hi << 4);
    let sum_v = i32x4_add(avail_lo, avail_hi);
    let sum01 = i32x4_extract_lane::<0>(sum_v).wrapping_add(i32x4_extract_lane::<1>(sum_v));
    let sum23 = i32x4_extract_lane::<2>(sum_v).wrapping_add(i32x4_extract_lane::<3>(sum_v));
    let total = sum01.wrapping_add(sum23);

    pack_i32_pair(total, mask)
}

/// Relational postcondition proving exact equivalence for stateful 8-level ask sweep.
#[unsafe(no_mangle)]
pub extern "C" fn ens_book_sweep_ask_8_eq(limit_px: i32, ret: i64) -> i32 {
    if ret == book_sweep_ask_8_ref(limit_px) {
        1
    } else {
        0
    }
}

/// Inductive L2 Order Book invariant (`1` = valid, `0` = violated):
/// 1. `BID_MASK` / `ASK_MASK` only use bits `0..8` and match `qty[i] > 0` for all 8 levels.
/// 2. Every level has `qty[i] >= 0`, `qty[i] > 0 => px[i] > 0`, and `qty[i] == 0 => px[i] == 0`.
/// 3. Non-crossed book: `(!empty_bid && !empty_ask) => best_bid < best_ask`.
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

/// Inline inductive contract: `book_set_bid` preserves `inv_l2_book()` (never crosses book).
#[unsafe(no_mangle)]
pub extern "C" fn contract_book_set_bid_preserves_inv(level: i32, px: i32, qty: i32) -> i32 {
    assume(inv_l2_book() == 1);
    let ok = book_set_bid(level, px, qty);
    assert_prop(inv_l2_book() == 1);
    ok
}

/// Inline inductive contract: `book_set_ask` preserves `inv_l2_book()` (never crosses book).
#[unsafe(no_mangle)]
pub extern "C" fn contract_book_set_ask_preserves_inv(level: i32, px: i32, qty: i32) -> i32 {
    assume(inv_l2_book() == 1);
    let ok = book_set_ask(level, px, qty);
    assert_prop(inv_l2_book() == 1);
    ok
}
