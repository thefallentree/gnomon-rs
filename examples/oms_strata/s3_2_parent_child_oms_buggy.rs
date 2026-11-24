#![no_std]

use core::sync::atomic::{AtomicI64, AtomicU8, Ordering};

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

const P_EMPTY: u8 = 0;
const P_WORKING: u8 = 1;
const P_COMPLETE: u8 = 2;

const C_EMPTY: u8 = 0;
const C_PENDING_NEW: u8 = 1;
const C_LIVE: u8 = 2;
const C_PENDING_REPLACE: u8 = 3;
const C_PENDING_CANCEL: u8 = 4;
const C_FILLED: u8 = 5;
const C_CANCELED: u8 = 6;
const C_REJECTED: u8 = 7;

static P_ACTIVE: AtomicU8 = AtomicU8::new(0);
static P_STATUS: AtomicU8 = AtomicU8::new(P_EMPTY);
static P_TARGET_QTY: AtomicI64 = AtomicI64::new(0);
static P_CUM_FILLED: AtomicI64 = AtomicI64::new(0);
static P_OPEN_WORST: AtomicI64 = AtomicI64::new(0);

static C_STATE: [AtomicU8; 4] = [
    AtomicU8::new(C_EMPTY),
    AtomicU8::new(C_EMPTY),
    AtomicU8::new(C_EMPTY),
    AtomicU8::new(C_EMPTY),
];
static C_LEAVES: [AtomicI64; 4] = [
    AtomicI64::new(0),
    AtomicI64::new(0),
    AtomicI64::new(0),
    AtomicI64::new(0),
];
static C_CUM: [AtomicI64; 4] = [
    AtomicI64::new(0),
    AtomicI64::new(0),
    AtomicI64::new(0),
    AtomicI64::new(0),
];
static C_PENDING: [AtomicI64; 4] = [
    AtomicI64::new(0),
    AtomicI64::new(0),
    AtomicI64::new(0),
    AtomicI64::new(0),
];
static C_WORST: [AtomicI64; 4] = [
    AtomicI64::new(0),
    AtomicI64::new(0),
    AtomicI64::new(0),
    AtomicI64::new(0),
];

#[inline(always)]
fn max_i64(a: i64, b: i64) -> i64 {
    if a >= b { a } else { b }
}

#[inline(always)]
fn sum4_checked(a: i64, b: i64, c: i64, d: i64) -> i64 {
    let s01 = a.wrapping_add(b);
    let s23 = c.wrapping_add(d);
    let s = s01.wrapping_add(s23);
    if (a | b | c | d | s01 | s23 | s) < 0 {
        -1
    } else {
        s
    }
}

#[inline(always)]
fn sum4_eq(a: i64, b: i64, c: i64, d: i64, total: i64) -> bool {
    let s01 = a.wrapping_add(b);
    let s23 = c.wrapping_add(d);
    let s = s01.wrapping_add(s23);
    ((a | b | c | d | total | s01 | s23 | s) >= 0) && (s == total)
}

#[inline(always)]
fn recompute_open_worst_with<const S: usize>(new_s_worst: i64) -> i64 {
    let w0 = if S == 0 { new_s_worst } else { C_WORST[0].load(Ordering::Relaxed) };
    let w1 = if S == 1 { new_s_worst } else { C_WORST[1].load(Ordering::Relaxed) };
    let w2 = if S == 2 { new_s_worst } else { C_WORST[2].load(Ordering::Relaxed) };
    let w3 = if S == 3 { new_s_worst } else { C_WORST[3].load(Ordering::Relaxed) };
    sum4_checked(w0, w1, w2, w3)
}

#[inline(always)]
fn recompute_cum_filled_with<const S: usize>(new_s_cum: i64) -> i64 {
    let u0 = if S == 0 { new_s_cum } else { C_CUM[0].load(Ordering::Relaxed) };
    let u1 = if S == 1 { new_s_cum } else { C_CUM[1].load(Ordering::Relaxed) };
    let u2 = if S == 2 { new_s_cum } else { C_CUM[2].load(Ordering::Relaxed) };
    let u3 = if S == 3 { new_s_cum } else { C_CUM[3].load(Ordering::Relaxed) };
    sum4_checked(u0, u1, u2, u3)
}

#[inline(always)]
fn load_c_state(slot: i32) -> u8 {
    let v0 = C_STATE[0].load(Ordering::Relaxed);
    let v1 = C_STATE[1].load(Ordering::Relaxed);
    let v2 = C_STATE[2].load(Ordering::Relaxed);
    let v3 = C_STATE[3].load(Ordering::Relaxed);
    if slot == 0 {
        v0
    } else if slot == 1 {
        v1
    } else if slot == 2 {
        v2
    } else {
        v3
    }
}

#[inline(always)]
fn load_c_leaves(slot: i32) -> i64 {
    let v0 = C_LEAVES[0].load(Ordering::Relaxed);
    let v1 = C_LEAVES[1].load(Ordering::Relaxed);
    let v2 = C_LEAVES[2].load(Ordering::Relaxed);
    let v3 = C_LEAVES[3].load(Ordering::Relaxed);
    if slot == 0 {
        v0
    } else if slot == 1 {
        v1
    } else if slot == 2 {
        v2
    } else {
        v3
    }
}

#[inline(always)]
fn inv_child_slot(st: u8, leaves: i64, cum: i64, pend: i64, worst: i64) -> bool {
    if st > C_REJECTED || (leaves | cum | pend | worst) < 0 || worst < leaves {
        return false;
    }
    if st == C_EMPTY {
        leaves == 0 && cum == 0 && pend == 0 && worst == 0
    } else if st == C_PENDING_NEW {
        leaves > 0 && cum == 0 && pend == 0 && worst == leaves
    } else if st == C_LIVE || st == C_PENDING_CANCEL {
        leaves > 0 && pend == 0 && worst == leaves
    } else if st == C_PENDING_REPLACE {
        leaves > 0 && worst >= pend && worst == max_i64(leaves, pend) && (pend > 0 || cum > 0)
    } else if st == C_FILLED {
        cum > 0 && leaves == 0 && pend == 0 && worst == 0
    } else if st == C_CANCELED {
        leaves == 0 && pend == 0 && worst == 0
    } else {
        cum == 0 && leaves == 0 && pend == 0 && worst == 0
    }
}

#[inline(never)]
fn route_child_at<const S: usize>(qty: i64) -> i32 {
    if C_STATE[S].load(Ordering::Relaxed) != C_EMPTY {
        return 0;
    }
    let target = P_TARGET_QTY.load(Ordering::Relaxed);
    let p_cum = P_CUM_FILLED.load(Ordering::Relaxed);
    let new_open = recompute_open_worst_with::<S>(qty);
    if target <= 0 || (p_cum | new_open) < 0 || p_cum > target || new_open > target.wrapping_sub(p_cum)
    {
        return 0;
    }
    C_STATE[S].store(C_PENDING_NEW, Ordering::Relaxed);
    C_LEAVES[S].store(qty, Ordering::Relaxed);
    C_WORST[S].store(qty, Ordering::Relaxed);
    P_OPEN_WORST.store(new_open, Ordering::Relaxed);
    1
}

#[inline(never)]
fn on_child_ack_at<const S: usize>() -> i32 {
    if C_STATE[S].load(Ordering::Relaxed) != C_PENDING_NEW {
        return 0;
    }
    C_STATE[S].store(C_LIVE, Ordering::Relaxed);
    1
}

#[inline(never)]
fn request_child_replace_at<const S: usize>(new_leaves: i64) -> i32 {
    if C_STATE[S].load(Ordering::Relaxed) != C_LIVE {
        return 0;
    }
    let old_leaves = C_LEAVES[S].load(Ordering::Relaxed);
    let new_worst = max_i64(new_leaves, old_leaves);
    let target = P_TARGET_QTY.load(Ordering::Relaxed);
    let p_cum = P_CUM_FILLED.load(Ordering::Relaxed);
    let new_open = recompute_open_worst_with::<S>(new_worst);
    if target <= 0 || (p_cum | new_open) < 0 || p_cum > target || new_open > target.wrapping_sub(p_cum)
    {
        return 0;
    }
    C_STATE[S].store(C_PENDING_REPLACE, Ordering::Relaxed);
    C_PENDING[S].store(new_leaves, Ordering::Relaxed);
    C_WORST[S].store(new_worst, Ordering::Relaxed);
    P_OPEN_WORST.store(new_open, Ordering::Relaxed);
    1
}

#[inline(never)]
fn on_child_fill_at<const S: usize>(fill_qty: i64) -> i32 {
    let st = C_STATE[S].load(Ordering::Relaxed);
    if st != C_LIVE && st != C_PENDING_CANCEL && st != C_PENDING_REPLACE {
        return 0;
    }
    let old_leaves = C_LEAVES[S].load(Ordering::Relaxed);
    if fill_qty <= 0 || fill_qty > old_leaves {
        return 0;
    }
    let old_cum = C_CUM[S].load(Ordering::Relaxed);
    if fill_qty > i64::MAX.wrapping_sub(old_cum) {
        return 0;
    }
    let new_leaves = old_leaves.wrapping_sub(fill_qty);
    let new_cum = old_cum.wrapping_add(fill_qty);

    let (new_state, new_pending, new_worst) = if new_leaves == 0 {
        (C_FILLED, 0, 0)
    } else if st == C_PENDING_REPLACE {
        let old_pend = C_PENDING[S].load(Ordering::Relaxed);
        let next_pend = if old_pend > fill_qty {
            old_pend.wrapping_sub(fill_qty)
        } else {
            0
        };
        (C_PENDING_REPLACE, next_pend, max_i64(new_leaves, next_pend))
    } else {
        (st, 0, new_leaves)
    };

    let p_target = P_TARGET_QTY.load(Ordering::Relaxed);
    let new_p_cum = recompute_cum_filled_with::<S>(new_cum);
    let new_p_open = recompute_open_worst_with::<S>(new_worst);
    if (new_p_cum | new_p_open) < 0
        || new_p_cum > p_target
        || new_p_open > p_target.wrapping_sub(new_p_cum)
    {
        return 0;
    }

    C_STATE[S].store(new_state, Ordering::Relaxed);
    C_LEAVES[S].store(new_leaves, Ordering::Relaxed);
    C_CUM[S].store(new_cum, Ordering::Relaxed);
    C_PENDING[S].store(new_pending, Ordering::Relaxed);
    C_WORST[S].store(new_worst, Ordering::Relaxed);
    P_CUM_FILLED.store(new_p_cum, Ordering::Relaxed);
    P_OPEN_WORST.store(new_p_open, Ordering::Relaxed);

    if new_p_cum == p_target && new_p_open == 0 {
        P_STATUS.store(P_COMPLETE, Ordering::Relaxed);
    }
    1
}

#[inline(never)]
fn request_child_cancel_buggy_at<const S: usize>() -> i32 {
    if C_STATE[S].load(Ordering::Relaxed) != C_LIVE {
        return 0;
    }
    let new_open = recompute_open_worst_with::<S>(0);
    C_STATE[S].store(C_PENDING_CANCEL, Ordering::Relaxed);
    // BUG: prematurely frees worst-case exposure before exchange confirms cancel!
    C_WORST[S].store(0, Ordering::Relaxed);
    P_OPEN_WORST.store(new_open, Ordering::Relaxed);
    1
}

/// Baseline `init_parent`.
#[unsafe(no_mangle)]
pub extern "C" fn init_parent(target_qty: i64) -> i32 {
    if target_qty <= 0 {
        return 0;
    }
    P_ACTIVE.store(1, Ordering::Relaxed);
    P_STATUS.store(P_WORKING, Ordering::Relaxed);
    P_TARGET_QTY.store(target_qty, Ordering::Relaxed);
    P_CUM_FILLED.store(0, Ordering::Relaxed);
    P_OPEN_WORST.store(0, Ordering::Relaxed);

    let mut i = 0;
    while i < 4 {
        C_STATE[i].store(C_EMPTY, Ordering::Relaxed);
        C_LEAVES[i].store(0, Ordering::Relaxed);
        C_CUM[i].store(0, Ordering::Relaxed);
        C_PENDING[i].store(0, Ordering::Relaxed);
        C_WORST[i].store(0, Ordering::Relaxed);
        i += 1;
    }
    1
}

/// Baseline `route_child`.
#[unsafe(no_mangle)]
pub extern "C" fn route_child(slot: i32, qty: i64) -> i32 {
    if P_ACTIVE.load(Ordering::Relaxed) != 1
        || P_STATUS.load(Ordering::Relaxed) != P_WORKING
        || qty <= 0
    {
        return 0;
    }
    if slot == 0 {
        route_child_at::<0>(qty)
    } else if slot == 1 {
        route_child_at::<1>(qty)
    } else if slot == 2 {
        route_child_at::<2>(qty)
    } else if slot == 3 {
        route_child_at::<3>(qty)
    } else {
        0
    }
}

/// Baseline `on_child_ack`.
#[unsafe(no_mangle)]
pub extern "C" fn on_child_ack(slot: i32) -> i32 {
    if P_ACTIVE.load(Ordering::Relaxed) != 1 {
        return 0;
    }
    if slot == 0 {
        on_child_ack_at::<0>()
    } else if slot == 1 {
        on_child_ack_at::<1>()
    } else if slot == 2 {
        on_child_ack_at::<2>()
    } else if slot == 3 {
        on_child_ack_at::<3>()
    } else {
        0
    }
}

/// Baseline `request_child_replace`.
#[unsafe(no_mangle)]
pub extern "C" fn request_child_replace(slot: i32, new_leaves: i64) -> i32 {
    if P_ACTIVE.load(Ordering::Relaxed) != 1 || new_leaves <= 0 {
        return 0;
    }
    if slot == 0 {
        request_child_replace_at::<0>(new_leaves)
    } else if slot == 1 {
        request_child_replace_at::<1>(new_leaves)
    } else if slot == 2 {
        request_child_replace_at::<2>(new_leaves)
    } else if slot == 3 {
        request_child_replace_at::<3>(new_leaves)
    } else {
        0
    }
}

/// Baseline `on_child_fill`.
#[unsafe(no_mangle)]
pub extern "C" fn on_child_fill(slot: i32, fill_qty: i64) -> i32 {
    if P_ACTIVE.load(Ordering::Relaxed) != 1 {
        return 0;
    }
    if slot == 0 {
        on_child_fill_at::<0>(fill_qty)
    } else if slot == 1 {
        on_child_fill_at::<1>(fill_qty)
    } else if slot == 2 {
        on_child_fill_at::<2>(fill_qty)
    } else if slot == 3 {
        on_child_fill_at::<3>(fill_qty)
    } else {
        0
    }
}

/// MUTANT (classic $10M+ SOR in-flight over-fill bug):
/// Optimistically releases `c_worst[slot]` from `p_open_worst` on `request_child_cancel`
/// BEFORE `CancelAck` arrives from the exchange. If a new child is immediately routed into
/// another venue slot while the canceling child gets filled in flight, total fills exceed `p_target_qty`!
#[unsafe(no_mangle)]
pub extern "C" fn request_child_cancel_buggy_optimistic(slot: i32) -> i32 {
    if P_ACTIVE.load(Ordering::Relaxed) != 1 {
        return 0;
    }
    if slot == 0 {
        request_child_cancel_buggy_at::<0>()
    } else if slot == 1 {
        request_child_cancel_buggy_at::<1>()
    } else if slot == 2 {
        request_child_cancel_buggy_at::<2>()
    } else if slot == 3 {
        request_child_cancel_buggy_at::<3>()
    } else {
        0
    }
}

/// Same inductive invariant `inv_parent_child_oms()` as `s3_2_parent_child_oms.rs`.
#[unsafe(no_mangle)]
pub extern "C" fn inv_parent_child_oms() -> i32 {
    let active = P_ACTIVE.load(Ordering::Relaxed);
    let status = P_STATUS.load(Ordering::Relaxed);
    let target = P_TARGET_QTY.load(Ordering::Relaxed);
    let p_cum = P_CUM_FILLED.load(Ordering::Relaxed);
    let p_open = P_OPEN_WORST.load(Ordering::Relaxed);

    let s0 = C_STATE[0].load(Ordering::Relaxed);
    let s1 = C_STATE[1].load(Ordering::Relaxed);
    let s2 = C_STATE[2].load(Ordering::Relaxed);
    let s3 = C_STATE[3].load(Ordering::Relaxed);

    let l0 = C_LEAVES[0].load(Ordering::Relaxed);
    let l1 = C_LEAVES[1].load(Ordering::Relaxed);
    let l2 = C_LEAVES[2].load(Ordering::Relaxed);
    let l3 = C_LEAVES[3].load(Ordering::Relaxed);

    let u0 = C_CUM[0].load(Ordering::Relaxed);
    let u1 = C_CUM[1].load(Ordering::Relaxed);
    let u2 = C_CUM[2].load(Ordering::Relaxed);
    let u3 = C_CUM[3].load(Ordering::Relaxed);

    let d0 = C_PENDING[0].load(Ordering::Relaxed);
    let d1 = C_PENDING[1].load(Ordering::Relaxed);
    let d2 = C_PENDING[2].load(Ordering::Relaxed);
    let d3 = C_PENDING[3].load(Ordering::Relaxed);

    let w0 = C_WORST[0].load(Ordering::Relaxed);
    let w1 = C_WORST[1].load(Ordering::Relaxed);
    let w2 = C_WORST[2].load(Ordering::Relaxed);
    let w3 = C_WORST[3].load(Ordering::Relaxed);

    if active == 0 {
        if (status | s0 | s1 | s2 | s3) == 0
            && (target | p_cum | p_open | l0 | l1 | l2 | l3 | u0 | u1 | u2 | u3 | d0 | d1 | d2 | d3
                | w0 | w1 | w2 | w3)
                == 0
        {
            return 1;
        }
        return 0;
    }

    if active != 1 || target <= 0 || (p_cum | p_open) < 0 {
        return 0;
    }
    if p_cum > target || p_open > target.wrapping_sub(p_cum) {
        return 0;
    }
    if status == P_WORKING {
        if p_cum >= target {
            return 0;
        }
    } else if status == P_COMPLETE {
        if p_cum != target || p_open != 0 {
            return 0;
        }
    } else {
        return 0;
    }

    if !inv_child_slot(s0, l0, u0, d0, w0)
        || !inv_child_slot(s1, l1, u1, d1, w1)
        || !inv_child_slot(s2, l2, u2, d2, w2)
        || !inv_child_slot(s3, l3, u3, d3, w3)
    {
        return 0;
    }
    if !sum4_eq(u0, u1, u2, u3, p_cum) || !sum4_eq(w0, w1, w2, w3, p_open) {
        return 0;
    }
    1
}

/// Contract harness exposing the optimistic-cancel SOR over-fill bug.
/// Expected result: FALSIFIED (both `inv_parent_child_oms()` and live exposure
/// `p_cum_filled + c_leaves[slot_cancel] + c_leaves[slot_new] <= p_target_qty` are violated).
#[unsafe(no_mangle)]
pub extern "C" fn contract_no_inflight_overfill_buggy(
    slot_cancel: i32,
    slot_new: i32,
    new_qty: i64,
) -> i32 {
    assume(inv_parent_child_oms() != 0);
    assume(P_ACTIVE.load(Ordering::Relaxed) == 1);
    assume(slot_cancel >= 0 && slot_cancel < 4);
    assume(slot_new >= 0 && slot_new < 4);
    assume(slot_cancel != slot_new);
    assume(load_c_state(slot_cancel) == C_LIVE);
    assume(load_c_state(slot_new) == C_EMPTY);
    assume(new_qty > 0);

    let cancel_ok = request_child_cancel_buggy_optimistic(slot_cancel);
    assert_prop(cancel_ok == 1);
    let _route_ok = route_child(slot_new, new_qty);

    let target = P_TARGET_QTY.load(Ordering::Relaxed);
    let cum = P_CUM_FILLED.load(Ordering::Relaxed);
    let open = P_OPEN_WORST.load(Ordering::Relaxed);
    let l_cancel = load_c_leaves(slot_cancel);
    let l_new = load_c_leaves(slot_new);

    assert_prop(l_cancel <= target.wrapping_sub(cum));
    assert_prop(l_new <= target.wrapping_sub(cum).wrapping_sub(l_cancel));
    assert_prop(cum <= target && open <= target.wrapping_sub(cum));
    assert_prop(inv_parent_child_oms() != 0);
    1
}
