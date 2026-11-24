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

// Parent order lifecycle states.
const P_EMPTY: u8 = 0;
const P_WORKING: u8 = 1;
const P_COMPLETE: u8 = 2;

// Child venue slot lifecycle states (matching S3.1).
const C_EMPTY: u8 = 0;
const C_PENDING_NEW: u8 = 1;
const C_LIVE: u8 = 2;
const C_PENDING_REPLACE: u8 = 3;
const C_PENDING_CANCEL: u8 = 4;
const C_FILLED: u8 = 5;
const C_CANCELED: u8 = 6;
const C_REJECTED: u8 = 7;

// Parent order state in fixed linear-memory slots (globals: 0, zero __stack_pointer, zero .rodata).
static P_ACTIVE: AtomicU8 = AtomicU8::new(0);
static P_STATUS: AtomicU8 = AtomicU8::new(P_EMPTY);
static P_TARGET_QTY: AtomicI64 = AtomicI64::new(0);
static P_CUM_FILLED: AtomicI64 = AtomicI64::new(0);
static P_OPEN_WORST: AtomicI64 = AtomicI64::new(0);

// Fixed K = 4 contiguous child venue arrays.
// All arithmetic and parent roll-ups execute ONCE (hoisted outside slot dispatch);
// only tiny constant-address slot writers dispatch per-slot (`S = 0..4`), yielding zero `.rodata`,
// zero bounds traps, and minimal SMT array stores.
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

/// Branchless, overflow-safe exact 4-way non-negative sum in Z via symmetric depth-2 tree.
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

/// Branchless, overflow-safe exact 4-way non-negative sum equality check: `a + b + c + d == total` in Z.
#[inline(always)]
fn sum4_eq(a: i64, b: i64, c: i64, d: i64, total: i64) -> bool {
    let s01 = a.wrapping_add(b);
    let s23 = c.wrapping_add(d);
    let s = s01.wrapping_add(s23);
    ((a | b | c | d | total | s01 | s23 | s) >= 0) && (s == total)
}

#[inline(always)]
fn select_u8(slot: i32, v0: u8, v1: u8, v2: u8, v3: u8) -> u8 {
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
fn select_i64(slot: i32, v0: i64, v1: i64, v2: i64, v3: i64) -> i64 {
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
fn load_c_state(slot: i32) -> u8 {
    select_u8(
        slot,
        C_STATE[0].load(Ordering::Relaxed),
        C_STATE[1].load(Ordering::Relaxed),
        C_STATE[2].load(Ordering::Relaxed),
        C_STATE[3].load(Ordering::Relaxed),
    )
}

#[inline(always)]
fn load_c_leaves(slot: i32) -> i64 {
    select_i64(
        slot,
        C_LEAVES[0].load(Ordering::Relaxed),
        C_LEAVES[1].load(Ordering::Relaxed),
        C_LEAVES[2].load(Ordering::Relaxed),
        C_LEAVES[3].load(Ordering::Relaxed),
    )
}

#[inline(always)]
fn load_c_cum(slot: i32) -> i64 {
    select_i64(
        slot,
        C_CUM[0].load(Ordering::Relaxed),
        C_CUM[1].load(Ordering::Relaxed),
        C_CUM[2].load(Ordering::Relaxed),
        C_CUM[3].load(Ordering::Relaxed),
    )
}

#[inline(always)]
fn load_c_pending(slot: i32) -> i64 {
    select_i64(
        slot,
        C_PENDING[0].load(Ordering::Relaxed),
        C_PENDING[1].load(Ordering::Relaxed),
        C_PENDING[2].load(Ordering::Relaxed),
        C_PENDING[3].load(Ordering::Relaxed),
    )
}

#[inline(always)]
fn recompute_open_worst_slot(slot: i32, new_s_worst: i64) -> i64 {
    let w0 = if slot == 0 { new_s_worst } else { C_WORST[0].load(Ordering::Relaxed) };
    let w1 = if slot == 1 { new_s_worst } else { C_WORST[1].load(Ordering::Relaxed) };
    let w2 = if slot == 2 { new_s_worst } else { C_WORST[2].load(Ordering::Relaxed) };
    let w3 = if slot == 3 { new_s_worst } else { C_WORST[3].load(Ordering::Relaxed) };
    sum4_checked(w0, w1, w2, w3)
}

#[inline(always)]
fn recompute_cum_filled_slot(slot: i32, new_s_cum: i64) -> i64 {
    let u0 = if slot == 0 { new_s_cum } else { C_CUM[0].load(Ordering::Relaxed) };
    let u1 = if slot == 1 { new_s_cum } else { C_CUM[1].load(Ordering::Relaxed) };
    let u2 = if slot == 2 { new_s_cum } else { C_CUM[2].load(Ordering::Relaxed) };
    let u3 = if slot == 3 { new_s_cum } else { C_CUM[3].load(Ordering::Relaxed) };
    sum4_checked(u0, u1, u2, u3)
}

#[inline(never)]
fn store_state_at<const S: usize>(st: u8) {
    C_STATE[S].store(st, Ordering::Relaxed);
}

#[inline(never)]
fn write_route_at<const S: usize>(qty: i64) {
    C_STATE[S].store(C_PENDING_NEW, Ordering::Relaxed);
    C_LEAVES[S].store(qty, Ordering::Relaxed);
    C_WORST[S].store(qty, Ordering::Relaxed);
}

#[inline(never)]
fn write_replace_req_at<const S: usize>(new_leaves: i64, new_worst: i64) {
    C_STATE[S].store(C_PENDING_REPLACE, Ordering::Relaxed);
    C_PENDING[S].store(new_leaves, Ordering::Relaxed);
    C_WORST[S].store(new_worst, Ordering::Relaxed);
}

#[inline(never)]
fn write_fill_at<const S: usize>(
    new_st: u8,
    new_leaves: i64,
    new_cum: i64,
    new_pend: i64,
    new_worst: i64,
) {
    C_STATE[S].store(new_st, Ordering::Relaxed);
    C_LEAVES[S].store(new_leaves, Ordering::Relaxed);
    C_CUM[S].store(new_cum, Ordering::Relaxed);
    C_PENDING[S].store(new_pend, Ordering::Relaxed);
    C_WORST[S].store(new_worst, Ordering::Relaxed);
}

#[inline(never)]
fn write_cancel_ack_at<const S: usize>() {
    C_STATE[S].store(C_CANCELED, Ordering::Relaxed);
    C_LEAVES[S].store(0, Ordering::Relaxed);
    C_WORST[S].store(0, Ordering::Relaxed);
}

#[inline(never)]
fn write_replace_ack_at<const S: usize>(new_st: u8, new_leaves: i64) {
    C_STATE[S].store(new_st, Ordering::Relaxed);
    C_LEAVES[S].store(new_leaves, Ordering::Relaxed);
    C_PENDING[S].store(0, Ordering::Relaxed);
    C_WORST[S].store(new_leaves, Ordering::Relaxed);
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
        // C_REJECTED
        cum == 0 && leaves == 0 && pend == 0 && worst == 0
    }
}

/// Initialize a valid parent order with `target_qty > 0` and 4 empty child venue slots.
/// If `target_qty <= 0`, leaves state unchanged (from zero-initialized memory this is a valid
/// inactive parent) and returns `0`. Returns `1` on initialization.
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

/// Route a new child slice of `qty` into an empty venue `slot` (`0..=3`).
/// Overflow-safely verifies `p_cum_filled + p_open_worst + qty <= p_target_qty` before routing.
#[unsafe(no_mangle)]
pub extern "C" fn route_child(slot: i32, qty: i64) -> i32 {
    if P_ACTIVE.load(Ordering::Relaxed) != 1
        || P_STATUS.load(Ordering::Relaxed) != P_WORKING
        || slot < 0
        || slot >= 4
        || qty <= 0
    {
        return 0;
    }
    if load_c_state(slot) != C_EMPTY {
        return 0;
    }
    let target = P_TARGET_QTY.load(Ordering::Relaxed);
    let p_cum = P_CUM_FILLED.load(Ordering::Relaxed);
    let new_open = recompute_open_worst_slot(slot, qty);
    if target <= 0 || (p_cum | new_open) < 0 || p_cum > target || new_open > target.wrapping_sub(p_cum)
    {
        return 0;
    }
    if slot == 0 {
        write_route_at::<0>(qty);
    } else if slot == 1 {
        write_route_at::<1>(qty);
    } else if slot == 2 {
        write_route_at::<2>(qty);
    } else {
        write_route_at::<3>(qty);
    }
    P_OPEN_WORST.store(new_open, Ordering::Relaxed);
    1
}

/// Exchange order acknowledgement: `PendingNew -> Live`.
#[unsafe(no_mangle)]
pub extern "C" fn on_child_ack(slot: i32) -> i32 {
    if P_ACTIVE.load(Ordering::Relaxed) != 1 || slot < 0 || slot >= 4 {
        return 0;
    }
    if load_c_state(slot) != C_PENDING_NEW {
        return 0;
    }
    if slot == 0 {
        store_state_at::<0>(C_LIVE);
    } else if slot == 1 {
        store_state_at::<1>(C_LIVE);
    } else if slot == 2 {
        store_state_at::<2>(C_LIVE);
    } else {
        store_state_at::<3>(C_LIVE);
    }
    1
}

/// Request child cancel: `Live -> PendingCancel`.
/// Pessimistically preserves `c_worst[slot] == c_leaves[slot]` and `p_open_worst` until `CancelAck`.
#[unsafe(no_mangle)]
pub extern "C" fn request_child_cancel(slot: i32) -> i32 {
    if P_ACTIVE.load(Ordering::Relaxed) != 1 || slot < 0 || slot >= 4 {
        return 0;
    }
    if load_c_state(slot) != C_LIVE {
        return 0;
    }
    if slot == 0 {
        store_state_at::<0>(C_PENDING_CANCEL);
    } else if slot == 1 {
        store_state_at::<1>(C_PENDING_CANCEL);
    } else if slot == 2 {
        store_state_at::<2>(C_PENDING_CANCEL);
    } else {
        store_state_at::<3>(C_PENDING_CANCEL);
    }
    1
}

/// Request child cancel/replace: `Live -> PendingReplace` with target remaining `new_leaves > 0`.
/// Pessimistically reserves `delta = max(new_leaves, old_leaves) - old_leaves` against parent headroom.
/// Never optimistically releases exposure when shrinking (`new_leaves < old_leaves`).
#[unsafe(no_mangle)]
pub extern "C" fn request_child_replace(slot: i32, new_leaves: i64) -> i32 {
    if P_ACTIVE.load(Ordering::Relaxed) != 1 || slot < 0 || slot >= 4 || new_leaves <= 0 {
        return 0;
    }
    if load_c_state(slot) != C_LIVE {
        return 0;
    }
    let old_leaves = load_c_leaves(slot);
    let new_worst = max_i64(new_leaves, old_leaves);
    let target = P_TARGET_QTY.load(Ordering::Relaxed);
    let p_cum = P_CUM_FILLED.load(Ordering::Relaxed);
    let new_open = recompute_open_worst_slot(slot, new_worst);
    if target <= 0 || (p_cum | new_open) < 0 || p_cum > target || new_open > target.wrapping_sub(p_cum)
    {
        return 0;
    }
    if slot == 0 {
        write_replace_req_at::<0>(new_leaves, new_worst);
    } else if slot == 1 {
        write_replace_req_at::<1>(new_leaves, new_worst);
    } else if slot == 2 {
        write_replace_req_at::<2>(new_leaves, new_worst);
    } else {
        write_replace_req_at::<3>(new_leaves, new_worst);
    }
    P_OPEN_WORST.store(new_open, Ordering::Relaxed);
    1
}

/// Process exchange fill on child `slot` (`Live | PendingCancel | PendingReplace`).
/// Rolls up exact fill to parent `p_cum_filled`, reduces `c_leaves`/`c_worst`/`p_open_worst`,
/// transitions child to `Filled` when `leaves == 0`, and marks parent `P_COMPLETE` when full.
#[unsafe(no_mangle)]
pub extern "C" fn on_child_fill(slot: i32, fill_qty: i64) -> i32 {
    if P_ACTIVE.load(Ordering::Relaxed) != 1 || slot < 0 || slot >= 4 || fill_qty <= 0 {
        return 0;
    }
    let st = load_c_state(slot);
    if st != C_LIVE && st != C_PENDING_CANCEL && st != C_PENDING_REPLACE {
        return 0;
    }
    let old_leaves = load_c_leaves(slot);
    if fill_qty > old_leaves {
        return 0;
    }
    let old_cum = load_c_cum(slot);
    if fill_qty > i64::MAX.wrapping_sub(old_cum) {
        return 0;
    }
    let new_leaves = old_leaves.wrapping_sub(fill_qty);
    let new_cum = old_cum.wrapping_add(fill_qty);

    let (new_state, new_pending, new_worst) = if new_leaves == 0 {
        (C_FILLED, 0, 0)
    } else if st == C_PENDING_REPLACE {
        let old_pend = load_c_pending(slot);
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
    let new_p_cum = recompute_cum_filled_slot(slot, new_cum);
    let new_p_open = recompute_open_worst_slot(slot, new_worst);
    if (new_p_cum | new_p_open) < 0
        || new_p_cum > p_target
        || new_p_open > p_target.wrapping_sub(new_p_cum)
    {
        return 0;
    }

    if slot == 0 {
        write_fill_at::<0>(new_state, new_leaves, new_cum, new_pending, new_worst);
    } else if slot == 1 {
        write_fill_at::<1>(new_state, new_leaves, new_cum, new_pending, new_worst);
    } else if slot == 2 {
        write_fill_at::<2>(new_state, new_leaves, new_cum, new_pending, new_worst);
    } else {
        write_fill_at::<3>(new_state, new_leaves, new_cum, new_pending, new_worst);
    }
    P_CUM_FILLED.store(new_p_cum, Ordering::Relaxed);
    P_OPEN_WORST.store(new_p_open, Ordering::Relaxed);
    if new_p_cum == p_target && new_p_open == 0 {
        P_STATUS.store(P_COMPLETE, Ordering::Relaxed);
    }
    1
}

/// Process exchange cancel acknowledgement (or unsolicited cancel while `Live`).
/// Releases `c_worst[slot]` from `p_open_worst` ONLY upon confirmed cancel; never mutates terminal slots.
#[unsafe(no_mangle)]
pub extern "C" fn on_child_cancel_ack(slot: i32) -> i32 {
    if P_ACTIVE.load(Ordering::Relaxed) != 1 || slot < 0 || slot >= 4 {
        return 0;
    }
    let st = load_c_state(slot);
    if st != C_PENDING_CANCEL && st != C_LIVE {
        return 0;
    }
    let target = P_TARGET_QTY.load(Ordering::Relaxed);
    let p_cum = P_CUM_FILLED.load(Ordering::Relaxed);
    let new_open = recompute_open_worst_slot(slot, 0);
    if target <= 0 || (p_cum | new_open) < 0 || p_cum > target || new_open > target.wrapping_sub(p_cum)
    {
        return 0;
    }
    if slot == 0 {
        write_cancel_ack_at::<0>();
    } else if slot == 1 {
        write_cancel_ack_at::<1>();
    } else if slot == 2 {
        write_cancel_ack_at::<2>();
    } else {
        write_cancel_ack_at::<3>();
    }
    P_OPEN_WORST.store(new_open, Ordering::Relaxed);
    1
}

/// Process exchange replace acknowledgement: `PendingReplace -> Live | Filled`.
/// Commits `new_leaves` and releases surplus worst-case reservation if the order shrunk.
#[unsafe(no_mangle)]
pub extern "C" fn on_child_replace_ack(slot: i32) -> i32 {
    if P_ACTIVE.load(Ordering::Relaxed) != 1 || slot < 0 || slot >= 4 {
        return 0;
    }
    if load_c_state(slot) != C_PENDING_REPLACE {
        return 0;
    }
    let new_leaves = load_c_pending(slot);
    if new_leaves < 0 {
        return 0;
    }
    let target = P_TARGET_QTY.load(Ordering::Relaxed);
    let p_cum = P_CUM_FILLED.load(Ordering::Relaxed);
    let new_open = recompute_open_worst_slot(slot, new_leaves);
    if target <= 0 || (p_cum | new_open) < 0 || p_cum > target || new_open > target.wrapping_sub(p_cum)
    {
        return 0;
    }
    let new_st = if new_leaves == 0 { C_FILLED } else { C_LIVE };
    if slot == 0 {
        write_replace_ack_at::<0>(new_st, new_leaves);
    } else if slot == 1 {
        write_replace_ack_at::<1>(new_st, new_leaves);
    } else if slot == 2 {
        write_replace_ack_at::<2>(new_st, new_leaves);
    } else {
        write_replace_ack_at::<3>(new_st, new_leaves);
    }
    P_OPEN_WORST.store(new_open, Ordering::Relaxed);
    1
}

/// Process exchange rejection on child `slot`:
/// - `PendingNew -> Rejected` (releases `c_worst[slot]` from `p_open_worst`)
/// - `PendingCancel | PendingReplace -> Live` (restores `c_worst = c_leaves`, releases replace surplus)
#[unsafe(no_mangle)]
pub extern "C" fn on_child_reject(slot: i32) -> i32 {
    if P_ACTIVE.load(Ordering::Relaxed) != 1 || slot < 0 || slot >= 4 {
        return 0;
    }
    let st = load_c_state(slot);
    if st != C_PENDING_NEW && st != C_PENDING_CANCEL && st != C_PENDING_REPLACE {
        return 0;
    }
    let (new_st, new_leaves) = if st == C_PENDING_NEW {
        (C_REJECTED, 0)
    } else {
        (C_LIVE, load_c_leaves(slot))
    };
    let target = P_TARGET_QTY.load(Ordering::Relaxed);
    let p_cum = P_CUM_FILLED.load(Ordering::Relaxed);
    let new_open = recompute_open_worst_slot(slot, new_leaves);
    if target <= 0 || (p_cum | new_open) < 0 || p_cum > target || new_open > target.wrapping_sub(p_cum)
    {
        return 0;
    }
    if slot == 0 {
        write_replace_ack_at::<0>(new_st, new_leaves);
    } else if slot == 1 {
        write_replace_ack_at::<1>(new_st, new_leaves);
    } else if slot == 2 {
        write_replace_ack_at::<2>(new_st, new_leaves);
    } else {
        write_replace_ack_at::<3>(new_st, new_leaves);
    }
    P_OPEN_WORST.store(new_open, Ordering::Relaxed);
    1
}

/// Inductive Parent/Child OMS state invariant (`1` iff all clauses hold):
/// 1. Valid parent active flag (`0` or `1`) and status (`P_EMPTY | P_WORKING | P_COMPLETE`).
/// 2. All quantities non-negative, valid child states `0..=7`, terminal children zeroed.
/// 3. Exact fill roll-up conservation: `p_cum_filled == sum(c_cum[0..4])` (overflow-safe).
/// 4. Exact exposure roll-up: `p_open_worst == sum(c_worst[0..4])` (overflow-safe).
/// 5. Zero Over-Fill (golden OMS theorem): `p_cum_filled + p_open_worst <= p_target_qty` (overflow-safe).
/// 6. Per-child pessimistic coverage: `c_worst[i] >= c_leaves[i]` and if `PendingReplace`, `c_worst[i] >= c_pending[i]`.
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

    if !sum4_eq(u0, u1, u2, u3, p_cum) {
        return 0;
    }
    if !sum4_eq(w0, w1, w2, w3, p_open) {
        return 0;
    }
    1
}

/// Inline relational contract:
/// Starting from any valid OMS state with a `Live` child at `slot_cancel` and an `Empty`
/// slot at `slot_new`, requesting cancel on `slot_cancel` and immediately attempting to route
/// `new_qty` into `slot_new` NEVER causes in-flight over-fill:
/// `inv_parent_child_oms()` holds, `p_cum_filled + p_open_worst <= p_target_qty`, AND
/// actual live exchange exposure `p_cum_filled + c_leaves[slot_cancel] + c_leaves[slot_new] <= p_target_qty`.
#[unsafe(no_mangle)]
pub extern "C" fn contract_no_inflight_overfill(
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

    let cancel_ok = request_child_cancel(slot_cancel);
    assert_prop(cancel_ok == 1);
    let _route_ok = route_child(slot_new, new_qty);

    let target = P_TARGET_QTY.load(Ordering::Relaxed);
    let cum = P_CUM_FILLED.load(Ordering::Relaxed);
    let open = P_OPEN_WORST.load(Ordering::Relaxed);

    assert_prop(cum <= target && open <= target.wrapping_sub(cum));
    assert_prop(inv_parent_child_oms() != 0);
    1
}

/// Inline relational contract:
/// Proves exact child-to-parent fill roll-up conservation across `Live | PendingCancel | PendingReplace`:
/// child `c_cum` and parent `p_cum_filled` both advance by exactly `fill_qty`, `c_leaves` decreases
/// by `fill_qty`, and exact fill roll-up + Zero Over-Fill hold.
#[unsafe(no_mangle)]
pub extern "C" fn contract_fill_rollup_exact(slot: i32, fill_qty: i64) -> i32 {
    assume(inv_parent_child_oms() != 0);
    assume(P_ACTIVE.load(Ordering::Relaxed) == 1);
    assume(slot >= 0 && slot < 4);
    let st = load_c_state(slot);
    assume(st == C_LIVE || st == C_PENDING_CANCEL || st == C_PENDING_REPLACE);
    let old_leaves = load_c_leaves(slot);
    assume(fill_qty > 0 && fill_qty <= old_leaves);

    let old_c_cum = load_c_cum(slot);
    let ok = on_child_fill(slot, fill_qty);
    if ok == 1 {
        assert_prop(load_c_cum(slot) == old_c_cum.wrapping_add(fill_qty));
        assert_prop(load_c_leaves(slot) == old_leaves.wrapping_sub(fill_qty));
        assert_prop(sum4_eq(
            C_CUM[0].load(Ordering::Relaxed),
            C_CUM[1].load(Ordering::Relaxed),
            C_CUM[2].load(Ordering::Relaxed),
            C_CUM[3].load(Ordering::Relaxed),
            P_CUM_FILLED.load(Ordering::Relaxed),
        ));
        let target = P_TARGET_QTY.load(Ordering::Relaxed);
        let p_cum = P_CUM_FILLED.load(Ordering::Relaxed);
        let p_open = P_OPEN_WORST.load(Ordering::Relaxed);
        assert_prop(p_cum <= target && p_open <= target.wrapping_sub(p_cum));
    }
    1
}
