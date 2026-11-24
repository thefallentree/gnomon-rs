#![no_std]

use core::sync::atomic::{AtomicI32, AtomicI64, Ordering};

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

const STATE_EMPTY: i32 = 0;
const STATE_PENDING_NEW: i32 = 1;
const STATE_LIVE: i32 = 2;
const STATE_PENDING_REPLACE: i32 = 3;
const STATE_PENDING_CANCEL: i32 = 4;
const STATE_FILLED: i32 = 5;
const STATE_CANCELED: i32 = 6;
const STATE_REJECTED: i32 = 7;

static STATE: AtomicI32 = AtomicI32::new(STATE_EMPTY);
static ORIG_QTY: AtomicI64 = AtomicI64::new(0);
static LEAVES_QTY: AtomicI64 = AtomicI64::new(0);
static CUM_FILLED: AtomicI64 = AtomicI64::new(0);
static PENDING_QTY: AtomicI64 = AtomicI64::new(0);
static WORST_CASE_LEAVES: AtomicI64 = AtomicI64::new(0);

#[inline(always)]
fn load_state() -> i32 {
    STATE.load(Ordering::Relaxed)
}

#[inline(always)]
fn store_state(v: i32) {
    STATE.store(v, Ordering::Relaxed);
}

#[inline(always)]
fn load_orig_qty() -> i64 {
    ORIG_QTY.load(Ordering::Relaxed)
}

#[inline(always)]
fn store_orig_qty(v: i64) {
    ORIG_QTY.store(v, Ordering::Relaxed);
}

#[inline(always)]
fn load_leaves_qty() -> i64 {
    LEAVES_QTY.load(Ordering::Relaxed)
}

#[inline(always)]
fn store_leaves_qty(v: i64) {
    LEAVES_QTY.store(v, Ordering::Relaxed);
}

#[inline(always)]
fn load_cum_filled() -> i64 {
    CUM_FILLED.load(Ordering::Relaxed)
}

#[inline(always)]
fn store_cum_filled(v: i64) {
    CUM_FILLED.store(v, Ordering::Relaxed);
}

#[inline(always)]
fn load_pending_qty() -> i64 {
    PENDING_QTY.load(Ordering::Relaxed)
}

#[inline(always)]
fn store_pending_qty(v: i64) {
    PENDING_QTY.store(v, Ordering::Relaxed);
}

#[inline(always)]
fn load_worst_case_leaves() -> i64 {
    WORST_CASE_LEAVES.load(Ordering::Relaxed)
}

#[inline(always)]
fn store_worst_case_leaves(v: i64) {
    WORST_CASE_LEAVES.store(v, Ordering::Relaxed);
}

#[inline(always)]
fn max_i64(a: i64, b: i64) -> i64 {
    if a >= b { a } else { b }
}

/// Clean empty initializer (shared baseline for buggy FSM).
#[unsafe(no_mangle)]
pub extern "C" fn init_empty() {
    store_state(STATE_EMPTY);
    store_orig_qty(0);
    store_leaves_qty(0);
    store_cum_filled(0);
    store_pending_qty(0);
    store_worst_case_leaves(0);
}

/// Baseline `submit_new`: `Empty -> PendingNew` (needed so all lifecycle states are reachable).
#[unsafe(no_mangle)]
pub extern "C" fn submit_new(qty: i64) -> i32 {
    if load_state() != STATE_EMPTY || qty <= 0 {
        return 0;
    }
    store_state(STATE_PENDING_NEW);
    store_orig_qty(qty);
    store_leaves_qty(qty);
    store_cum_filled(0);
    store_pending_qty(0);
    store_worst_case_leaves(qty);
    1
}

/// Baseline `on_ack`: `PendingNew -> Live`.
#[unsafe(no_mangle)]
pub extern "C" fn on_ack() -> i32 {
    if load_state() != STATE_PENDING_NEW {
        return 0;
    }
    store_state(STATE_LIVE);
    1
}

/// Baseline `request_cancel`: `Live -> PendingCancel`.
#[unsafe(no_mangle)]
pub extern "C" fn request_cancel() -> i32 {
    if load_state() != STATE_LIVE {
        return 0;
    }
    store_state(STATE_PENDING_CANCEL);
    1
}

/// Baseline `on_replace_ack`: `PendingReplace -> Live | Filled`.
#[unsafe(no_mangle)]
pub extern "C" fn on_replace_ack() -> i32 {
    if load_state() != STATE_PENDING_REPLACE {
        return 0;
    }
    let new_leaves = load_pending_qty();
    let cum = load_cum_filled();
    if new_leaves < 0 || new_leaves > i64::MAX.wrapping_sub(cum) {
        return 0;
    }
    store_orig_qty(cum.wrapping_add(new_leaves));
    store_leaves_qty(new_leaves);
    store_pending_qty(0);
    store_worst_case_leaves(new_leaves);
    if new_leaves == 0 {
        store_state(STATE_FILLED);
    } else {
        store_state(STATE_LIVE);
    }
    1
}

/// Baseline `on_reject`: `PendingNew -> Rejected`, `PendingCancel | PendingReplace -> Live`.
#[unsafe(no_mangle)]
pub extern "C" fn on_reject() -> i32 {
    let st = load_state();
    if st == STATE_PENDING_NEW {
        store_state(STATE_REJECTED);
        store_leaves_qty(0);
        store_pending_qty(0);
        store_worst_case_leaves(0);
        1
    } else if st == STATE_PENDING_CANCEL || st == STATE_PENDING_REPLACE {
        store_state(STATE_LIVE);
        store_pending_qty(0);
        store_worst_case_leaves(load_leaves_qty());
        1
    } else {
        0
    }
}

/// Same inductive invariant `inv_child_fsm()` as `s3_1_child_fsm.rs`.
#[unsafe(no_mangle)]
pub extern "C" fn inv_child_fsm() -> i32 {
    let st = load_state();
    let orig = load_orig_qty();
    let leaves = load_leaves_qty();
    let cum = load_cum_filled();
    let pend = load_pending_qty();
    let wcl = load_worst_case_leaves();

    if st < STATE_EMPTY || st > STATE_REJECTED {
        return 0;
    }
    if orig < 0 || leaves < 0 || cum < 0 || pend < 0 || wcl < 0 {
        return 0;
    }
    if leaves > i64::MAX.wrapping_sub(cum) || pend > i64::MAX.wrapping_sub(cum) {
        return 0;
    }
    if wcl < leaves {
        return 0;
    }

    if st == STATE_EMPTY {
        if orig == 0 && leaves == 0 && cum == 0 && pend == 0 && wcl == 0 {
            1
        } else {
            0
        }
    } else if st == STATE_PENDING_NEW {
        if orig > 0 && leaves == orig && cum == 0 && pend == 0 && wcl == leaves {
            1
        } else {
            0
        }
    } else if st == STATE_LIVE || st == STATE_PENDING_CANCEL {
        if leaves > 0
            && orig == cum.wrapping_add(leaves)
            && pend == 0
            && wcl == leaves
        {
            1
        } else {
            0
        }
    } else if st == STATE_PENDING_REPLACE {
        if leaves > 0
            && orig == cum.wrapping_add(leaves)
            && wcl >= pend
            && wcl == max_i64(leaves, pend)
            && (pend > 0 || cum > 0)
        {
            1
        } else {
            0
        }
    } else if st == STATE_FILLED {
        if cum > 0 && orig == cum && leaves == 0 && pend == 0 && wcl == 0 {
            1
        } else {
            0
        }
    } else if st == STATE_CANCELED {
        if leaves == 0 && pend == 0 && wcl == 0 && cum <= orig {
            1
        } else {
            0
        }
    } else {
        if leaves == 0 && pend == 0 && wcl == 0 && cum == 0 {
            1
        } else {
            0
        }
    }
}

/// MUTANT 1 ("phantom flat"):
/// Ignores fills that race with an in-flight cancel (`PendingCancel`), causing the OMS
/// to believe the order was canceled flat when the exchange actually filled it!
#[unsafe(no_mangle)]
pub extern "C" fn on_fill_buggy_drops_pending_cancel(fill_qty: i64) -> i32 {
    let st = load_state();
    // BUG: missing `st != STATE_PENDING_CANCEL`! Drops fills during PendingCancel!
    if st != STATE_LIVE && st != STATE_PENDING_REPLACE {
        return 0;
    }
    let leaves = load_leaves_qty();
    if fill_qty <= 0 || fill_qty > leaves {
        return 0;
    }
    let cum = load_cum_filled();
    if fill_qty > i64::MAX.wrapping_sub(cum) {
        return 0;
    }
    let new_cum = cum.wrapping_add(fill_qty);
    let new_leaves = leaves.wrapping_sub(fill_qty);
    store_cum_filled(new_cum);
    store_leaves_qty(new_leaves);

    if new_leaves == 0 {
        store_state(STATE_FILLED);
        store_pending_qty(0);
        store_worst_case_leaves(0);
    } else if st == STATE_PENDING_REPLACE {
        let pend = load_pending_qty();
        let new_pend = if pend > fill_qty {
            pend.wrapping_sub(fill_qty)
        } else {
            0
        };
        store_pending_qty(new_pend);
        store_worst_case_leaves(max_i64(new_leaves, new_pend));
    } else {
        store_worst_case_leaves(new_leaves);
    }
    1
}

/// MUTANT 2 (terminal state overwrite / resurrection):
/// Accepts `on_cancel_ack` while already terminal `Filled`, overwriting `Filled`
/// with `Canceled` and corrupting order audit/reconciliation state!
#[unsafe(no_mangle)]
pub extern "C" fn on_cancel_ack_buggy_resurrects_or_overwrites_filled() -> i32 {
    let st = load_state();
    // BUG: allows `STATE_FILLED` to be overwritten with `STATE_CANCELED`!
    if st != STATE_PENDING_CANCEL && st != STATE_LIVE && st != STATE_FILLED {
        return 0;
    }
    store_state(STATE_CANCELED);
    store_leaves_qty(0);
    store_pending_qty(0);
    store_worst_case_leaves(0);
    1
}

/// MUTANT 3 (optimistic exposure shrink -> in-flight over-fill bug):
/// On `request_replace` from `Live`, optimistically sets `worst_case_leaves = new_leaves`
/// even when shrinking (`new_leaves < leaves_qty`) BEFORE the exchange acknowledges the replace!
/// Violates `worst_case_leaves >= leaves_qty` in `inv_child_fsm()`, allowing parent routing
/// to release risk credit prematurely and over-fill if the exchange fills the old quantity in flight.
#[unsafe(no_mangle)]
pub extern "C" fn request_replace_buggy_optimistic_leaves(new_total_qty: i64) -> i32 {
    if load_state() != STATE_LIVE {
        return 0;
    }
    let cum = load_cum_filled();
    if new_total_qty <= cum {
        return 0;
    }
    let new_leaves = new_total_qty.wrapping_sub(cum);
    store_state(STATE_PENDING_REPLACE);
    store_pending_qty(new_leaves);
    // BUG: optimistic shrink — ignores `leaves_qty` when `new_leaves < leaves_qty`!
    store_worst_case_leaves(new_leaves);
    1
}

/// Contract harness exposing Mutant 1 (`on_fill_buggy_drops_pending_cancel`):
/// Expected result: FALSIFIED (assertion fails because `ok == 0` and `cum_filled` does not increase).
#[unsafe(no_mangle)]
pub extern "C" fn contract_fill_during_pending_cancel_buggy(fill_qty: i64) -> i32 {
    assume(inv_child_fsm() != 0);
    assume(load_state() == STATE_PENDING_CANCEL);
    let old_cum = load_cum_filled();
    let old_leaves = load_leaves_qty();
    assume(fill_qty > 0 && fill_qty <= old_leaves);

    let ok = on_fill_buggy_drops_pending_cancel(fill_qty);
    assert_prop(ok == 1);
    assert_prop(load_cum_filled() > old_cum);
    assert_prop(load_cum_filled() == old_cum.wrapping_add(fill_qty));
    assert_prop(load_leaves_qty() == old_leaves.wrapping_sub(fill_qty));
    assert_prop(inv_child_fsm() != 0);
    1
}

/// Contract harness exposing Mutant 2 (`on_cancel_ack_buggy_resurrects_or_overwrites_filled`):
/// Expected result: FALSIFIED (when `st0 == STATE_FILLED` and `evt == 5`, state changes to `Canceled`).
#[unsafe(no_mangle)]
pub extern "C" fn contract_no_terminal_resurrection_buggy(evt: i32, arg: i64) -> i32 {
    assume(inv_child_fsm() != 0);
    let st0 = load_state();
    assume(st0 == STATE_FILLED || st0 == STATE_CANCELED || st0 == STATE_REJECTED);
    let cum0 = load_cum_filled();
    let leaves0 = load_leaves_qty();
    let orig0 = load_orig_qty();
    let wcl0 = load_worst_case_leaves();

    let res = if evt == 0 {
        submit_new(arg)
    } else if evt == 1 {
        on_ack()
    } else if evt == 2 {
        request_cancel()
    } else if evt == 3 {
        request_replace_buggy_optimistic_leaves(arg)
    } else if evt == 4 {
        on_fill_buggy_drops_pending_cancel(arg)
    } else if evt == 5 {
        on_cancel_ack_buggy_resurrects_or_overwrites_filled()
    } else if evt == 6 {
        on_replace_ack()
    } else {
        on_reject()
    };

    assert_prop(res == 0);
    assert_prop(load_state() == st0);
    assert_prop(load_cum_filled() == cum0);
    assert_prop(load_leaves_qty() == leaves0);
    assert_prop(load_orig_qty() == orig0);
    assert_prop(load_worst_case_leaves() == wcl0);
    assert_prop(inv_child_fsm() != 0);
    1
}

/// Contract harness exposing Mutant 3 (`request_replace_buggy_optimistic_leaves`):
/// Expected result: FALSIFIED (when `new_total_qty < cum_filled + leaves_qty`,
/// `worst_case_leaves` drops below `old_leaves` and violates `inv_child_fsm()`).
#[unsafe(no_mangle)]
pub extern "C" fn contract_replace_pessimistic_exposure_buggy(new_total_qty: i64) -> i32 {
    assume(inv_child_fsm() != 0);
    assume(load_state() == STATE_LIVE);
    let old_leaves = load_leaves_qty();
    let old_cum = load_cum_filled();
    assume(new_total_qty > old_cum);

    let ok = request_replace_buggy_optimistic_leaves(new_total_qty);
    assert_prop(ok == 1);
    assert_prop(load_state() == STATE_PENDING_REPLACE);
    assert_prop(load_worst_case_leaves() >= old_leaves);
    assert_prop(load_worst_case_leaves() >= new_total_qty.wrapping_sub(old_cum));
    assert_prop(inv_child_fsm() != 0);
    1
}
