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

// Child order lifecycle states.
const STATE_EMPTY: i32 = 0;
const STATE_PENDING_NEW: i32 = 1;
const STATE_LIVE: i32 = 2;
const STATE_PENDING_REPLACE: i32 = 3;
const STATE_PENDING_CANCEL: i32 = 4;
const STATE_FILLED: i32 = 5;
const STATE_CANCELED: i32 = 6;
const STATE_REJECTED: i32 = 7;

// Single child order state stored in fixed linear-memory slots via Relaxed atomics
// (zero `unsafe` raw pointers, zero `__stack_pointer` shadow-stack spills on wasm32).
static STATE: AtomicI32 = AtomicI32::new(STATE_EMPTY);
static ORIG_QTY: AtomicI64 = AtomicI64::new(0);
static LEAVES_QTY: AtomicI64 = AtomicI64::new(0);
static CUM_FILLED: AtomicI64 = AtomicI64::new(0);
// `PENDING_QTY` holds the pending replacement leaves (`new_total_qty - cum_filled`)
// while in `PendingReplace`, and `0` in all other states.
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

/// Initialize a clean empty child order slot (`state = Empty`, all quantities zero).
#[unsafe(no_mangle)]
pub extern "C" fn init_empty() {
    store_state(STATE_EMPTY);
    store_orig_qty(0);
    store_leaves_qty(0);
    store_cum_filled(0);
    store_pending_qty(0);
    store_worst_case_leaves(0);
}

/// Submit a new child order: `Empty -> PendingNew` if `qty > 0`.
/// Returns `1` on valid transition, `0` otherwise (no-op).
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

/// Exchange order acknowledgement: `PendingNew -> Live`.
/// Returns `1` on valid transition, `0` otherwise (no-op).
#[unsafe(no_mangle)]
pub extern "C" fn on_ack() -> i32 {
    if load_state() != STATE_PENDING_NEW {
        return 0;
    }
    store_state(STATE_LIVE);
    1
}

/// Initiate cancel request: `Live -> PendingCancel`.
/// Pessimistic exposure is preserved (`worst_case_leaves == leaves_qty`) until exchange ack.
#[unsafe(no_mangle)]
pub extern "C" fn request_cancel() -> i32 {
    if load_state() != STATE_LIVE {
        return 0;
    }
    store_state(STATE_PENDING_CANCEL);
    1
}

/// Initiate cancel/replace request: `Live -> PendingReplace` for desired `new_total_qty`.
/// Requires `new_total_qty > cum_filled` so pending leaves `new_leaves = new_total_qty - cum_filled > 0`.
/// Updates pessimistic `worst_case_leaves = max(leaves_qty, new_leaves)`.
#[unsafe(no_mangle)]
pub extern "C" fn request_replace(new_total_qty: i64) -> i32 {
    if load_state() != STATE_LIVE {
        return 0;
    }
    let cum = load_cum_filled();
    if new_total_qty <= cum {
        return 0;
    }
    let leaves = load_leaves_qty();
    let new_leaves = new_total_qty.wrapping_sub(cum);
    store_state(STATE_PENDING_REPLACE);
    store_pending_qty(new_leaves);
    store_worst_case_leaves(max_i64(leaves, new_leaves));
    1
}

/// Process an exchange execution fill (`fill_qty > 0 && fill_qty <= leaves_qty`).
/// Valid in `Live | PendingCancel | PendingReplace` — NEVER drops a fill during `PendingCancel`.
/// Transitions to terminal `Filled` when `leaves_qty` reaches `0`.
#[unsafe(no_mangle)]
pub extern "C" fn on_fill(fill_qty: i64) -> i32 {
    let st = load_state();
    if st != STATE_LIVE && st != STATE_PENDING_CANCEL && st != STATE_PENDING_REPLACE {
        return 0;
    }
    let leaves = load_leaves_qty();
    if fill_qty <= 0 || fill_qty > leaves {
        return 0;
    }
    let cum = load_cum_filled();
    // Guard against i64 wraparound even if invoked outside invariant.
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

/// Process exchange cancel acknowledgement (or unsolicited cancel while `Live`).
/// Valid ONLY in `PendingCancel | Live` — NEVER resurrects or overwrites `Filled`/`Canceled`/`Rejected`,
/// and NEVER erases `cum_filled`.
#[unsafe(no_mangle)]
pub extern "C" fn on_cancel_ack() -> i32 {
    let st = load_state();
    if st != STATE_PENDING_CANCEL && st != STATE_LIVE {
        return 0;
    }
    store_state(STATE_CANCELED);
    store_leaves_qty(0);
    store_pending_qty(0);
    store_worst_case_leaves(0);
    1
}

/// Commit an acknowledged cancel/replace: `PendingReplace -> Live` (or `Filled` if pending leaves hit 0
/// due to an intervening fill). Updates `orig_qty = cum_filled + new_leaves` and `worst_case_leaves = new_leaves`.
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

/// Process exchange rejection:
/// - `PendingNew -> Rejected` (zeros `leaves_qty`, `pending_qty`, `worst_case_leaves`)
/// - `PendingCancel | PendingReplace -> Live` (restores `worst_case_leaves = leaves_qty`, clears `pending_qty`)
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

/// Full inductive state invariant `inv_child_fsm() -> i32` (`1` iff all clauses hold):
/// 1. `0 <= state <= 7`
/// 2. All quantities non-negative (`orig_qty`, `leaves_qty`, `cum_filled`, `pending_qty`, `worst_case_leaves >= 0`)
/// 3. Overflow-free accounting (`cum_filled + leaves_qty <= i64::MAX`, `cum_filled + pending_qty <= i64::MAX`)
/// 4. Global pessimistic bound: `worst_case_leaves >= leaves_qty`
/// 5. Terminal states (`Empty | Filled | Canceled | Rejected`):
///    `leaves_qty == 0 && worst_case_leaves == 0 && pending_qty == 0`
///    plus `Empty => orig_qty == 0 && cum_filled == 0`,
///    `Filled => cum_filled > 0 && orig_qty == cum_filled`,
///    `Canceled => cum_filled <= orig_qty`,
///    `Rejected => cum_filled == 0`.
/// 6. Active states:
///    - `PendingNew`: `orig_qty > 0 && leaves_qty == orig_qty && cum_filled == 0 && pending_qty == 0 && worst_case_leaves == leaves_qty`
///    - `Live | PendingCancel`: `leaves_qty > 0 && orig_qty == cum_filled + leaves_qty && pending_qty == 0 && worst_case_leaves == leaves_qty`
///    - `PendingReplace`: `leaves_qty > 0 && orig_qty == cum_filled + leaves_qty && worst_case_leaves >= pending_qty && worst_case_leaves == max(leaves_qty, pending_qty) && (pending_qty > 0 || cum_filled > 0)`
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
        // STATE_REJECTED
        if leaves == 0 && pend == 0 && wcl == 0 && cum == 0 {
            1
        } else {
            0
        }
    }
}

/// Inline relational contract harness:
/// Proves that a valid fill arriving during `PendingCancel` is NEVER dropped:
/// it succeeds (`ret == 1`), strictly increases `cum_filled` by `fill_qty`,
/// decreases `leaves_qty` by `fill_qty`, and preserves `inv_child_fsm()`.
#[unsafe(no_mangle)]
pub extern "C" fn contract_fill_during_pending_cancel(fill_qty: i64) -> i32 {
    assume(inv_child_fsm() != 0);
    assume(load_state() == STATE_PENDING_CANCEL);
    let old_cum = load_cum_filled();
    let old_leaves = load_leaves_qty();
    assume(fill_qty > 0 && fill_qty <= old_leaves);

    let ok = on_fill(fill_qty);
    assert_prop(ok == 1);
    assert_prop(load_cum_filled() > old_cum);
    assert_prop(load_cum_filled() == old_cum.wrapping_add(fill_qty));
    assert_prop(load_leaves_qty() == old_leaves.wrapping_sub(fill_qty));
    assert_prop(inv_child_fsm() != 0);
    1
}

/// Inline relational contract harness:
/// Proves that once an order reaches ANY terminal state (`Filled | Canceled | Rejected`),
/// NO event (`0..=7`) can resurrect it or alter `state`, `cum_filled`, `leaves_qty`,
/// `orig_qty`, or `worst_case_leaves`.
#[unsafe(no_mangle)]
pub extern "C" fn contract_no_terminal_resurrection(evt: i32, arg: i64) -> i32 {
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
        request_replace(arg)
    } else if evt == 4 {
        on_fill(arg)
    } else if evt == 5 {
        on_cancel_ack()
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

/// Inline relational contract harness:
/// Proves that `request_replace` from `Live` NEVER optimistically shrinks `worst_case_leaves`
/// below current `leaves_qty` before exchange acknowledgement, covers `new_leaves`,
/// and preserves `inv_child_fsm()`.
#[unsafe(no_mangle)]
pub extern "C" fn contract_replace_pessimistic_exposure(new_total_qty: i64) -> i32 {
    assume(inv_child_fsm() != 0);
    assume(load_state() == STATE_LIVE);
    let old_leaves = load_leaves_qty();
    let old_cum = load_cum_filled();
    assume(new_total_qty > old_cum);

    let ok = request_replace(new_total_qty);
    assert_prop(ok == 1);
    assert_prop(load_state() == STATE_PENDING_REPLACE);
    assert_prop(load_worst_case_leaves() >= old_leaves);
    assert_prop(load_worst_case_leaves() >= new_total_qty.wrapping_sub(old_cum));
    assert_prop(inv_child_fsm() != 0);
    1
}
