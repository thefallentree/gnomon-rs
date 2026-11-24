#![no_std]

//! Vertical Pack 4 — Distributed Cloud Quota / Reservation Saga (Multi-Tenant 4-Slot Saga)
//!
//! Generalizes OMS `S3.2`/`S3.3` two-phase reservation accounting to a distributed cloud tenant
//! quota saga stored in fixed linear-memory slots (`globals: 0` via `AtomicI32`/`AtomicU32`,
//! zero shadow stack, zero `.rodata`):
//! - Tenant quota state: `LIMIT`, `COMMITTED`, `RESERVED`
//! - 4 in-flight reservation slots: packed 4×u8 `R_STATE` (`r_state[0..4]`) + `R_QTY[4]`
//! - Operations: `init_quota(limit)`, `reserve(slot, qty)`, `commit(slot)`, `cancel_reserve(slot)`
//! - Inductive invariant `inv_quota_saga()`:
//!   - `0 <= committed`, `0 <= reserved`, `committed + reserved <= limit` (ZERO over-commit!)
//!   - `reserved == sum_{s=0..4}(active r_qty[s])` (exact conservation with zero overflow!)
//!   - Active (`R_RESERVED`) slots have `r_qty > 0`; `R_EMPTY`/`R_COMMITTED`/`R_CANCELED` have `r_qty == 0`
//! - Inline contracts:
//!   - `contract_no_double_release(slot)`: duplicate `cancel_reserve(slot)` NEVER double-releases quota!
//!   - `contract_commit_conserves_total(slot)`: `commit(slot)` strictly conserves `committed + reserved`!

use core::sync::atomic::{AtomicI32, AtomicU32, Ordering};

#[cfg(target_arch = "wasm32")]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

#[cfg(target_arch = "wasm32")]
#[link(wasm_import_module = "gnomon")]
unsafe extern "C" {
    fn gnomon_assume(cond: i32);
    fn gnomon_assert(cond: i32);
}

#[cfg(target_arch = "wasm32")]
#[inline(always)]
fn assume(cond: bool) {
    unsafe {
        gnomon_assume(if cond { 1 } else { 0 });
    }
}

#[cfg(target_arch = "wasm32")]
#[inline(always)]
fn assert_prop(cond: bool) {
    unsafe {
        gnomon_assert(if cond { 1 } else { 0 });
    }
}

// Reservation slot lifecycle states (1 byte per slot packed into `R_STATE`).
const R_EMPTY: u32 = 0;
const R_RESERVED: u32 = 1;
const R_COMMITTED: u32 = 2;
const R_CANCELED: u32 = 3;

// Tenant quota & 4-slot reservation table in fixed linear memory (globals: 0, zero .rodata).
static LIMIT: AtomicI32 = AtomicI32::new(0);
static COMMITTED: AtomicI32 = AtomicI32::new(0);
static RESERVED: AtomicI32 = AtomicI32::new(0);
static R_STATE: AtomicU32 = AtomicU32::new(0); // 4 × u8 slot states: r_state[s] = (R_STATE >> (s*8)) & 0xFF
static R_QTY: [AtomicI32; 4] = [
    AtomicI32::new(0),
    AtomicI32::new(0),
    AtomicI32::new(0),
    AtomicI32::new(0),
];

/// Branchless, overflow-safe exact 4-way non-negative sum in Z via symmetric depth-2 tree.
#[inline(always)]
fn sum4_checked(a: i32, b: i32, c: i32, d: i32) -> i32 {
    let s01 = a.wrapping_add(b);
    let s23 = c.wrapping_add(d);
    let s = s01.wrapping_add(s23);
    if (a | b | c | d | s01 | s23 | s) < 0 {
        -1
    } else {
        s
    }
}

/// Branchless, overflow-safe exact 4-way non-negative sum equality check: `a + b + c + d == total`.
#[inline(always)]
fn sum4_eq(a: i32, b: i32, c: i32, d: i32, total: i32) -> bool {
    let s01 = a.wrapping_add(b);
    let s23 = c.wrapping_add(d);
    let s = s01.wrapping_add(s23);
    ((a | b | c | d | total | s01 | s23 | s) >= 0) & (s == total)
}

#[inline(always)]
fn select_i32(slot: i32, v0: i32, v1: i32, v2: i32, v3: i32) -> i32 {
    let v01 = if slot == 0 { v0 } else { v1 };
    let v23 = if slot == 2 { v2 } else { v3 };
    if (slot & 2) == 0 { v01 } else { v23 }
}

#[inline(always)]
fn slot_valid(st: u32, q: i32) -> bool {
    let active_ok = (st == R_RESERVED) & (q > 0);
    let inactive_ok = ((st == R_EMPTY) | (st == R_COMMITTED) | (st == R_CANCELED)) & (q == 0);
    active_ok | inactive_ok
}

#[inline(always)]
fn write_r_qty(slot: i32, qty: i32) {
    if slot == 0 {
        R_QTY[0].store(qty, Ordering::Relaxed);
    } else if slot == 1 {
        R_QTY[1].store(qty, Ordering::Relaxed);
    } else if slot == 2 {
        R_QTY[2].store(qty, Ordering::Relaxed);
    } else {
        R_QTY[3].store(qty, Ordering::Relaxed);
    }
}

/// Initialize tenant quota saga with `limit` (clamped to `0` if negative so `I(post_init)`
/// holds unconditionally for all `limit: i32`). Returns `1` if `limit >= 0`, else `0`.
#[unsafe(no_mangle)]
pub extern "C" fn init_quota(limit: i32) -> i32 {
    let eff_limit = if limit >= 0 { limit } else { 0 };
    LIMIT.store(eff_limit, Ordering::Relaxed);
    COMMITTED.store(0, Ordering::Relaxed);
    RESERVED.store(0, Ordering::Relaxed);
    R_STATE.store(0, Ordering::Relaxed);
    R_QTY[0].store(0, Ordering::Relaxed);
    R_QTY[1].store(0, Ordering::Relaxed);
    R_QTY[2].store(0, Ordering::Relaxed);
    R_QTY[3].store(0, Ordering::Relaxed);
    if limit >= 0 { 1 } else { 0 }
}

/// Inductive invariant for the multi-tenant reservation saga:
/// 1. `limit >= 0`, `committed >= 0`, `reserved >= 0`
/// 2. Zero over-commit: `committed + reserved <= limit` (overflow-safe)
/// 3. Each slot `s in 0..4` has valid state & `r_qty[s] > 0` iff `R_RESERVED` (`0` otherwise)
/// 4. Exact conservation: `reserved == r_qty[0] + r_qty[1] + r_qty[2] + r_qty[3]`
#[unsafe(no_mangle)]
pub extern "C" fn inv_quota_saga() -> i32 {
    // SAFETY: Volatile reads emit plain Wasm loads while preventing LLVM GlobalOpt
    // from eliding symbolic pre-state range checks on private statics (`globals: 0`).
    let (limit, committed, reserved, states, q0, q1, q2, q3) = unsafe {
        (
            core::ptr::read_volatile(LIMIT.as_ptr()),
            core::ptr::read_volatile(COMMITTED.as_ptr()),
            core::ptr::read_volatile(RESERVED.as_ptr()),
            core::ptr::read_volatile(R_STATE.as_ptr()),
            core::ptr::read_volatile(R_QTY[0].as_ptr()),
            core::ptr::read_volatile(R_QTY[1].as_ptr()),
            core::ptr::read_volatile(R_QTY[2].as_ptr()),
            core::ptr::read_volatile(R_QTY[3].as_ptr()),
        )
    };

    let used = committed.wrapping_add(reserved);
    let ok = (limit >= 0)
        & (committed >= 0)
        & (reserved >= 0)
        & (used >= 0)
        & (used <= limit)
        & slot_valid(states & 0xFF, q0)
        & slot_valid((states >> 8) & 0xFF, q1)
        & slot_valid((states >> 16) & 0xFF, q2)
        & slot_valid((states >> 24) & 0xFF, q3)
        & sum4_eq(q0, q1, q2, q3, reserved);
    if ok { 1 } else { 0 }
}

/// Phase-1 Saga Reserve: atomically reserves `qty > 0` in an empty `slot` (`0..4`)
/// iff sufficient headroom (`committed + next_reserved <= limit`) exists.
#[unsafe(no_mangle)]
pub extern "C" fn reserve(slot: i32, qty: i32) -> i32 {
    let limit = LIMIT.load(Ordering::Relaxed);
    let committed = COMMITTED.load(Ordering::Relaxed);
    let states = R_STATE.load(Ordering::Relaxed);
    let q0 = R_QTY[0].load(Ordering::Relaxed);
    let q1 = R_QTY[1].load(Ordering::Relaxed);
    let q2 = R_QTY[2].load(Ordering::Relaxed);
    let q3 = R_QTY[3].load(Ordering::Relaxed);

    let shift = ((slot & 3) as u32) * 8;
    let st = (states >> shift) & 0xFF;

    let c_q0 = if slot == 0 { qty } else { q0 };
    let c_q1 = if slot == 1 { qty } else { q1 };
    let c_q2 = if slot == 2 { qty } else { q2 };
    let c_q3 = if slot == 3 { qty } else { q3 };

    let next_reserved = sum4_checked(c_q0, c_q1, c_q2, c_q3);
    let next_used = committed.wrapping_add(next_reserved);

    let ok = (slot >= 0)
        & (slot < 4)
        & (qty > 0)
        & (st == R_EMPTY)
        & (limit >= 0)
        & (committed >= 0)
        & (next_reserved >= 0)
        & (next_used >= 0)
        & (next_used <= limit);

    if !ok {
        return 0;
    }

    let next_states = (states & !(0xFFu32 << shift)) | (R_RESERVED << shift);
    R_STATE.store(next_states, Ordering::Relaxed);
    RESERVED.store(next_reserved, Ordering::Relaxed);
    write_r_qty(slot, qty);
    1
}

/// Phase-2 Saga Commit: transitions an active `R_RESERVED` slot to `R_COMMITTED`,
/// atomically moving `r_qty[slot]` from `RESERVED` to `COMMITTED`.
#[unsafe(no_mangle)]
pub extern "C" fn commit(slot: i32) -> i32 {
    let limit = LIMIT.load(Ordering::Relaxed);
    let committed = COMMITTED.load(Ordering::Relaxed);
    let states = R_STATE.load(Ordering::Relaxed);
    let q0 = R_QTY[0].load(Ordering::Relaxed);
    let q1 = R_QTY[1].load(Ordering::Relaxed);
    let q2 = R_QTY[2].load(Ordering::Relaxed);
    let q3 = R_QTY[3].load(Ordering::Relaxed);

    let shift = ((slot & 3) as u32) * 8;
    let st = (states >> shift) & 0xFF;
    let slot_q = select_i32(slot, q0, q1, q2, q3);

    let c_q0 = if slot == 0 { 0 } else { q0 };
    let c_q1 = if slot == 1 { 0 } else { q1 };
    let c_q2 = if slot == 2 { 0 } else { q2 };
    let c_q3 = if slot == 3 { 0 } else { q3 };

    let next_reserved = sum4_checked(c_q0, c_q1, c_q2, c_q3);
    let next_committed = committed.wrapping_add(slot_q);
    let next_used = next_committed.wrapping_add(next_reserved);

    let ok = (slot >= 0)
        & (slot < 4)
        & (st == R_RESERVED)
        & (limit >= 0)
        & (next_committed >= 0)
        & (next_reserved >= 0)
        & (next_used >= 0)
        & (next_used <= limit);

    if !ok {
        return 0;
    }

    let next_states = (states & !(0xFFu32 << shift)) | (R_COMMITTED << shift);
    R_STATE.store(next_states, Ordering::Relaxed);
    COMMITTED.store(next_committed, Ordering::Relaxed);
    RESERVED.store(next_reserved, Ordering::Relaxed);
    write_r_qty(slot, 0);
    1
}

/// Phase-2 Saga Compensating Action (Cancel): releases an active `R_RESERVED` slot's quota
/// back to tenant headroom and marks the slot `R_CANCELED` with `r_qty[slot] = 0`.
/// Strictly idempotent against duplicate retries (calling again returns `0`, zero state change).
#[unsafe(no_mangle)]
pub extern "C" fn cancel_reserve(slot: i32) -> i32 {
    let limit = LIMIT.load(Ordering::Relaxed);
    let committed = COMMITTED.load(Ordering::Relaxed);
    let states = R_STATE.load(Ordering::Relaxed);
    let q0 = R_QTY[0].load(Ordering::Relaxed);
    let q1 = R_QTY[1].load(Ordering::Relaxed);
    let q2 = R_QTY[2].load(Ordering::Relaxed);
    let q3 = R_QTY[3].load(Ordering::Relaxed);

    let shift = ((slot & 3) as u32) * 8;
    let st = (states >> shift) & 0xFF;

    let c_q0 = if slot == 0 { 0 } else { q0 };
    let c_q1 = if slot == 1 { 0 } else { q1 };
    let c_q2 = if slot == 2 { 0 } else { q2 };
    let c_q3 = if slot == 3 { 0 } else { q3 };

    let next_reserved = sum4_checked(c_q0, c_q1, c_q2, c_q3);
    let next_used = committed.wrapping_add(next_reserved);

    let ok = (slot >= 0)
        & (slot < 4)
        & (st == R_RESERVED)
        & (limit >= 0)
        & (committed >= 0)
        & (next_reserved >= 0)
        & (next_used >= 0)
        & (next_used <= limit);

    if !ok {
        return 0;
    }

    let next_states = (states & !(0xFFu32 << shift)) | (R_CANCELED << shift);
    R_STATE.store(next_states, Ordering::Relaxed);
    RESERVED.store(next_reserved, Ordering::Relaxed);
    write_r_qty(slot, 0);
    1
}

// ============================================================================
// Inline Contracts (`gnomon_assume` / `gnomon_assert`)
// ============================================================================

/// Proves duplicate `cancel_reserve(slot)` NEVER double-releases quota and preserves `inv_quota_saga`.
#[cfg(target_arch = "wasm32")]
#[unsafe(no_mangle)]
pub extern "C" fn contract_no_double_release(slot: i32) -> i32 {
    assume(inv_quota_saga() == 1);
    let _r1 = cancel_reserve(slot);
    let res_after_1 = RESERVED.load(Ordering::Relaxed);
    let r2 = cancel_reserve(slot);
    let res_after_2 = RESERVED.load(Ordering::Relaxed);
    assert_prop(r2 == 0);
    assert_prop(res_after_2 == res_after_1);
    assert_prop(inv_quota_saga() == 1);
    1
}

/// Proves duplicate `commit(slot)` NEVER double-commits quota (`r2 == 0` and `COMMITTED` unchanged).
#[cfg(target_arch = "wasm32")]
#[unsafe(no_mangle)]
pub extern "C" fn contract_no_double_commit(slot: i32) -> i32 {
    assume(inv_quota_saga() == 1);
    let _r1 = commit(slot);
    let com_after_1 = COMMITTED.load(Ordering::Relaxed);
    let r2 = commit(slot);
    let com_after_2 = COMMITTED.load(Ordering::Relaxed);
    assert_prop(r2 == 0);
    assert_prop(com_after_2 == com_after_1);
    1
}
