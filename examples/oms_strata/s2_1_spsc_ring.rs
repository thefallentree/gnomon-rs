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

const CAP: i32 = 8;
const MASK: i32 = CAP - 1;

// Power-of-2 Disruptor-style SPSC ring buffer stored in fixed linear-memory
// atomic slots (`globals: 0`, zero `__stack_pointer`, zero raw-pointer unsafe).
static HEAD: AtomicI32 = AtomicI32::new(0);
static TAIL: AtomicI32 = AtomicI32::new(0);
static CAPACITY: AtomicI32 = AtomicI32::new(CAP);

static SLOTS: [AtomicI64; 8] = [
    AtomicI64::new(0),
    AtomicI64::new(0),
    AtomicI64::new(0),
    AtomicI64::new(0),
    AtomicI64::new(0),
    AtomicI64::new(0),
    AtomicI64::new(0),
    AtomicI64::new(0),
];

#[inline(always)]
fn load_head() -> i32 {
    HEAD.load(Ordering::Relaxed)
}

#[inline(always)]
fn store_head(v: i32) {
    HEAD.store(v, Ordering::Relaxed);
}

#[inline(always)]
fn load_tail() -> i32 {
    TAIL.load(Ordering::Relaxed)
}

#[inline(always)]
fn store_tail(v: i32) {
    TAIL.store(v, Ordering::Relaxed);
}

#[inline(always)]
fn load_cap() -> i32 {
    CAPACITY.load(Ordering::Relaxed)
}

#[inline(always)]
fn store_cap(v: i32) {
    CAPACITY.store(v, Ordering::Relaxed);
}

#[inline(always)]
fn load_slot(idx: i32) -> i64 {
    SLOTS[(idx & MASK) as usize].load(Ordering::Relaxed)
}

#[inline(always)]
fn store_slot(idx: i32, val: i64) {
    SLOTS[(idx & MASK) as usize].store(val, Ordering::Relaxed);
}

/// Initialize an empty SPSC ring buffer (`head = 0`, `tail = 0`, `cap = 8`, zeroed slots).
#[unsafe(no_mangle)]
pub extern "C" fn init_ring() {
    store_head(0);
    store_tail(0);
    store_cap(CAP);
    SLOTS[0].store(0, Ordering::Relaxed);
    SLOTS[1].store(0, Ordering::Relaxed);
    SLOTS[2].store(0, Ordering::Relaxed);
    SLOTS[3].store(0, Ordering::Relaxed);
    SLOTS[4].store(0, Ordering::Relaxed);
    SLOTS[5].store(0, Ordering::Relaxed);
    SLOTS[6].store(0, Ordering::Relaxed);
    SLOTS[7].store(0, Ordering::Relaxed);
}

/// Current occupancy `tail.wrapping_sub(head)` (in `0..=8` whenever `inv_spsc_ring()` holds,
/// even across 32-bit `head`/`tail` wraparound).
#[unsafe(no_mangle)]
pub extern "C" fn ring_len() -> i32 {
    load_tail().wrapping_sub(load_head())
}

/// Returns `1` iff the ring has at least one unread element available to pop, `0` if empty.
#[unsafe(no_mangle)]
pub extern "C" fn ring_pop_ok() -> i32 {
    let len = load_tail().wrapping_sub(load_head()) as u32;
    if len > 0 && len <= (CAP as u32) {
        1
    } else {
        0
    }
}

/// Producer push: writes `val` into `slots[tail & 7]` and advances `tail` by 1.
/// Returns `1` on success, `0` if full (leaving `head`, `tail`, and all unread slots untouched).
#[unsafe(no_mangle)]
pub extern "C" fn ring_push(val: i64) -> i32 {
    if load_cap() != CAP {
        return 0;
    }
    let h = load_head();
    let t = load_tail();
    let len = t.wrapping_sub(h) as u32;
    if len >= (CAP as u32) {
        return 0;
    }
    store_slot(t & MASK, val);
    store_tail(t.wrapping_add(1));
    1
}

/// Consumer pop: reads `slots[head & 7]` and advances `head` by 1 if non-empty.
/// Returns the popped value, or `0` (no-op) when the ring is empty.
#[unsafe(no_mangle)]
pub extern "C" fn ring_pop() -> i64 {
    if load_cap() != CAP {
        return 0;
    }
    let h = load_head();
    let t = load_tail();
    let len = t.wrapping_sub(h) as u32;
    if len == 0 || len > (CAP as u32) {
        return 0;
    }
    let v = load_slot(h & MASK);
    store_head(h.wrapping_add(1));
    v
}

/// Inductive state invariant `inv_spsc_ring() -> i32`:
/// - `cap == 8` (and power-of-2: `cap > 0 && (cap & (cap - 1)) == 0`)
/// - `tail.wrapping_sub(head) as u32 <= 8` (holds across arbitrary 32-bit wraparound!).
#[unsafe(no_mangle)]
pub extern "C" fn inv_spsc_ring() -> i32 {
    let cap = load_cap();
    if cap != CAP || (cap & (cap - 1)) != 0 {
        return 0;
    }
    let len = load_tail().wrapping_sub(load_head()) as u32;
    if len <= (CAP as u32) { 1 } else { 0 }
}

/// Inline relational contract:
/// Proves that pushing into a full ring (`len == 8`, at any wrapped `head`/`tail`)
/// is rejected (`ret == 0`), preserves `head`, `tail`, and the oldest unread slot
/// `slots[head & 7]`, and maintains `inv_spsc_ring()`.
#[unsafe(no_mangle)]
pub extern "C" fn contract_push_full_rejected(val: i64) -> i32 {
    assume(inv_spsc_ring() != 0);
    assume(ring_len() == CAP);
    let h0 = load_head();
    let t0 = load_tail();
    let front0 = load_slot(h0 & MASK);

    let ok = ring_push(val);
    assert_prop(ok == 0);
    assert_prop(load_head() == h0);
    assert_prop(load_tail() == t0);
    assert_prop(load_slot(h0 & MASK) == front0);
    assert_prop(inv_spsc_ring() != 0);
    1
}

/// Inline relational contract:
/// Proves FIFO push/pop round-trip on an empty ring at ANY wrapped cursor `head == tail`:
/// `ring_push(val)` succeeds, sets `ring_len() == 1` and `ring_pop_ok() == 1`,
/// and `ring_pop()` returns exact `val`, restoring `ring_len() == 0` and `inv_spsc_ring()`.
#[unsafe(no_mangle)]
pub extern "C" fn contract_push_pop_roundtrip(val: i64) -> i32 {
    assume(inv_spsc_ring() != 0);
    assume(ring_len() == 0);

    let pushed = ring_push(val);
    assert_prop(pushed == 1);
    assert_prop(ring_len() == 1);
    assert_prop(ring_pop_ok() == 1);
    assert_prop(inv_spsc_ring() != 0);

    let popped = ring_pop();
    assert_prop(popped == val);
    assert_prop(ring_len() == 0);
    assert_prop(ring_pop_ok() == 0);
    assert_prop(inv_spsc_ring() != 0);
    1
}
