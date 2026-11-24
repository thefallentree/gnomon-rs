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

#[unsafe(no_mangle)]
pub extern "C" fn ring_len() -> i32 {
    load_tail().wrapping_sub(load_head())
}

#[unsafe(no_mangle)]
pub extern "C" fn ring_pop_ok() -> i32 {
    let len = load_tail().wrapping_sub(load_head()) as u32;
    if len > 0 && len <= (CAP as u32) {
        1
    } else {
        0
    }
}

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

#[unsafe(no_mangle)]
pub extern "C" fn inv_spsc_ring() -> i32 {
    let cap = load_cap();
    if cap != CAP || (cap & (cap - 1)) != 0 {
        return 0;
    }
    let len = load_tail().wrapping_sub(load_head()) as u32;
    if len <= (CAP as u32) { 1 } else { 0 }
}

/// Buggy Mutant 1: missing full-ring guard (`len >= CAP`).
/// Overwrites the oldest unread slot `slots[head & 7]` and increments `tail` past `head + CAP`,
/// violating both `inv_spsc_ring()` and `contract_push_full_rejected_buggy`.
#[unsafe(no_mangle)]
pub extern "C" fn ring_push_buggy_overwrite(val: i64) -> i32 {
    if load_cap() != CAP {
        return 0;
    }
    let t = load_tail();
    store_slot(t & MASK, val);
    store_tail(t.wrapping_add(1));
    1
}

/// Buggy Mutant 2: off-by-one bitmask (`t & (CAP - 2)` instead of `t & (CAP - 1)`).
/// Odd cursor positions write to the wrong even slot, corrupting FIFO round-trips
/// whenever `head` is odd!
#[unsafe(no_mangle)]
pub extern "C" fn ring_push_buggy_bad_mask(val: i64) -> i32 {
    if load_cap() != CAP {
        return 0;
    }
    let h = load_head();
    let t = load_tail();
    let len = t.wrapping_sub(h) as u32;
    if len >= (CAP as u32) {
        return 0;
    }
    store_slot(t & (CAP - 2), val);
    store_tail(t.wrapping_add(1));
    1
}

/// Inline contract harness targeting Mutant 1 (`ring_push_buggy_overwrite`): MUST FALSIFY.
#[unsafe(no_mangle)]
pub extern "C" fn contract_push_full_rejected_buggy(val: i64) -> i32 {
    assume(inv_spsc_ring() != 0);
    assume(ring_len() == CAP);
    let h0 = load_head();
    let t0 = load_tail();
    let front0 = load_slot(h0 & MASK);

    let ok = ring_push_buggy_overwrite(val);
    assert_prop(ok == 0);
    assert_prop(load_head() == h0);
    assert_prop(load_tail() == t0);
    assert_prop(load_slot(h0 & MASK) == front0);
    assert_prop(inv_spsc_ring() != 0);
    1
}

/// Inline contract harness targeting Mutant 2 (`ring_push_buggy_bad_mask`): MUST FALSIFY.
#[unsafe(no_mangle)]
pub extern "C" fn contract_push_pop_roundtrip_buggy(val: i64) -> i32 {
    assume(inv_spsc_ring() != 0);
    assume(ring_len() == 0);

    let pushed = ring_push_buggy_bad_mask(val);
    assert_prop(pushed == 1);
    assert_prop(ring_len() == 1);
    assert_prop(ring_pop_ok() == 1);

    let popped = ring_pop();
    assert_prop(popped == val);
    assert_prop(ring_len() == 0);
    assert_prop(inv_spsc_ring() != 0);
    1
}
