#![no_std]

//! Vertical Pack 3 Buggy Mutant — WireGuard / IPsec 64-Bit Anti-Replay Window
//!
//! `accept_nonce_buggy_shift64_wrap`: omits the `diff >= 64` guard before shifting `1u64 << diff`
//! (and `bm << diff`), causing shift counts `>= 64` to wrap modulo 64 (`1u64 << (diff & 63)`)!
//! As a result, a stale replayed old nonce (`diff >= 64`) aliases an unset bit in the 64-bit
//! bitmap and is WRONGLY ACCEPTED, and a large jump (`delta >= 64`) fails to clear stale bits!

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

static INITIALIZED: AtomicU8 = AtomicU8::new(0);
static LAST_SEQ: AtomicI64 = AtomicI64::new(0);
static BITMAP: AtomicI64 = AtomicI64::new(0);

#[unsafe(no_mangle)]
pub extern "C" fn init_replay() -> i32 {
    INITIALIZED.store(0, Ordering::Relaxed);
    LAST_SEQ.store(0, Ordering::Relaxed);
    BITMAP.store(0, Ordering::Relaxed);
    1
}

#[unsafe(no_mangle)]
pub extern "C" fn inv_replay_window() -> i32 {
    let (init, last, bm) = unsafe {
        (
            core::ptr::read_volatile(INITIALIZED.as_ptr()),
            core::ptr::read_volatile(LAST_SEQ.as_ptr()),
            core::ptr::read_volatile(BITMAP.as_ptr()) as u64,
        )
    };

    let uninit_ok = (init == 0) & (last == 0) & (bm == 0);
    let init_ok = (init == 1) & (last >= 0) & ((bm & 1u64) == 1u64);
    if uninit_ok | init_ok { 1 } else { 0 }
}

/// Buggy Mutant: forgets `diff >= 64` guard -> `wrapping_shl` wraps shift amount mod 64,
/// leaving stale bits intact on large jumps AND accepting replayed old nonces (`diff >= 64`)!
#[unsafe(no_mangle)]
pub extern "C" fn accept_nonce_buggy_shift64_wrap(seq: i64) -> i32 {
    if seq < 0 {
        return 0;
    }

    let init = INITIALIZED.load(Ordering::Relaxed);
    if init == 0 {
        INITIALIZED.store(1, Ordering::Relaxed);
        LAST_SEQ.store(seq, Ordering::Relaxed);
        BITMAP.store(1, Ordering::Relaxed);
        return 1;
    }

    let last = LAST_SEQ.load(Ordering::Relaxed);
    let bm = BITMAP.load(Ordering::Relaxed) as u64;

    if seq > last {
        let diff = (seq as u64).wrapping_sub(last as u64);
        // BUG: forgets `if diff >= 64 { 1 } else { ... }` -> wraps shift count mod 64!
        let new_bm = bm.wrapping_shl(diff as u32) | 1u64;
        LAST_SEQ.store(seq, Ordering::Relaxed);
        BITMAP.store(new_bm as i64, Ordering::Relaxed);
        1
    } else {
        let diff = (last as u64).wrapping_sub(seq as u64);
        // BUG: forgets `if diff >= 64 { return 0; }` -> `1u64 << (diff & 63)` accepts stale replay!
        let mask = 1u64.wrapping_shl(diff as u32);
        if (bm & mask) != 0 {
            return 0;
        }
        BITMAP.store((bm | mask) as i64, Ordering::Relaxed);
        1
    }
}

/// Inline contract catching the shift-64 wrap bug on large jumps & stale replay (`FALSIFIED`).
#[unsafe(no_mangle)]
pub extern "C" fn contract_large_jump_clears_stale(delta: i64) -> i32 {
    assume(inv_replay_window() == 1);
    assume(INITIALIZED.load(Ordering::Relaxed) == 1);
    let old_last = LAST_SEQ.load(Ordering::Relaxed);
    assume(delta >= 64);
    assume(old_last <= i64::MAX - delta);

    let new_seq = old_last + delta;
    let r_jump = accept_nonce_buggy_shift64_wrap(new_seq);
    assert_prop(r_jump == 1);
    assert_prop(LAST_SEQ.load(Ordering::Relaxed) == new_seq);
    assert_prop(BITMAP.load(Ordering::Relaxed) == 1);

    let r_stale = accept_nonce_buggy_shift64_wrap(old_last);
    assert_prop(r_stale == 0);
    1
}
