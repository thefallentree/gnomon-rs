#![no_std]

//! Vertical Pack 5 Buggy Mutants — Cryptography / Constant-Time Security Dataplane
//!
//! 1. `pkcs7_unpad16_buggy_zero_pad_oracle`: classic PKCS#7 padding oracle bug (forgets `pad >= 1`
//!    check, accepting `pad == 0` as a valid 16-byte plaintext block and violating `ens_pkcs7_unpad16`!).
//! 2. `ct_mac16_buggy_off_by_one`: classic AEAD MAC truncation bug (checks only bytes `0..15`,
//!    forgetting byte 15 — caught by `contract_mac16_1bit_flip_rejected` with a 1-bit forgery!).
//! 3. `chacha20_col_round_buggy_rot`: subtle RFC 8439 rotation typo (`rotl(15)` instead of `rotl(16)`),
//!    caught immediately by `check-goal` against `chacha20_col_round_ref`.

use core::arch::wasm32::*;

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

static TLS_DMA_GUARD: [u8; 64] = [0; 64];

const STACK_TOP: i32 = 1_048_576;
const LIVE_LO: i32 = STACK_TOP + 64;
const LIVE_HI: i32 = STACK_TOP + 32_768;
const MIN_LIVE_PAGES: usize = 17;

#[unsafe(no_mangle)]
pub extern "C" fn req_block16_slice(rx_ptr: i32, rx_len: i32) -> i32 {
    if core::arch::wasm32::memory_size(0) < MIN_LIVE_PAGES {
        return 0;
    }
    let guard_lo = (TLS_DMA_GUARD.as_ptr() as i32).wrapping_add(64);
    let live_lo = if guard_lo > LIVE_LO {
        guard_lo
    } else {
        LIVE_LO
    };
    if rx_ptr < live_lo || rx_ptr > LIVE_HI {
        return 0;
    }
    if rx_len < 0 || rx_len > LIVE_HI - rx_ptr {
        return 0;
    }
    1
}

#[unsafe(no_mangle)]
pub extern "C" fn req_chacha_state(state_ptr: i32) -> i32 {
    if core::arch::wasm32::memory_size(0) < MIN_LIVE_PAGES {
        return 0;
    }
    let guard_lo = (TLS_DMA_GUARD.as_ptr() as i32).wrapping_add(64);
    let live_lo = if guard_lo > LIVE_LO {
        guard_lo
    } else {
        LIVE_LO
    };
    if state_ptr < live_lo || state_ptr > LIVE_HI - 64 {
        return 0;
    }
    1
}

#[unsafe(no_mangle)]
pub extern "C" fn ens_pkcs7_unpad16(rx_ptr: i32, rx_len: i32, ret: i32) -> i32 {
    if rx_len < 16 {
        return if ret == -1 { 1 } else { 0 };
    }
    let base = rx_ptr as usize as *const u8;
    let pad = unsafe { core::ptr::read(base.add(15)) };
    if pad == 0 || pad > 16 {
        return if ret == -1 { 1 } else { 0 };
    }
    let start = 16usize - (pad as usize);
    let mut i = 0usize;
    while i < 16 {
        if i >= start {
            let b = unsafe { core::ptr::read(base.add(i)) };
            if b != pad {
                return if ret == -1 { 1 } else { 0 };
            }
        }
        i += 1;
    }
    let expected = 16i32 - (pad as i32);
    if ret == expected && ret >= 0 && ret <= 15 {
        1
    } else {
        0
    }
}

/// Buggy Mutant 1: omits `pad == 0` rejection, vacuously accepting `pad == 0` as 16 plaintext bytes!
#[unsafe(no_mangle)]
pub extern "C" fn pkcs7_unpad16_buggy_zero_pad_oracle(rx_ptr: i32, rx_len: i32) -> i32 {
    if rx_len < 16 {
        return -1;
    }
    let base = rx_ptr as usize as *const u8;
    unsafe {
        let pad = core::ptr::read(base.add(15));
        // BUG: forgets `pad == 0` check -> `start = 16`, loop runs 0 times, returns 16!
        if pad > 16 {
            return -1;
        }
        let start = 16usize - (pad as usize);
        let mut i = 0usize;
        while i < 16 {
            if i >= start && core::ptr::read(base.add(i)) != pad {
                return -1;
            }
            i += 1;
        }
        start as i32
    }
}

/// Buggy Mutant 2: checks only the first 15 bytes of the 16-byte AEAD MAC tag, ignoring byte 15!
#[unsafe(no_mangle)]
pub extern "C" fn ct_mac16_buggy_off_by_one(a0: u64, a1: u64, b0: u64, b1: u64) -> i32 {
    let va = i64x2(a0 as i64, a1 as i64);
    let vb = i64x2(b0 as i64, b1 as i64);
    // BUG: masks off byte 15 (`0x00FF_FFFF_FFFF_FFFF`), checking only 15 of 16 MAC bytes!
    let mask15 = i64x2(-1i64, 0x00FF_FFFF_FFFF_FFFFi64);
    let diff = v128_and(v128_xor(va, vb), mask15);
    if !v128_any_true(diff) { 1 } else { 0 }
}

/// Inline contract catching the off-by-one MAC forgery bug (`FALSIFIED`).
#[unsafe(no_mangle)]
pub extern "C" fn contract_mac16_1bit_flip_rejected(a0: u64, a1: u64, bit_idx: u32) -> i32 {
    assume(bit_idx < 128);
    assert_prop(ct_mac16_buggy_off_by_one(a0, a1, a0, a1) == 1);

    let (b0, b1) = if bit_idx < 64 {
        (a0 ^ (1u64 << bit_idx), a1)
    } else {
        (a0, a1 ^ (1u64 << (bit_idx - 64)))
    };
    assert_prop(ct_mac16_buggy_off_by_one(a0, a1, b0, b1) == 0);
    1
}

#[inline(always)]
fn u32x4_rotl(v: v128, k: u32) -> v128 {
    v128_or(i32x4_shl(v, k), u32x4_shr(v, 32 - k))
}

/// Buggy Mutant 3: subtle RFC 8439 ChaCha20 rotation typo (`15` instead of `16` on first step).
#[unsafe(no_mangle)]
pub extern "C" fn chacha20_col_round_buggy_rot(state_ptr: i32) -> i32 {
    let base = state_ptr as usize as *mut v128;
    unsafe {
        let mut a = v128_load(base);
        let mut b = v128_load(base.add(1));
        let mut c = v128_load(base.add(2));
        let mut d = v128_load(base.add(3));

        a = i32x4_add(a, b);
        // BUG: rotates left by 15 instead of RFC 8439's 16!
        d = u32x4_rotl(v128_xor(d, a), 15);
        c = i32x4_add(c, d);
        b = u32x4_rotl(v128_xor(b, c), 12);
        a = i32x4_add(a, b);
        d = u32x4_rotl(v128_xor(d, a), 8);
        c = i32x4_add(c, d);
        b = u32x4_rotl(v128_xor(b, c), 7);

        v128_store(base, a);
        v128_store(base.add(1), b);
        v128_store(base.add(2), c);
        v128_store(base.add(3), d);
    }
    1
}
