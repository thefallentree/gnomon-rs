#![no_std]

//! Vertical Pack 2 Buggy Mutants — Columnar DB / Parquet Varint Slice Decoder
//!
//! 1. `varint_decode_buggy_short_read`: reads 4 bytes from the slice without guarding `len >= 4`,
//!    causing an out-of-bounds panic/trap on truncated slices (`len < 4`).
//! 2. `varint_decode_buggy_shift_overflow`: forgets to mask the continuation bit `0x80` on
//!    intermediate bytes and shifts byte 3 improperly, corrupting multi-byte varints.

use core::slice;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

static PARQUET_DMA_GUARD: [u8; 64] = [0; 64];

const STACK_TOP: i32 = 1_048_576;
const LIVE_LO: i32 = STACK_TOP + 64;
const LIVE_HI: i32 = STACK_TOP + 32_768;
const MIN_LIVE_PAGES: usize = 17;

#[unsafe(no_mangle)]
pub extern "C" fn req_varint_slice(rx_ptr: i32, rx_len: i32) -> i32 {
    if core::arch::wasm32::memory_size(0) < MIN_LIVE_PAGES {
        return 0;
    }
    let guard_lo = (PARQUET_DMA_GUARD.as_ptr() as i32).wrapping_add(64);
    let live_lo = if guard_lo > LIVE_LO { guard_lo } else { LIVE_LO };
    if rx_ptr < live_lo || rx_ptr > LIVE_HI {
        return 0;
    }
    if rx_len < 0 || rx_len > LIVE_HI - rx_ptr {
        return 0;
    }
    1
}

#[inline(always)]
fn slice_get_or_trap(s: &[u8], idx: usize) -> u8 {
    match s.get(idx) {
        Some(&b) => b,
        None => core::arch::wasm32::unreachable(),
    }
}

/// Buggy Mutant 1: blindly loads a 4-byte window via bounds-checked slice indexing when `rx_len >= 1`
/// without checking `rx_len >= 4` -> triggers OOB trap on truncated slices (`len < 4`)!
#[unsafe(no_mangle)]
pub extern "C" fn varint_decode_buggy_short_read(rx_ptr: i32, rx_len: i32) -> i64 {
    if rx_len <= 0 {
        return 0;
    }
    // SAFETY: Caller satisfies `req_varint_slice`.
    let rx = unsafe { slice::from_raw_parts(rx_ptr as usize as *const u8, rx_len as usize) };
    // BUG: assumes at least 4 bytes are readable for the wide-load fast path!
    let w = u32::from_le_bytes([
        slice_get_or_trap(rx, 0),
        slice_get_or_trap(rx, 1),
        slice_get_or_trap(rx, 2),
        slice_get_or_trap(rx, 3),
    ]);
    let c0 = (w >> 7) & 1;
    let c1 = c0 & ((w >> 15) & 1);
    let c2 = c1 & ((w >> 23) & 1);
    let c3 = c2 & ((w >> 31) & 1);
    if c3 != 0 {
        return 0;
    }
    let m1 = 0u32.wrapping_sub(c0);
    let m2 = 0u32.wrapping_sub(c1);
    let m3 = 0u32.wrapping_sub(c2);
    let val = ((w & 0x7F)
        | (((w >> 8) & 0x7F) & m1) << 7
        | (((w >> 16) & 0x7F) & m2) << 14
        | (((w >> 24) & 0x7F) & m3) << 21) as u64;
    let consumed = (1u32 + c0 + c1 + c2) as u64;
    ((consumed << 32) | val) as i64
}

/// Buggy Mutant 2: safe on truncated slices, but forgets `& 0x7F` on byte 0/1/2 and shifts byte 3
/// by 24 instead of 21 (classic shift-overflow / continuation-bit bleed bug)!
#[unsafe(no_mangle)]
pub extern "C" fn varint_decode_buggy_shift_overflow(rx_ptr: i32, rx_len: i32) -> i64 {
    if rx_len <= 0 {
        return 0;
    }
    let base = rx_ptr as usize as *const u8;
    // SAFETY: Caller satisfies `req_varint_slice`.
    unsafe {
        let b0 = core::ptr::read(base);
        if (b0 & 0x80) == 0 {
            return ((1u64 << 32) | (b0 as u64)) as i64;
        }
        if rx_len < 2 {
            return 0;
        }
        let b1 = core::ptr::read(base.add(1));
        // BUG: forgets `& 0x7F` on `b0`, letting continuation bit `0x80` bleed into bit 7!
        let v1 = (b0 as u32) | (((b1 & 0x7F) as u32) << 7);
        if (b1 & 0x80) == 0 {
            return ((2u64 << 32) | (v1 as u64)) as i64;
        }
        if rx_len < 3 {
            return 0;
        }
        let b2 = core::ptr::read(base.add(2));
        let v2 = v1 | (((b2 & 0x7F) as u32) << 14);
        if (b2 & 0x80) == 0 {
            return ((3u64 << 32) | (v2 as u64)) as i64;
        }
        if rx_len < 4 {
            return 0;
        }
        let b3 = core::ptr::read(base.add(3));
        if (b3 & 0x80) != 0 {
            return 0;
        }
        // BUG: shifts by 24 instead of 21 -> overflows 28-bit payload into upper bits!
        let v3 = v2 | (((b3 & 0x7F) as u32) << 24);
        ((4u64 << 32) | (v3 as u64)) as i64
    }
}
