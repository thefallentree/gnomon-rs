#![no_std]

//! Vertical Pack 2 — Columnar DB / Apache Parquet (4-Byte LEB128 Varint Slice Decoder + Delta-ZigZag)
//!
//! 1. `varint_decode_ref` (safe `&[u8]` slice with explicit shadow-stack `[u8; 4]` staging buffer)
//!    vs `varint_decode_opt` (zero-stack unaligned `u32` wide-load branchless fast path + safe
//!    truncated-slice tail for `len < 4`).
//!    - Proved equivalent under `--ignore-dead-stack` across all slice lengths `len >= 0`
//!    - Proved trap-free (zero panics on truncated slices) and `SliceFrame readonly` (input slice untouched)
//! 2. Delta-ZigZag encode/decode (`zigzag_encode`, `zigzag_decode`, `zigzag_enc_dec_roundtrip`):
//!    - Proved `zigzag_decode(zigzag_encode(x)) == x` for all `2^64` `i64` values (including `i64::MIN`/`MAX`)
//! 3. Portable native profile pair (`varint_decode_branchy_ref` vs `varint_decode_branchless_opt`)
//!    for `gnomon profile --compare --targets x64,arm64` (also proved bit-exact equivalent!).

use core::slice;

#[cfg(target_arch = "wasm32")]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

#[cfg(target_arch = "wasm32")]
#[link(wasm_import_module = "gnomon")]
unsafe extern "C" {
    fn gnomon_assert(cond: i32);
}

#[cfg(target_arch = "wasm32")]
#[inline(always)]
fn assert_prop(cond: bool) {
    unsafe {
        gnomon_assert(if cond { 1 } else { 0 });
    }
}

/// 64-byte static guard placed in `.bss` right above the 1 MiB shadow stack
/// (`0x10_0000`), ensuring `min_pages >= 17` (`1_114_112` bytes) on Wasm32.
#[cfg(target_arch = "wasm32")]
static PARQUET_DMA_GUARD: [u8; 64] = [0; 64];

#[cfg(target_arch = "wasm32")]
const STACK_TOP: i32 = 1_048_576; // 16 * 65536
#[cfg(target_arch = "wasm32")]
const LIVE_LO: i32 = STACK_TOP + 64;
#[cfg(target_arch = "wasm32")]
const LIVE_HI: i32 = STACK_TOP + 32_768;
#[cfg(target_arch = "wasm32")]
const MIN_LIVE_PAGES: usize = 17;

/// Precondition for `varint_decode_ref` and `varint_decode_opt`:
/// `[rx_ptr, rx_ptr + rx_len)` lies within the live window above `SP_in + 64`
/// with non-negative length `rx_len >= 0` (including truncated slices `rx_len < 4`).
#[cfg(target_arch = "wasm32")]
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

/// Shadow-stack staging helper: copies up to 4 available bytes from `rx` into a
/// caller-allocated `[u8; 4]` buffer on `__stack_pointer` (`Global(0)`), returning `min(rx.len(), 4)`.
#[inline(never)]
fn stage_varint_bytes(rx: &[u8], staged: &mut [u8; 4]) -> usize {
    let n = if rx.len() < 4 { rx.len() } else { 4 };
    let mut i = 0usize;
    while i < n {
        staged[i] = rx[i];
        i += 1;
    }
    n
}

/// Reference 4-byte LEB128 varint decoder (safe `&[u8]` slice + shadow-stack staging):
/// Returns packed `i64`:
/// - `((consumed_bytes as i64) << 32) | (decoded_u28 as i64)` with `consumed_bytes in 1..=4`
/// - `0` on truncated input (`rx_len == 0` or continuation bit `0x80` extends past `rx_len`)
///   or overflow (> 4-byte varint where byte 3 still has `0x80` set).
#[unsafe(no_mangle)]
pub extern "C" fn varint_decode_ref(rx_ptr: i32, rx_len: i32) -> i64 {
    if rx_len <= 0 {
        return 0;
    }
    // SAFETY: Caller satisfies `req_varint_slice`.
    let rx = unsafe { slice::from_raw_parts(rx_ptr as usize as *const u8, rx_len as usize) };
    let mut staged = [0u8; 4];
    let n = stage_varint_bytes(rx, &mut staged);

    let mut acc: u32 = 0;
    let mut i = 0usize;
    while i < n {
        let b = staged[i];
        acc |= ((b & 0x7F) as u32) << (i * 7);
        if (b & 0x80) == 0 {
            let consumed = (i + 1) as u64;
            return ((consumed << 32) | (acc as u64)) as i64;
        }
        i += 1;
    }
    0
}

/// Optimized zero-stack 4-byte LEB128 varint decoder:
/// - Hot path (`rx_len >= 4`): single unaligned `u32` wide load (`u32::from_le`) +
///   branchless continuation bitmask + zero shadow-stack usage (`0` `Global(0)` accesses).
/// - Short-slice tail (`rx_len < 4`): safe bounds-checked byte reads with zero OOB traps.
#[unsafe(no_mangle)]
pub extern "C" fn varint_decode_opt(rx_ptr: i32, rx_len: i32) -> i64 {
    if rx_len <= 0 {
        return 0;
    }
    let base = rx_ptr as usize as *const u8;
    // SAFETY: Caller satisfies `req_varint_slice`; every load is guarded by `rx_len`.
    unsafe {
        if rx_len >= 4 {
            let w = u32::from_le(core::ptr::read_unaligned(base as *const u32));
            return varint_decode_branchless_opt(w) as i64;
        }

        let b0 = core::ptr::read(base);
        let v0 = (b0 & 0x7F) as u32;
        if (b0 & 0x80) == 0 {
            return ((1u64 << 32) | (v0 as u64)) as i64;
        }
        if rx_len < 2 {
            return 0;
        }
        let b1 = core::ptr::read(base.add(1));
        let v1 = v0 | (((b1 & 0x7F) as u32) << 7);
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
        0
    }
}

// ============================================================================
// Delta-ZigZag Encode / Decode (Parquet `DELTA_BINARY_PACKED`)
// ============================================================================

/// ZigZag signed-to-unsigned encoding: maps `0 -> 0, -1 -> 1, 1 -> 2, -2 -> 3, ...`.
#[unsafe(no_mangle)]
pub extern "C" fn zigzag_encode(x: i64) -> u64 {
    ((x << 1) ^ (x >> 63)) as u64
}

/// ZigZag unsigned-to-signed decoding (exact inverse of `zigzag_encode`).
#[unsafe(no_mangle)]
pub extern "C" fn zigzag_decode(u: u64) -> i64 {
    ((u >> 1) as i64) ^ (-((u & 1) as i64))
}

/// Round-trip composition `zigzag_decode(zigzag_encode(x))`.
#[unsafe(no_mangle)]
pub extern "C" fn zigzag_enc_dec_roundtrip(x: i64) -> i64 {
    zigzag_decode(zigzag_encode(x))
}

/// Specification identity for `check-goal` equivalence against `zigzag_enc_dec_roundtrip`.
#[unsafe(no_mangle)]
pub extern "C" fn identity_i64(x: i64) -> i64 {
    x
}

/// Inline contract proving `zigzag_decode(zigzag_encode(x)) == x` across all `2^64` `i64` inputs.
#[cfg(target_arch = "wasm32")]
#[unsafe(no_mangle)]
pub extern "C" fn contract_zigzag_roundtrip(x: i64) -> i32 {
    assert_prop(zigzag_enc_dec_roundtrip(x) == x);
    1
}

// ============================================================================
// Portable Native Profile Pair (`gnomon profile --compare --targets x64,arm64`)
// ============================================================================

/// Reference branchy 4-byte LEB128 varint decoder operating on a 4-byte little-endian word.
/// Early-exits per byte, producing 4 conditional branches on native x86-64 and ARM64.
#[unsafe(no_mangle)]
pub extern "C" fn varint_decode_branchy_ref(w: u32) -> u64 {
    let b0 = (w & 0xFF) as u8;
    let v0 = (b0 & 0x7F) as u32;
    if (b0 & 0x80) == 0 {
        return (1u64 << 32) | (v0 as u64);
    }
    let b1 = ((w >> 8) & 0xFF) as u8;
    let v1 = v0 | (((b1 & 0x7F) as u32) << 7);
    if (b1 & 0x80) == 0 {
        return (2u64 << 32) | (v1 as u64);
    }
    let b2 = ((w >> 16) & 0xFF) as u8;
    let v2 = v1 | (((b2 & 0x7F) as u32) << 14);
    if (b2 & 0x80) == 0 {
        return (3u64 << 32) | (v2 as u64);
    }
    let b3 = ((w >> 24) & 0xFF) as u8;
    let v3 = v2 | (((b3 & 0x7F) as u32) << 21);
    if (b3 & 0x80) == 0 {
        return (4u64 << 32) | (v3 as u64);
    }
    0
}

/// Optimized branchless 4-byte LEB128 varint decoder operating on a 4-byte little-endian word.
/// Emits 0 conditional branches on BOTH x86-64 (`skylake`) and ARM64 (`neoverse-v2`),
/// and is proved bit-for-bit equivalent to `varint_decode_branchy_ref` over all `2^32` words.
#[unsafe(no_mangle)]
pub extern "C" fn varint_decode_branchless_opt(w: u32) -> u64 {
    let c0 = ((w >> 7) & 1) as u32;
    let c1 = c0 & ((w >> 15) & 1);
    let c2 = c1 & ((w >> 23) & 1);
    let c3 = c2 & ((w >> 31) & 1);

    let m1 = 0u32.wrapping_sub(c0);
    let m2 = 0u32.wrapping_sub(c1);
    let m3 = 0u32.wrapping_sub(c2);
    let ok_mask = 0u64.wrapping_sub((c3 ^ 1) as u64);

    let d0 = w & 0x7F;
    let d1 = ((w >> 8) & 0x7F) & m1;
    let d2 = ((w >> 16) & 0x7F) & m2;
    let d3 = ((w >> 24) & 0x7F) & m3;

    let val = (d0 | (d1 << 7) | (d2 << 14) | (d3 << 21)) as u64;
    let consumed = (1u32 + c0 + c1 + c2) as u64;
    ((consumed << 32) | val) & ok_mask
}
