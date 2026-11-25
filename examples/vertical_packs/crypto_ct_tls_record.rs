#![no_std]

//! Vertical Pack 5 — Cryptography / Constant-Time Security Dataplane
//! (TLS/AEAD Constant-Time PKCS#7 Unpad + 16-Byte MAC Verify + RFC 8439 ChaCha20 `u32x4` SIMD)
//!
//! Demonstrates Gnomon as BOTH a formal cryptographic equivalence/security verifier AND a
//! dual-architecture (`x86-64` & `ARM64`) **Constant-Time Zero-Branch Hardware Auditor**:
//! 1. **Constant-Time 16-Byte PKCS#7 Unpadding (`pkcs7_unpad16_ref` vs `pkcs7_unpad16_opt`):**
//!    - `pkcs7_unpad16_ref`: safe `&[u8]` slice with explicit shadow-stack `[u8; 16]` staging
//!      and branchy early-exit padding loop (`globals: 1`).
//!    - `pkcs7_unpad16_opt`: zero-stack unaligned wide load + SWAR constant-time unpad.
//!    - Proved bit-exact equivalent under `--ignore-dead-stack`, trap-free on truncated slices
//!      (`len < 16`), complete RFC 5652 postcondition `ens_pkcs7_unpad16`, and `SliceFrame readonly`.
//! 2. **Portable Constant-Time Profile Pair (`pkcs7_unpad16_branchy` vs `pkcs7_unpad16_branchless`):**
//!    - Proved bit-exact equivalent across ALL `2^128` 16-byte blocks (0 preconditions).
//!    - Audited live via `gnomon profile --compare --targets x64,arm64 --bench`: eliminates ALL
//!      secret-dependent conditional branches (`branches -> 0`) on BOTH `x64 (skylake)` and
//!      `arm64 (neoverse-v2)` (eliminating Lucky 13 / CVE-2013-0169 timing branches!) while
//!      delivering strong cycle, RThroughput, and live host `ns/op` speedups.
//! 3. **16-Byte AEAD MAC Tag Verify (`ct_mac16_eq_v128` ≡ `ct_mac16_eq_ref`):**
//!    - `v128_xor` + `v128_any_true` SIMD128 equivalence + 1-bit forgery rejection contract
//!      (`contract_mac16_1bit_flip_rejected`) over all 128 tag bits.
//! 4. **RFC 8439 ChaCha20 4-Lane Column Round (`chacha20_col_round_v128` ≡ `chacha20_col_round_ref`):**
//!    - 4-column `u32x4` SIMD128 quarter-round proved bit-exact over all 512 state bits +
//!      `SliceFrame` 64-byte write containment (`base=param:0,len=64`).

use core::slice;

#[cfg(target_arch = "wasm32")]
use core::arch::wasm32::*;

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

/// 64-byte static guard in `.bss` right above the 1 MiB shadow stack (`0x10_0000`),
/// guaranteeing `min_pages >= 17` on Wasm32.
#[cfg(target_arch = "wasm32")]
static TLS_DMA_GUARD: [u8; 64] = [0; 64];

#[cfg(target_arch = "wasm32")]
const STACK_TOP: i32 = 1_048_576; // 16 * 65536
#[cfg(target_arch = "wasm32")]
const LIVE_LO: i32 = STACK_TOP + 64;
#[cfg(target_arch = "wasm32")]
const LIVE_HI: i32 = STACK_TOP + 32_768;
#[cfg(target_arch = "wasm32")]
const MIN_LIVE_PAGES: usize = 17;

/// Precondition for `&[u8]` TLS record block slice `[rx_ptr, rx_ptr + rx_len)`:
/// lies within live memory above `SP_in + 64` with `rx_len >= 0` (including truncated `< 16`).
#[cfg(target_arch = "wasm32")]
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

/// Precondition for 64-byte ChaCha20 4x4 state matrix `[state_ptr, state_ptr + 64)`.
#[cfg(target_arch = "wasm32")]
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

// ============================================================================
// Part 1: Constant-Time 16-Byte PKCS#7 Unpad (`&[u8]` Slice Ref vs Zero-Stack Opt)
// ============================================================================

/// Shadow-stack staging helper: copies 16 bytes from `rx` into a caller-allocated `[u8; 16]`
/// buffer on `__stack_pointer` (`Global(0)`).
#[inline(never)]
fn stage_block16(rx: &[u8], staged: &mut [u8; 16]) {
    let mut i = 0usize;
    while i < 16 {
        // SAFETY: Both `rx` (`len >= 16`) and `staged` (`[u8; 16]`) have 16 valid bytes.
        // Volatile write prevents LLVM from emitting unsupported `i16x8.narrow` vectorization
        // while keeping genuine shadow-stack staging on `Global(0)`.
        unsafe {
            core::ptr::write_volatile(staged.as_mut_ptr().add(i), rx[i]);
        }
        i += 1;
    }
}

/// Reference 16-byte PKCS#7 unpadder using safe `&[u8]` slice + shadow-stack staging and
/// an idiomatic branchy early-exit loop.
/// Returns plaintext length in `0..=15` if valid RFC 5652 padding, or `-1` if invalid/truncated.
#[unsafe(no_mangle)]
pub extern "C" fn pkcs7_unpad16_ref(rx_ptr: i32, rx_len: i32) -> i32 {
    if rx_len < 16 {
        return -1;
    }
    // SAFETY: Caller satisfies `req_block16_slice` and `rx_len >= 16`.
    let rx = unsafe { slice::from_raw_parts(rx_ptr as usize as *const u8, rx_len as usize) };
    let mut staged = [0u8; 16];
    stage_block16(rx, &mut staged);

    let pad = staged[15];
    if pad == 0 || pad > 16 {
        return -1;
    }
    let start = 16usize - (pad as usize);
    let mut i = 0usize;
    while i < 16 {
        if i >= start && staged[i] != pad {
            return -1;
        }
        i += 1;
    }
    start as i32
}

/// Optimized zero-stack constant-time 16-byte PKCS#7 unpadder:
/// - Guards `rx_len < 16` (panic-free on truncated TLS records)
/// - Reads the 16-byte block via two unaligned `u64` wide loads (`0` shadow-stack writes)
/// - Delegates to 100% branchless SWAR `pkcs7_unpad16_branchless`
/// Proved bit-exact equivalent to `pkcs7_unpad16_ref` under `--ignore-dead-stack`.
#[unsafe(no_mangle)]
pub extern "C" fn pkcs7_unpad16_opt(rx_ptr: i32, rx_len: i32) -> i32 {
    if rx_len < 16 {
        return -1;
    }
    let base = rx_ptr as usize as *const u8;
    // SAFETY: Caller satisfies `req_block16_slice` and `rx_len >= 16`.
    unsafe {
        let lo = u64::from_le(core::ptr::read_unaligned(base as *const u64));
        let hi = u64::from_le(core::ptr::read_unaligned(base.add(8) as *const u64));
        pkcs7_unpad16_branchless(lo, hi)
    }
}

/// Complete RFC 5652 PKCS#7 postcondition (both soundness and completeness):
/// - Truncated slice (`rx_len < 16`) => `ret == -1`
/// - Valid return `0 <= ret <= 15` => `pad = 16 - ret` is in `1..=16` AND every trailing
///   byte `mem[rx_ptr + i]` for `i in ret..16` equals `pad`
/// - Reject return `ret == -1` (when `rx_len >= 16`) => either `pad == 0`, `pad > 16`, or at
///   least one byte in `(16 - pad)..16` differs from `pad`.
#[cfg(target_arch = "wasm32")]
#[unsafe(no_mangle)]
pub extern "C" fn ens_pkcs7_unpad16(rx_ptr: i32, rx_len: i32, ret: i32) -> i32 {
    if rx_len < 16 {
        return if ret == -1 { 1 } else { 0 };
    }
    let base = rx_ptr as usize as *const u8;
    // SAFETY: `req_block16_slice` + `rx_len >= 16`.
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

// ============================================================================
// Part 2: Portable Native Constant-Time Profile Pair (`x64` & `arm64` Audit)
// ============================================================================

/// Reference branchy 16-byte PKCS#7 unpadder over `(lo, hi)` (little-endian 16-byte block).
/// Contains secret-dependent early-exit branches on padding length and every padding byte
/// (classic Lucky 13 / CVE-2013-0169 timing side-channel pattern).
#[unsafe(no_mangle)]
pub extern "C" fn pkcs7_unpad16_branchy(lo: u64, hi: u64) -> i32 {
    let pad = ((hi >> 56) & 0xFF) as u32;
    if pad == 0 || pad > 16 {
        return -1;
    }
    let start = 16u32 - pad;
    let mut i = 0u32;
    while i < 16 {
        if i >= start {
            let b = if i < 8 {
                ((lo >> (i * 8)) & 0xFF) as u32
            } else {
                ((hi >> ((i - 8) * 8)) & 0xFF) as u32
            };
            if b != pad {
                return -1;
            }
        }
        i += 1;
    }
    start as i32
}

/// Optimized 100% branchless SWAR constant-time 16-byte PKCS#7 unpadder:
/// - Zero loops, zero `if` expressions, zero secret-dependent memory loads
/// - Proved bit-exact equivalent to `pkcs7_unpad16_branchy` across ALL `2^128` 16-byte blocks
/// - Audited by `gnomon profile --targets x64,arm64` to emit **0 conditional branches** on BOTH
///   x86-64 (`skylake`) and ARM64 (`neoverse-v2`)!
#[unsafe(no_mangle)]
pub extern "C" fn pkcs7_unpad16_branchless(lo: u64, hi: u64) -> i32 {
    let pad = ((hi >> 56) & 0xFF) as u32;
    // `pad in 1..=16` iff bit 31 of `(0 - pad)` AND bit 31 of `(pad - 17)` are both 1.
    let valid_range = ((0u32.wrapping_sub(pad) & pad.wrapping_sub(17)) >> 31) & 1;

    // Splat `pad` across all 8 bytes of a `u64` via shift/OR tree (LLVM folds to constant-time `imul`/`mul`).
    let p8 = pad as u64;
    let p16 = p8 | (p8 << 8);
    let p32 = p16 | (p16 << 16);
    let pad_splat = p32 | (p32 << 32);

    // Build exact byte masks for trailing `pad` bytes of `[lo, hi]` with zero shift>=64 UB:
    // - For `hi` (bytes 8..16): skip `8 - pad` low bytes when `pad < 8`, else skip `0`.
    let lt8 = (pad.wrapping_sub(8) >> 31) & 1;
    let hi_skip = (8u32.wrapping_sub(pad)) & 0u32.wrapping_sub(lt8);
    let mask_hi = (!0u64).wrapping_shl((hi_skip & 7) * 8);

    // - For `lo` (bytes 0..8): active only when `pad > 8`; skip `16 - pad` low bytes.
    let gt8 = (8u32.wrapping_sub(pad) >> 31) & 1;
    let lo_skip = 16u32.wrapping_sub(pad) & 7;
    let mask_lo = ((!0u64).wrapping_shl(lo_skip * 8)) & 0u64.wrapping_sub(gt8 as u64);

    let bad = ((lo ^ pad_splat) & mask_lo) | ((hi ^ pad_splat) & mask_hi);
    let bad_nz = (((bad | bad.wrapping_neg()) >> 63) & 1) as u32;

    let ok = valid_range & (bad_nz ^ 1);
    let ok_mask = 0u32.wrapping_sub(ok);
    let plain_len = 16u32.wrapping_sub(pad);
    ((plain_len & ok_mask) | (!0u32 & !ok_mask)) as i32
}

// ============================================================================
// Part 3: 16-Byte Constant-Time AEAD MAC Tag Verify (`v128` `i8x16` SIMD)
// ============================================================================

/// Reference byte-by-byte branchy 16-byte AEAD authentication tag comparison.
#[unsafe(no_mangle)]
pub extern "C" fn ct_mac16_eq_ref(a0: u64, a1: u64, b0: u64, b1: u64) -> i32 {
    let mut i = 0u32;
    while i < 8 {
        if ((a0 >> (i * 8)) & 0xFF) != ((b0 >> (i * 8)) & 0xFF) {
            return 0;
        }
        i += 1;
    }
    let mut j = 0u32;
    while j < 8 {
        if ((a1 >> (j * 8)) & 0xFF) != ((b1 >> (j * 8)) & 0xFF) {
            return 0;
        }
        j += 1;
    }
    1
}

/// Vectorized constant-time 16-byte AEAD MAC comparison using Wasm `v128.xor` + `v128.any_true`.
/// Proved bit-exact equivalent to `ct_mac16_eq_ref` across all `2^256` tag pairs.
#[cfg(target_arch = "wasm32")]
#[unsafe(no_mangle)]
pub extern "C" fn ct_mac16_eq_v128(a0: u64, a1: u64, b0: u64, b1: u64) -> i32 {
    let va = i64x2(a0 as i64, a1 as i64);
    let vb = i64x2(b0 as i64, b1 as i64);
    if !v128_any_true(v128_xor(va, vb)) {
        1
    } else {
        0
    }
}

/// Inline security contract proving ANY 1-bit flip across all 128 MAC tag bits is ALWAYS rejected,
/// while an identical 16-byte tag is ALWAYS accepted.
#[cfg(target_arch = "wasm32")]
#[unsafe(no_mangle)]
pub extern "C" fn contract_mac16_1bit_flip_rejected(a0: u64, a1: u64, bit_idx: u32) -> i32 {
    assume(bit_idx < 128);
    assert_prop(ct_mac16_eq_v128(a0, a1, a0, a1) == 1);

    let (b0, b1) = if bit_idx < 64 {
        (a0 ^ (1u64 << bit_idx), a1)
    } else {
        (a0, a1 ^ (1u64 << (bit_idx - 64)))
    };
    assert_prop(ct_mac16_eq_v128(a0, a1, b0, b1) == 0);
    1
}

// ============================================================================
// Part 4: RFC 8439 ChaCha20 4-Lane Column Round (`u32x4` SIMD128 vs Scalar)
// ============================================================================

#[cfg(target_arch = "wasm32")]
#[inline(always)]
fn chacha_qround(a: u32, b: u32, c: u32, d: u32) -> (u32, u32, u32, u32) {
    let a = a.wrapping_add(b);
    let d = (d ^ a).rotate_left(16);
    let c = c.wrapping_add(d);
    let b = (b ^ c).rotate_left(12);
    let a = a.wrapping_add(b);
    let d = (d ^ a).rotate_left(8);
    let c = c.wrapping_add(d);
    let b = (b ^ c).rotate_left(7);
    (a, b, c, d)
}

/// Scalar reference RFC 8439 ChaCha20 column round over a 64-byte `[u32; 16]` state matrix.
#[cfg(target_arch = "wasm32")]
#[unsafe(no_mangle)]
pub extern "C" fn chacha20_col_round_ref(state_ptr: i32) -> i32 {
    let base = state_ptr as usize as *mut u32;
    // SAFETY: Caller satisfies `req_chacha_state` (64 bytes in bounds).
    unsafe {
        let mut col = 0usize;
        while col < 4 {
            let a = u32::from_le(core::ptr::read_unaligned(base.add(col)));
            let b = u32::from_le(core::ptr::read_unaligned(base.add(4 + col)));
            let c = u32::from_le(core::ptr::read_unaligned(base.add(8 + col)));
            let d = u32::from_le(core::ptr::read_unaligned(base.add(12 + col)));
            let (na, nb, nc, nd) = chacha_qround(a, b, c, d);
            core::ptr::write_unaligned(base.add(col), na.to_le());
            core::ptr::write_unaligned(base.add(4 + col), nb.to_le());
            core::ptr::write_unaligned(base.add(8 + col), nc.to_le());
            core::ptr::write_unaligned(base.add(12 + col), nd.to_le());
            col += 1;
        }
    }
    1
}

#[cfg(target_arch = "wasm32")]
#[inline(always)]
fn u32x4_rotl(v: v128, k: u32) -> v128 {
    v128_or(i32x4_shl(v, k), u32x4_shr(v, 32 - k))
}

/// Vectorized `u32x4` SIMD128 RFC 8439 ChaCha20 column round (4 columns in parallel via
/// `v128_load`/`v128_store`, `i32x4_add`, `v128_xor`, `i32x4_shl`/`u32x4_shr`).
/// Proved bit-exact equivalent to `chacha20_col_round_ref` across all `2^512` state matrices
/// AND `SliceFrame` write-isolated to `[state_ptr, state_ptr + 64)`.
#[cfg(target_arch = "wasm32")]
#[unsafe(no_mangle)]
pub extern "C" fn chacha20_col_round_v128(state_ptr: i32) -> i32 {
    let base = state_ptr as usize as *mut v128;
    // SAFETY: Caller satisfies `req_chacha_state` (64 bytes in bounds).
    unsafe {
        let mut a = v128_load(base);
        let mut b = v128_load(base.add(1));
        let mut c = v128_load(base.add(2));
        let mut d = v128_load(base.add(3));

        a = i32x4_add(a, b);
        d = u32x4_rotl(v128_xor(d, a), 16);
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
