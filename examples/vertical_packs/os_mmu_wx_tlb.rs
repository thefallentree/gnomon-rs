#![no_std]

//! Vertical Pack 7 — OS Kernel / Hypervisor Memory Protection & Vectorized TLB
//! (4-Region `W^X` MMU/MPU Manager + `v128` `i32x4` 4-Way Parallel TLB Access Check)
//!
//! Models a microkernel / hypervisor / sandbox 4-region memory-protection table (`globals: 0`
//! via `AtomicU32`, zero shadow stack) plus a vectorized 4-way TLB permission checker:
//! 1. **Inductive Multi-Op `W^X` MMU Safety (`init_mmu` + `map_region,mprotect_region,unmap_region`):**
//!    - Strict **`W^X` (Write XOR Execute):** no active region EVER has both `PERM_WRITE` & `PERM_EXEC`.
//!    - **4 KiB Page Alignment:** every active mapping has `(base & 0xFFF) == 0`, `(len & 0xFFF) == 0`, `len > 0`.
//!    - **Zero `u32` Wraparound:** `base <= ADDR_LIMIT && len <= ADDR_LIMIT - base` (eliminates
//!      classic `mmap`/VMA integer-overflow overlap CVEs).
//!    - **Pairwise Disjointness:** all 6 unordered slot pairs `(i, j)` are strictly non-overlapping.
//! 2. **Global Virtual-Address Security Contracts (`gnomon_assume` / `gnomon_assert`):**
//!    - `contract_no_wx_escalation(slot, new_perm, addr)`: proves global address-level `W^X`
//!      non-interference across ALL `2^32` virtual addresses after any `mprotect_region` call!
//!    - `contract_unmap_revokes_access(slot, offset, req_perm)`: proves `unmap_region(slot)`
//!      immediately revokes ALL access to every byte of the unmapped region (zero alias leaks!).
//! 3. **Vectorized 4-Way Parallel TLB Lookup (`tlb_check_4_ref` vs `tlb_check_4_v128` & `tlb_check_4_branchless`):**
//!    - Proved bit-exact equivalent (`tlb_check_4_v128 ≡ tlb_check_4_ref` AND
//!      `tlb_check_4_branchless ≡ tlb_check_4_ref`) + `SliceFrame readonly` (TLB tables untouched!).
//!    - Exact same `tlb_check_4_ref -> tlb_check_4_branchless` pair profiled natively on BOTH
//!      x86-64 (`skylake` AVX2/SSE) and ARM64 (`neoverse-v2` NEON) + live host `--bench`.

use core::sync::atomic::{AtomicU32, Ordering};

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

// ============================================================================
// Part 1: Stateful 4-Region `W^X` MMU / MPU Page-Protection Table (`globals: 0`)
// ============================================================================

const PERM_READ: u32 = 1;
const PERM_WRITE: u32 = 2;
const PERM_EXEC: u32 = 4;
const PERM_MASK: u32 = PERM_READ | PERM_WRITE | PERM_EXEC; // 0x7
const PERM_WX: u32 = PERM_WRITE | PERM_EXEC; // 0x6 (FORBIDDEN!)
const PAGE_MASK: u32 = 0x0FFF; // 4 KiB pages
const ADDR_LIMIT: u32 = 0xFFFF_F000; // 4 GiB minus top guard page

// Fixed linear-memory MMU table (globals: 0, zero shadow stack).
static BASE: [AtomicU32; 4] = [
    AtomicU32::new(0),
    AtomicU32::new(0),
    AtomicU32::new(0),
    AtomicU32::new(0),
];
static LEN: [AtomicU32; 4] = [
    AtomicU32::new(0),
    AtomicU32::new(0),
    AtomicU32::new(0),
    AtomicU32::new(0),
];
// Packed 4 × u8 region permissions: `perm[s] = (PERM >> (s * 8)) & 0xFF` (`0` = unmapped).
static PERM: AtomicU32 = AtomicU32::new(0);

#[inline(always)]
fn perm_valid_wx(p: u32) -> bool {
    (p != 0) & ((p & !PERM_MASK) == 0) & ((p & PERM_WX) != PERM_WX)
}

#[inline(always)]
fn region_valid(base: u32, len: u32, perm: u32) -> bool {
    let unmapped_ok = (perm == 0) & (base == 0) & (len == 0);
    let mapped_ok = perm_valid_wx(perm)
        & ((base & PAGE_MASK) == 0)
        & ((len & PAGE_MASK) == 0)
        & (len > 0)
        & (base <= ADDR_LIMIT)
        & (len <= ADDR_LIMIT.wrapping_sub(base));
    unmapped_ok | mapped_ok
}

#[inline(always)]
fn pair_disjoint(b1: u32, l1: u32, p1: u32, b2: u32, l2: u32, p2: u32) -> bool {
    let e1 = b1.wrapping_add(l1);
    let e2 = b2.wrapping_add(l2);
    (p1 == 0) | (p2 == 0) | (e1 <= b2) | (e2 <= b1)
}

#[cfg(target_arch = "wasm32")]
#[inline(always)]
fn select_u32(slot: i32, v0: u32, v1: u32, v2: u32, v3: u32) -> u32 {
    let v01 = if slot == 0 { v0 } else { v1 };
    let v23 = if slot == 2 { v2 } else { v3 };
    if (slot & 2) == 0 { v01 } else { v23 }
}

#[inline(always)]
fn load_slot(a: &AtomicU32) -> u32 {
    // SAFETY: Plain volatile load on fixed static linear-memory slot; prevents LLVM
    // GlobalOpt folding and unsupported `v128.load32_zero` SLP vectorization on Wasm32.
    unsafe { core::ptr::read_volatile(a.as_ptr()) }
}

#[inline(always)]
fn write_slot(slot: i32, base: u32, len: u32) {
    if slot == 0 {
        BASE[0].store(base, Ordering::Relaxed);
        LEN[0].store(len, Ordering::Relaxed);
    } else if slot == 1 {
        BASE[1].store(base, Ordering::Relaxed);
        LEN[1].store(len, Ordering::Relaxed);
    } else if slot == 2 {
        BASE[2].store(base, Ordering::Relaxed);
        LEN[2].store(len, Ordering::Relaxed);
    } else {
        BASE[3].store(base, Ordering::Relaxed);
        LEN[3].store(len, Ordering::Relaxed);
    }
}

/// Initialize an empty 4-region MMU table (all slots unmapped).
#[unsafe(no_mangle)]
pub extern "C" fn init_mmu() -> i32 {
    BASE[0].store(0, Ordering::Relaxed);
    BASE[1].store(0, Ordering::Relaxed);
    BASE[2].store(0, Ordering::Relaxed);
    BASE[3].store(0, Ordering::Relaxed);
    LEN[0].store(0, Ordering::Relaxed);
    LEN[1].store(0, Ordering::Relaxed);
    LEN[2].store(0, Ordering::Relaxed);
    LEN[3].store(0, Ordering::Relaxed);
    PERM.store(0, Ordering::Relaxed);
    1
}

/// Inductive OS kernel MMU safety invariant (`W^X` + 4 KiB page-aligned + no overflow +
/// pairwise disjointness across all 4 region slots).
#[unsafe(no_mangle)]
pub extern "C" fn inv_mmu_wx() -> i32 {
    // SAFETY: Volatile reads emit plain Wasm loads while preventing LLVM GlobalOpt
    // from eliding symbolic pre-state range checks on private statics (`globals: 0`).
    let (b0, b1, b2, b3, l0, l1, l2, l3, perms) = unsafe {
        (
            core::ptr::read_volatile(BASE[0].as_ptr()),
            core::ptr::read_volatile(BASE[1].as_ptr()),
            core::ptr::read_volatile(BASE[2].as_ptr()),
            core::ptr::read_volatile(BASE[3].as_ptr()),
            core::ptr::read_volatile(LEN[0].as_ptr()),
            core::ptr::read_volatile(LEN[1].as_ptr()),
            core::ptr::read_volatile(LEN[2].as_ptr()),
            core::ptr::read_volatile(LEN[3].as_ptr()),
            core::ptr::read_volatile(PERM.as_ptr()),
        )
    };
    let p0 = perms & 0xFF;
    let p1 = (perms >> 8) & 0xFF;
    let p2 = (perms >> 16) & 0xFF;
    let p3 = (perms >> 24) & 0xFF;

    if !region_valid(b0, l0, p0) {
        return 0;
    }
    if !region_valid(b1, l1, p1) {
        return 0;
    }
    if !region_valid(b2, l2, p2) {
        return 0;
    }
    if !region_valid(b3, l3, p3) {
        return 0;
    }
    if !pair_disjoint(b0, l0, p0, b1, l1, p1)
        || !pair_disjoint(b0, l0, p0, b2, l2, p2)
        || !pair_disjoint(b0, l0, p0, b3, l3, p3)
        || !pair_disjoint(b1, l1, p1, b2, l2, p2)
        || !pair_disjoint(b1, l1, p1, b3, l3, p3)
        || !pair_disjoint(b2, l2, p2, b3, l3, p3)
    {
        return 0;
    }
    1
}

/// Map a new 4 KiB-aligned `W^X` memory region into an unmapped `slot` (`0..4`),
/// rejecting wraparound, misaligned addresses, `W+X`, or any overlap with active slots.
#[unsafe(no_mangle)]
pub extern "C" fn map_region(slot: i32, base: u32, len: u32, perm: u32) -> i32 {
    let b0 = load_slot(&BASE[0]);
    let b1 = load_slot(&BASE[1]);
    let b2 = load_slot(&BASE[2]);
    let b3 = load_slot(&BASE[3]);
    let l0 = load_slot(&LEN[0]);
    let l1 = load_slot(&LEN[1]);
    let l2 = load_slot(&LEN[2]);
    let l3 = load_slot(&LEN[3]);
    let perms = load_slot(&PERM);

    let p0 = perms & 0xFF;
    let p1 = (perms >> 8) & 0xFF;
    let p2 = (perms >> 16) & 0xFF;
    let p3 = (perms >> 24) & 0xFF;

    let shift = ((slot & 3) as u32) * 8;
    let cur_p = (perms >> shift) & 0xFF;

    let valid_new = perm_valid_wx(perm)
        & ((base & PAGE_MASK) == 0)
        & ((len & PAGE_MASK) == 0)
        & (len > 0)
        & (base <= ADDR_LIMIT)
        & (len <= ADDR_LIMIT.wrapping_sub(base));

    if slot < 0 || slot >= 4 || cur_p != 0 || !valid_new {
        return 0;
    }
    if (slot != 0 && !pair_disjoint(base, len, perm, b0, l0, p0))
        || (slot != 1 && !pair_disjoint(base, len, perm, b1, l1, p1))
        || (slot != 2 && !pair_disjoint(base, len, perm, b2, l2, p2))
        || (slot != 3 && !pair_disjoint(base, len, perm, b3, l3, p3))
    {
        return 0;
    }

    let next_perms = (perms & !(0xFFu32 << shift)) | (perm << shift);
    write_slot(slot, base, len);
    PERM.store(next_perms, Ordering::Relaxed);
    1
}

/// Change permissions (`mprotect`) of an active mapped `slot` (`0..4`), strictly enforcing `W^X`.
#[unsafe(no_mangle)]
pub extern "C" fn mprotect_region(slot: i32, new_perm: u32) -> i32 {
    let perms = PERM.load(Ordering::Relaxed);
    let shift = ((slot & 3) as u32) * 8;
    let cur_p = (perms >> shift) & 0xFF;

    let ok = (slot >= 0) & (slot < 4) & (cur_p != 0) & perm_valid_wx(new_perm);
    if !ok {
        return 0;
    }

    let next_perms = (perms & !(0xFFu32 << shift)) | (new_perm << shift);
    PERM.store(next_perms, Ordering::Relaxed);
    1
}

/// Unmap an active `slot` (`0..4`), clearing its base, length, and permission bits atomically.
#[unsafe(no_mangle)]
pub extern "C" fn unmap_region(slot: i32) -> i32 {
    let perms = PERM.load(Ordering::Relaxed);
    let shift = ((slot & 3) as u32) * 8;
    let cur_p = (perms >> shift) & 0xFF;

    let ok = (slot >= 0) & (slot < 4) & (cur_p != 0);
    if !ok {
        return 0;
    }

    let next_perms = perms & !(0xFFu32 << shift);
    write_slot(slot, 0, 0);
    PERM.store(next_perms, Ordering::Relaxed);
    1
}

/// Check whether virtual address `addr` is permitted for `req_perm` under the current MMU table.
#[unsafe(no_mangle)]
pub extern "C" fn mmu_check_access(addr: u32, req_perm: u32) -> i32 {
    if req_perm == 0 || (req_perm & !PERM_MASK) != 0 {
        return 0;
    }
    let b0 = load_slot(&BASE[0]);
    let b1 = load_slot(&BASE[1]);
    let b2 = load_slot(&BASE[2]);
    let b3 = load_slot(&BASE[3]);
    let l0 = load_slot(&LEN[0]);
    let l1 = load_slot(&LEN[1]);
    let l2 = load_slot(&LEN[2]);
    let l3 = load_slot(&LEN[3]);
    let perms = load_slot(&PERM);
    let p0 = perms & 0xFF;
    let p1 = (perms >> 8) & 0xFF;
    let p2 = (perms >> 16) & 0xFF;
    let p3 = (perms >> 24) & 0xFF;

    if p0 != 0 && addr >= b0 && addr.wrapping_sub(b0) < l0 && (p0 & req_perm) == req_perm {
        return 1;
    }
    if p1 != 0 && addr >= b1 && addr.wrapping_sub(b1) < l1 && (p1 & req_perm) == req_perm {
        return 1;
    }
    if p2 != 0 && addr >= b2 && addr.wrapping_sub(b2) < l2 && (p2 & req_perm) == req_perm {
        return 1;
    }
    if p3 != 0 && addr >= b3 && addr.wrapping_sub(b3) < l3 && (p3 & req_perm) == req_perm {
        return 1;
    }
    0
}

// ============================================================================
// Inline Global Security Contracts (`gnomon_assume` / `gnomon_assert`)
// ============================================================================

/// Proves GLOBAL virtual-address `W^X` non-interference: starting from ANY invariant-satisfying
/// MMU state, after ANY `mprotect_region(slot, new_perm)`, NO virtual address `addr` in `[0, 2^32)`
/// can EVER be simultaneously writable AND executable!
#[cfg(target_arch = "wasm32")]
#[unsafe(no_mangle)]
pub extern "C" fn contract_no_wx_escalation(slot: i32, new_perm: u32, addr: u32) -> i32 {
    assume(inv_mmu_wx() == 1);
    let _r = mprotect_region(slot, new_perm);
    assert_prop(inv_mmu_wx() == 1);
    let can_w = mmu_check_access(addr, PERM_WRITE);
    let can_x = mmu_check_access(addr, PERM_EXEC);
    assert_prop(!(can_w == 1 && can_x == 1));
    1
}

/// Proves immediate access revocation on `unmap_region(slot)`: because active mappings are
/// pairwise disjoint, unmapping `slot` revokes ALL access (`R`, `W`, `X`) to every address
/// `old_base + offset` (`offset < old_len`) with zero alias mappings left behind!
#[cfg(target_arch = "wasm32")]
#[unsafe(no_mangle)]
pub extern "C" fn contract_unmap_revokes_access(slot: i32, offset: u32, req_perm: u32) -> i32 {
    assume(inv_mmu_wx() == 1);
    assume(slot >= 0 && slot < 4);
    let perms = PERM.load(Ordering::Relaxed);
    let cur_p = (perms >> ((slot as u32) * 8)) & 0xFF;
    assume(cur_p != 0);

    let old_base = select_u32(
        slot,
        load_slot(&BASE[0]),
        load_slot(&BASE[1]),
        load_slot(&BASE[2]),
        load_slot(&BASE[3]),
    );
    let old_len = select_u32(
        slot,
        load_slot(&LEN[0]),
        load_slot(&LEN[1]),
        load_slot(&LEN[2]),
        load_slot(&LEN[3]),
    );
    assume(offset < old_len);
    let target_addr = old_base.wrapping_add(offset);

    let r = unmap_region(slot);
    assert_prop(r == 1);
    assert_prop(inv_mmu_wx() == 1);
    assert_prop(mmu_check_access(target_addr, req_perm) == 0);
    1
}

// ============================================================================
// Part 2: Vectorized 4-Way Parallel TLB Lookup (`v128` SIMD + Native Profile Pair)
// ============================================================================

#[cfg(target_arch = "wasm32")]
const STACK_TOP: i32 = 1_048_576; // 16 * 65536
#[cfg(target_arch = "wasm32")]
const LIVE_LO: i32 = STACK_TOP + 64;
#[cfg(target_arch = "wasm32")]
const LIVE_HI: i32 = STACK_TOP + 32_768;
#[cfg(target_arch = "wasm32")]
const MIN_LIVE_PAGES: usize = 17;

/// Precondition for 3× 16-byte TLB descriptor arrays (`bases`, `lens`, `perms`) in live memory.
#[cfg(target_arch = "wasm32")]
#[unsafe(no_mangle)]
pub extern "C" fn req_tlb_tables(
    bases: *const u32,
    lens: *const u32,
    perms: *const u32,
    _addr: u32,
    _req_perm: u32,
) -> i32 {
    if core::arch::wasm32::memory_size(0) < MIN_LIVE_PAGES {
        return 0;
    }
    let bp = bases as i32;
    let lp = lens as i32;
    let pp = perms as i32;
    let ok = (bp >= LIVE_LO)
        & (bp <= LIVE_HI - 16)
        & (lp >= LIVE_LO)
        & (lp <= LIVE_HI - 16)
        & (pp >= LIVE_LO)
        & (pp <= LIVE_HI - 16);
    if ok { 1 } else { 0 }
}

/// Reference branchy 4-way sequential TLB / MPU access check:
/// Returns `1` iff `req_perm` is a valid non-zero mask (`1..=7`) and some TLB slot `i in 0..4`
/// has `perms[i] != 0`, `addr in [bases[i], bases[i] + lens[i])` (unsigned overflow-safe),
/// and `(perms[i] & req_perm) == req_perm`.
#[unsafe(no_mangle)]
pub extern "C" fn tlb_check_4_ref(
    bases: *const u32,
    lens: *const u32,
    perms: *const u32,
    addr: u32,
    req_perm: u32,
) -> i32 {
    if req_perm == 0 || (req_perm & !PERM_MASK) != 0 {
        return 0;
    }
    // SAFETY: Caller supplies valid 4-element `bases`, `lens`, and `perms` tables.
    unsafe {
        let mut i = 0usize;
        while i < 4 {
            let p = core::ptr::read_unaligned(perms.add(i));
            if p != 0 {
                let b = core::ptr::read_unaligned(bases.add(i));
                if addr >= b {
                    let l = core::ptr::read_unaligned(lens.add(i));
                    if addr.wrapping_sub(b) < l && (p & req_perm) == req_perm {
                        return 1;
                    }
                }
            }
            i += 1;
        }
    }
    0
}

/// Optimized 100% branchless 4-way parallel TLB / MPU access check:
/// - Zero conditional branches on BOTH x86-64 (`skylake`) and ARM64 (`neoverse-v2` NEON)
/// - Proved bit-exact equivalent to `tlb_check_4_ref` across all memory contents and inputs
/// - Proved `SliceFrame readonly` (TLB tables are 100% untouched)
/// - Profiled directly via `gnomon profile --compare --targets x64,arm64 --bench`.
#[unsafe(no_mangle)]
pub extern "C" fn tlb_check_4_branchless(
    bases: *const u32,
    lens: *const u32,
    perms: *const u32,
    addr: u32,
    req_perm: u32,
) -> i32 {
    let req_ok = ((req_perm != 0) & ((req_perm & !PERM_MASK) == 0)) as u32;
    // SAFETY: Caller supplies valid 4-element `bases`, `lens`, and `perms` tables.
    unsafe {
        let b = core::ptr::read_unaligned(bases as *const [u32; 4]);
        let l = core::ptr::read_unaligned(lens as *const [u32; 4]);
        let p = core::ptr::read_unaligned(perms as *const [u32; 4]);

        let mut hit = 0u32;
        let mut i = 0usize;
        while i < 4 {
            let in_range = (addr >= b[i]) & (addr.wrapping_sub(b[i]) < l[i]);
            let perm_ok = (p[i] != 0) & ((p[i] & req_perm) == req_perm);
            hit |= (in_range & perm_ok) as u32;
            i += 1;
        }
        (hit & req_ok) as i32
    }
}

/// Explicit Wasm `v128` (`u32x4`) 4-way parallel TLB lookup using `v128_load`, `u32x4_ge`,
/// `i32x4_sub`, `u32x4_lt`, `i32x4_ne`, `i32x4_eq`, and `i32x4_bitmask`.
/// Proved bit-exact equivalent to `tlb_check_4_ref` AND `SliceFrame readonly`.
#[cfg(target_arch = "wasm32")]
#[unsafe(no_mangle)]
pub extern "C" fn tlb_check_4_v128(
    bases: *const u32,
    lens: *const u32,
    perms: *const u32,
    addr: u32,
    req_perm: u32,
) -> i32 {
    if req_perm == 0 || (req_perm & !PERM_MASK) != 0 {
        return 0;
    }
    // SAFETY: Caller satisfies `req_tlb_tables` (16 bytes readable at each pointer).
    unsafe {
        let bv = v128_load(bases as *const v128);
        let lv = v128_load(lens as *const v128);
        let pv = v128_load(perms as *const v128);

        let av = u32x4_splat(addr);
        let rv = u32x4_splat(req_perm);
        let zv = u32x4_splat(0);

        let in_range = v128_and(u32x4_ge(av, bv), u32x4_lt(i32x4_sub(av, bv), lv));
        let perm_ok = v128_and(i32x4_ne(pv, zv), i32x4_eq(v128_and(pv, rv), rv));
        if i32x4_bitmask(v128_and(in_range, perm_ok)) != 0 {
            1
        } else {
            0
        }
    }
}
