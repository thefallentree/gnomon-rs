#![no_std]

//! Vertical Pack 7 Buggy Mutants — OS Kernel / Hypervisor `W^X` MMU & Vectorized TLB
//!
//! 1. `map_region_buggy_wrap_overlap`: classic `mmap`/VMA integer-overflow CVE! Computes
//!    `end = base.wrapping_add(len)` without guarding `base + len` overflow. When `base + len`
//!    wraps past `2^32`, `end <= other_base` falsely passes overlap checks, violating `inv_mmu_wx`!
//! 2. `mprotect_buggy_wx_escalation`: classic `mprotect` `W^X` privilege escalation bug!
//!    Allows setting `PERM_WRITE | PERM_EXEC` (`RWX`) on an active region — caught by BOTH the
//!    inductive suite AND global virtual-address `contract_no_wx_escalation`!
//! 3. `tlb_check_4_buggy_signed_cmp`: classic signed-vs-unsigned address comparison bug
//!    (`(addr as i32) >= (b as i32)`) failing on high-half virtual addresses `>= 0x8000_0000`!

use core::sync::atomic::{AtomicU32, Ordering};

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

const PERM_READ: u32 = 1;
const PERM_WRITE: u32 = 2;
const PERM_EXEC: u32 = 4;
const PERM_MASK: u32 = PERM_READ | PERM_WRITE | PERM_EXEC;
const PERM_WX: u32 = PERM_WRITE | PERM_EXEC;
const PAGE_MASK: u32 = 0x0FFF;
const ADDR_LIMIT: u32 = 0xFFFF_F000;

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

#[inline(always)]
fn load_slot(a: &AtomicU32) -> u32 {
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

#[unsafe(no_mangle)]
pub extern "C" fn inv_mmu_wx() -> i32 {
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

/// Buggy Mutant 1: omits `base <= ADDR_LIMIT && len <= ADDR_LIMIT - base` overflow check!
/// `base + len` wraps modulo `2^32`, passing `pair_disjoint` while violating `inv_mmu_wx`!
#[unsafe(no_mangle)]
pub extern "C" fn map_region_buggy_wrap_overlap(slot: i32, base: u32, len: u32, perm: u32) -> i32 {
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

    // BUG: forgets `base <= ADDR_LIMIT && len <= ADDR_LIMIT - base` wraparound guard!
    let valid_new =
        perm_valid_wx(perm) & ((base & PAGE_MASK) == 0) & ((len & PAGE_MASK) == 0) & (len > 0);

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

/// Buggy Mutant 2: omits the `W^X` exclusion check in `mprotect`, allowing `RWX` escalation!
#[unsafe(no_mangle)]
pub extern "C" fn mprotect_buggy_wx_escalation(slot: i32, new_perm: u32) -> i32 {
    let perms = PERM.load(Ordering::Relaxed);
    let shift = ((slot & 3) as u32) * 8;
    let cur_p = (perms >> shift) & 0xFF;

    // BUG: checks `new_perm in 1..=7` but forgets `(new_perm & PERM_WX) != PERM_WX`!
    let ok =
        (slot >= 0) & (slot < 4) & (cur_p != 0) & (new_perm != 0) & ((new_perm & !PERM_MASK) == 0);
    if !ok {
        return 0;
    }

    let next_perms = (perms & !(0xFFu32 << shift)) | (new_perm << shift);
    PERM.store(next_perms, Ordering::Relaxed);
    1
}

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

/// Inline contract catching `W^X` escalation on `mprotect_buggy_wx_escalation` (`FALSIFIED`).
#[unsafe(no_mangle)]
pub extern "C" fn contract_no_wx_escalation(slot: i32, new_perm: u32, addr: u32) -> i32 {
    assume(inv_mmu_wx() == 1);
    let _r = mprotect_buggy_wx_escalation(slot, new_perm);
    let can_w = mmu_check_access(addr, PERM_WRITE);
    let can_x = mmu_check_access(addr, PERM_EXEC);
    assert_prop(!(can_w == 1 && can_x == 1));
    1
}

/// Buggy Mutant 3: signed address comparison (`(addr as i32) >= (b as i32)`) fails on
/// high-half virtual addresses (`>= 0x8000_0000`)!
#[unsafe(no_mangle)]
pub extern "C" fn tlb_check_4_buggy_signed_cmp(
    bases: *const u32,
    lens: *const u32,
    perms: *const u32,
    addr: u32,
    req_perm: u32,
) -> i32 {
    let req_ok = ((req_perm != 0) & ((req_perm & !PERM_MASK) == 0)) as u32;
    unsafe {
        let b = core::ptr::read_unaligned(bases as *const [u32; 4]);
        let l = core::ptr::read_unaligned(lens as *const [u32; 4]);
        let p = core::ptr::read_unaligned(perms as *const [u32; 4]);

        let mut hit = 0u32;
        let mut i = 0usize;
        while i < 4 {
            // BUG: signed comparison `(addr as i32) >= (b[i] as i32)` breaks at `0x8000_0000`!
            let in_range = ((addr as i32) >= (b[i] as i32)) & (addr.wrapping_sub(b[i]) < l[i]);
            let perm_ok = (p[i] != 0) & ((p[i] & req_perm) == req_perm);
            hit |= (in_range & perm_ok) as u32;
            i += 1;
        }
        (hit & req_ok) as i32
    }
}
