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

// Layer-1 Stratum import (`S1.3` bijective 64-bit order-ID mixer).
// Demonstrates Step 1b multi-layer Rust Strata composition (`import "stratum" "order_id_mix"`).
#[link(wasm_import_module = "stratum")]
unsafe extern "C" {
    fn order_id_mix(x: i64) -> i64;
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

// Pre-allocated flat order slab in fixed linear-memory atomic arrays
// (`globals: 0`, zero `__stack_pointer`, zero `.rodata` pointer tables).
static USED: [AtomicI32; 8] = [
    AtomicI32::new(0),
    AtomicI32::new(0),
    AtomicI32::new(0),
    AtomicI32::new(0),
    AtomicI32::new(0),
    AtomicI32::new(0),
    AtomicI32::new(0),
    AtomicI32::new(0),
];

static CL_ORD_ID: [AtomicI64; 8] = [
    AtomicI64::new(0),
    AtomicI64::new(0),
    AtomicI64::new(0),
    AtomicI64::new(0),
    AtomicI64::new(0),
    AtomicI64::new(0),
    AtomicI64::new(0),
    AtomicI64::new(0),
];

static LIVE_COUNT: AtomicI32 = AtomicI32::new(0);
static FREE_COUNT: AtomicI32 = AtomicI32::new(CAP);

#[inline(always)]
fn load_used(idx: i32) -> i32 {
    USED[(idx & MASK) as usize].load(Ordering::Relaxed)
}

#[inline(always)]
fn store_used(idx: i32, v: i32) {
    USED[(idx & MASK) as usize].store(v, Ordering::Relaxed);
}

#[inline(always)]
fn store_id(idx: i32, v: i64) {
    CL_ORD_ID[(idx & MASK) as usize].store(v, Ordering::Relaxed);
}

#[inline(always)]
fn load_live() -> i32 {
    LIVE_COUNT.load(Ordering::Relaxed)
}

#[inline(always)]
fn store_live(v: i32) {
    LIVE_COUNT.store(v, Ordering::Relaxed);
}

#[inline(always)]
fn load_free() -> i32 {
    FREE_COUNT.load(Ordering::Relaxed)
}

#[inline(always)]
fn store_free(v: i32) {
    FREE_COUNT.store(v, Ordering::Relaxed);
}

/// Initialize an empty pre-allocated order slab (`live_count = 0`, `free_count = 8`).
#[unsafe(no_mangle)]
pub extern "C" fn init_slab() {
    USED[0].store(0, Ordering::Relaxed);
    USED[1].store(0, Ordering::Relaxed);
    USED[2].store(0, Ordering::Relaxed);
    USED[3].store(0, Ordering::Relaxed);
    USED[4].store(0, Ordering::Relaxed);
    USED[5].store(0, Ordering::Relaxed);
    USED[6].store(0, Ordering::Relaxed);
    USED[7].store(0, Ordering::Relaxed);

    CL_ORD_ID[0].store(0, Ordering::Relaxed);
    CL_ORD_ID[1].store(0, Ordering::Relaxed);
    CL_ORD_ID[2].store(0, Ordering::Relaxed);
    CL_ORD_ID[3].store(0, Ordering::Relaxed);
    CL_ORD_ID[4].store(0, Ordering::Relaxed);
    CL_ORD_ID[5].store(0, Ordering::Relaxed);
    CL_ORD_ID[6].store(0, Ordering::Relaxed);
    CL_ORD_ID[7].store(0, Ordering::Relaxed);

    store_live(0);
    store_free(CAP);
}

/// Self-contained open-addressing insert starting at `start_bucket & 7`.
/// Rejects `cl_ord_id == 0`, rejects duplicate `cl_ord_id`, and returns allocated slot `0..=7`
/// or `-1` if full or duplicate.
#[unsafe(no_mangle)]
pub extern "C" fn slab_insert_at(cl_ord_id: i64, start_bucket: i32) -> i32 {
    if cl_ord_id == 0 {
        return -1;
    }
    let live = load_live();
    let free = load_free();
    if free <= 0 || live >= CAP {
        return -1;
    }

    // Load all 8 occupancy flags & keys once from fixed slots.
    let u0 = USED[0].load(Ordering::Relaxed);
    let u1 = USED[1].load(Ordering::Relaxed);
    let u2 = USED[2].load(Ordering::Relaxed);
    let u3 = USED[3].load(Ordering::Relaxed);
    let u4 = USED[4].load(Ordering::Relaxed);
    let u5 = USED[5].load(Ordering::Relaxed);
    let u6 = USED[6].load(Ordering::Relaxed);
    let u7 = USED[7].load(Ordering::Relaxed);

    if (u0 != 0 && CL_ORD_ID[0].load(Ordering::Relaxed) == cl_ord_id)
        || (u1 != 0 && CL_ORD_ID[1].load(Ordering::Relaxed) == cl_ord_id)
        || (u2 != 0 && CL_ORD_ID[2].load(Ordering::Relaxed) == cl_ord_id)
        || (u3 != 0 && CL_ORD_ID[3].load(Ordering::Relaxed) == cl_ord_id)
        || (u4 != 0 && CL_ORD_ID[4].load(Ordering::Relaxed) == cl_ord_id)
        || (u5 != 0 && CL_ORD_ID[5].load(Ordering::Relaxed) == cl_ord_id)
        || (u6 != 0 && CL_ORD_ID[6].load(Ordering::Relaxed) == cl_ord_id)
        || (u7 != 0 && CL_ORD_ID[7].load(Ordering::Relaxed) == cl_ord_id)
    {
        return -1;
    }

    // Pack free-slot bitmask (bit i == 1 iff slot i is free) and linear-probe from `start_bucket & 7`.
    let free_mask: u32 = ((u0 == 0) as u32)
        | (((u1 == 0) as u32) << 1)
        | (((u2 == 0) as u32) << 2)
        | (((u3 == 0) as u32) << 3)
        | (((u4 == 0) as u32) << 4)
        | (((u5 == 0) as u32) << 5)
        | (((u6 == 0) as u32) << 6)
        | (((u7 == 0) as u32) << 7);

    if free_mask == 0 {
        return -1;
    }

    // Rotate 8-bit free mask right by `start = start_bucket & 7`, take trailing_zeros = probe distance.
    let start = (start_bucket & MASK) as u32;
    let rotated = ((free_mask | (free_mask << 8)) >> start) & 0xFF;
    let step = rotated.trailing_zeros();
    let slot = ((start + step) & 7) as i32;

    store_used(slot, 1);
    store_id(slot, cl_ord_id);
    store_live(live.wrapping_add(1));
    store_free(free.wrapping_sub(1));
    slot
}

/// Self-contained open-addressing lookup starting at `start_bucket & 7`.
/// Returns slot index `0..=7` if found, or `-1` otherwise.
#[unsafe(no_mangle)]
pub extern "C" fn slab_lookup_at(cl_ord_id: i64, start_bucket: i32) -> i32 {
    if cl_ord_id == 0 {
        return -1;
    }
    let m0 = (USED[0].load(Ordering::Relaxed) != 0 && CL_ORD_ID[0].load(Ordering::Relaxed) == cl_ord_id) as u32;
    let m1 = (USED[1].load(Ordering::Relaxed) != 0 && CL_ORD_ID[1].load(Ordering::Relaxed) == cl_ord_id) as u32;
    let m2 = (USED[2].load(Ordering::Relaxed) != 0 && CL_ORD_ID[2].load(Ordering::Relaxed) == cl_ord_id) as u32;
    let m3 = (USED[3].load(Ordering::Relaxed) != 0 && CL_ORD_ID[3].load(Ordering::Relaxed) == cl_ord_id) as u32;
    let m4 = (USED[4].load(Ordering::Relaxed) != 0 && CL_ORD_ID[4].load(Ordering::Relaxed) == cl_ord_id) as u32;
    let m5 = (USED[5].load(Ordering::Relaxed) != 0 && CL_ORD_ID[5].load(Ordering::Relaxed) == cl_ord_id) as u32;
    let m6 = (USED[6].load(Ordering::Relaxed) != 0 && CL_ORD_ID[6].load(Ordering::Relaxed) == cl_ord_id) as u32;
    let m7 = (USED[7].load(Ordering::Relaxed) != 0 && CL_ORD_ID[7].load(Ordering::Relaxed) == cl_ord_id) as u32;

    let match_mask: u32 =
        m0 | (m1 << 1) | (m2 << 2) | (m3 << 3) | (m4 << 4) | (m5 << 5) | (m6 << 6) | (m7 << 7);
    if match_mask == 0 {
        return -1;
    }
    let start = (start_bucket & MASK) as u32;
    let rotated = ((match_mask | (match_mask << 8)) >> start) & 0xFF;
    let step = rotated.trailing_zeros();
    ((start + step) & 7) as i32
}

/// Layer-2 open-addressing slab insert using Layer-1 Stratum `stratum::order_id_mix`.
#[unsafe(no_mangle)]
pub extern "C" fn slab_insert(cl_ord_id: i64) -> i32 {
    if cl_ord_id == 0 {
        return -1;
    }
    let bucket = (unsafe { order_id_mix(cl_ord_id) } as i32) & MASK;
    slab_insert_at(cl_ord_id, bucket)
}

/// Layer-2 open-addressing slab lookup using Layer-1 Stratum `stratum::order_id_mix`.
#[unsafe(no_mangle)]
pub extern "C" fn slab_lookup(cl_ord_id: i64) -> i32 {
    if cl_ord_id == 0 {
        return -1;
    }
    let bucket = (unsafe { order_id_mix(cl_ord_id) } as i32) & MASK;
    slab_lookup_at(cl_ord_id, bucket)
}

/// Free an active slab slot `0..=7`.
/// Returns `1` on valid release, or `0` (no-op) on out-of-range slot or already-free slot.
#[unsafe(no_mangle)]
pub extern "C" fn slab_free(slot: i32) -> i32 {
    if slot < 0 || slot >= CAP {
        return 0;
    }
    if load_used(slot) == 0 {
        return 0;
    }
    let live = load_live();
    let free = load_free();
    if live <= 0 || free >= CAP {
        return 0;
    }
    store_used(slot, 0);
    store_id(slot, 0);
    store_live(live.wrapping_sub(1));
    store_free(free.wrapping_add(1));
    1
}

#[inline(always)]
fn slot_ok(u: i32, id: i64) -> bool {
    (u == 1 && id != 0) || (u == 0 && id == 0)
}

#[inline(always)]
fn pair_distinct(ua: i32, ida: i64, ub: i32, idb: i64) -> bool {
    ua == 0 || ub == 0 || ida != idb
}

/// Full inductive state invariant `inv_slab() -> i32`:
/// 1. `live_count >= 0 && free_count >= 0 && live_count + free_count == 8`
/// 2. Every slot has `used[i] in {0, 1}`, active slots have `cl_ord_id[i] != 0`,
///    free slots have `cl_ord_id[i] == 0`
/// 3. `live_count == popcount(used[0..8])`
/// 4. Pairwise unique `cl_ord_id` across all 28 active slot pairs `(i < j)`.
#[unsafe(no_mangle)]
pub extern "C" fn inv_slab() -> i32 {
    let live = load_live();
    let free = load_free();
    if live < 0 || free < 0 || live > CAP || free > CAP || live.wrapping_add(free) != CAP {
        return 0;
    }

    let u0 = USED[0].load(Ordering::Relaxed);
    let u1 = USED[1].load(Ordering::Relaxed);
    let u2 = USED[2].load(Ordering::Relaxed);
    let u3 = USED[3].load(Ordering::Relaxed);
    let u4 = USED[4].load(Ordering::Relaxed);
    let u5 = USED[5].load(Ordering::Relaxed);
    let u6 = USED[6].load(Ordering::Relaxed);
    let u7 = USED[7].load(Ordering::Relaxed);

    let k0 = CL_ORD_ID[0].load(Ordering::Relaxed);
    let k1 = CL_ORD_ID[1].load(Ordering::Relaxed);
    let k2 = CL_ORD_ID[2].load(Ordering::Relaxed);
    let k3 = CL_ORD_ID[3].load(Ordering::Relaxed);
    let k4 = CL_ORD_ID[4].load(Ordering::Relaxed);
    let k5 = CL_ORD_ID[5].load(Ordering::Relaxed);
    let k6 = CL_ORD_ID[6].load(Ordering::Relaxed);
    let k7 = CL_ORD_ID[7].load(Ordering::Relaxed);

    if !(slot_ok(u0, k0)
        && slot_ok(u1, k1)
        && slot_ok(u2, k2)
        && slot_ok(u3, k3)
        && slot_ok(u4, k4)
        && slot_ok(u5, k5)
        && slot_ok(u6, k6)
        && slot_ok(u7, k7))
    {
        return 0;
    }

    let pop = u0 + u1 + u2 + u3 + u4 + u5 + u6 + u7;
    if live != pop {
        return 0;
    }

    let unique = pair_distinct(u0, k0, u1, k1)
        && pair_distinct(u0, k0, u2, k2)
        && pair_distinct(u0, k0, u3, k3)
        && pair_distinct(u0, k0, u4, k4)
        && pair_distinct(u0, k0, u5, k5)
        && pair_distinct(u0, k0, u6, k6)
        && pair_distinct(u0, k0, u7, k7)
        && pair_distinct(u1, k1, u2, k2)
        && pair_distinct(u1, k1, u3, k3)
        && pair_distinct(u1, k1, u4, k4)
        && pair_distinct(u1, k1, u5, k5)
        && pair_distinct(u1, k1, u6, k6)
        && pair_distinct(u1, k1, u7, k7)
        && pair_distinct(u2, k2, u3, k3)
        && pair_distinct(u2, k2, u4, k4)
        && pair_distinct(u2, k2, u5, k5)
        && pair_distinct(u2, k2, u6, k6)
        && pair_distinct(u2, k2, u7, k7)
        && pair_distinct(u3, k3, u4, k4)
        && pair_distinct(u3, k3, u5, k5)
        && pair_distinct(u3, k3, u6, k6)
        && pair_distinct(u3, k3, u7, k7)
        && pair_distinct(u4, k4, u5, k5)
        && pair_distinct(u4, k4, u6, k6)
        && pair_distinct(u4, k4, u7, k7)
        && pair_distinct(u5, k5, u6, k6)
        && pair_distinct(u5, k5, u7, k7)
        && pair_distinct(u6, k6, u7, k7);

    if unique { 1 } else { 0 }
}

/// Inline relational contract (Strata-composed via `stratum::order_id_mix`):
/// Proves that inserting a fresh non-zero `cl_ord_id` into a non-full slab succeeds,
/// `slab_lookup` recovers the exact allocated slot, `slab_free` releases it cleanly,
/// and `inv_slab()` is preserved throughout.
#[unsafe(no_mangle)]
pub extern "C" fn contract_insert_lookup_free_roundtrip(cl_ord_id: i64) -> i32 {
    assume(inv_slab() != 0);
    assume(cl_ord_id != 0);
    assume(load_free() > 0);
    assume(slab_lookup(cl_ord_id) < 0);

    let live0 = load_live();
    let slot = slab_insert(cl_ord_id);
    assert_prop(slot >= 0 && slot < CAP);
    assert_prop(load_live() == live0.wrapping_add(1));
    assert_prop(slab_lookup(cl_ord_id) == slot);

    let freed = slab_free(slot);
    assert_prop(freed == 1);
    assert_prop(load_live() == live0);
    assert_prop(slab_lookup(cl_ord_id) == -1);
    assert_prop(inv_slab() != 0);
    1
}

/// Self-contained inline relational contract (arbitrary symbolic `bucket`):
/// Proves the same insert/lookup/free round-trip for ANY starting bucket `0..=7`.
#[unsafe(no_mangle)]
pub extern "C" fn contract_insert_lookup_free_at_roundtrip(cl_ord_id: i64, bucket: i32) -> i32 {
    assume(inv_slab() != 0);
    assume(cl_ord_id != 0);
    assume(load_free() > 0);
    assume(slab_lookup_at(cl_ord_id, bucket) < 0);

    let live0 = load_live();
    let slot = slab_insert_at(cl_ord_id, bucket);
    assert_prop(slot >= 0 && slot < CAP);
    assert_prop(load_live() == live0.wrapping_add(1));
    assert_prop(slab_lookup_at(cl_ord_id, bucket) == slot);

    let freed = slab_free(slot);
    assert_prop(freed == 1);
    assert_prop(load_live() == live0);
    assert_prop(slab_lookup_at(cl_ord_id, bucket) == -1);
    assert_prop(inv_slab() != 0);
    1
}

/// Inline relational contract:
/// Proves double-free on an already-free slot is rejected and preserves counts & `inv_slab()`.
#[unsafe(no_mangle)]
pub extern "C" fn contract_double_free_rejected(slot: i32) -> i32 {
    assume(inv_slab() != 0);
    assume(slot >= 0 && slot < CAP);
    assume(load_used(slot) == 0);
    let live0 = load_live();
    let free0 = load_free();

    let ok = slab_free(slot);
    assert_prop(ok == 0);
    assert_prop(load_live() == live0);
    assert_prop(load_free() == free0);
    assert_prop(inv_slab() != 0);
    1
}
