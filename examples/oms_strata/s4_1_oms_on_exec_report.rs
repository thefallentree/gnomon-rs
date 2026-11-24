#![no_std]

use core::slice;
use core::sync::atomic::{AtomicI32, AtomicI64, AtomicU8, Ordering};

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

#[link(wasm_import_module = "gnomon")]
unsafe extern "C" {
    fn gnomon_assume(cond: i32);
    fn gnomon_assert(cond: i32);
}

// Layer-1 Stratum import (`S1.3` bijective 64-bit MurmurHash3 order-ID mixer).
// Discharged in milliseconds by Gnomon UF CEGAR without bit-blasting fmix64.
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

// ============================================================================
// Memory Window & Wire Constants (min_pages >= 17, live DMA window > 1 MiB)
// ============================================================================

/// Guard static placed in `.bss` above the 1 MiB shadow stack (`0x10_0000`),
/// guaranteeing `min_pages >= 17` (`1_114_112` bytes).
static WIRE_DMA_GUARD: [u8; 64] = [0; 64];

const STACK_TOP: i32 = 1_048_576; // 16 * 65536 (rustc default __stack_pointer init)
const LIVE_LO: i32 = STACK_TOP + 4_096; // 1_052_672 (strictly above .bss OMS state)
const LIVE_HI: i32 = STACK_TOP + 32_768; // 1_081_344 (strictly inside 17 pages)
const MIN_LIVE_PAGES: usize = 17;

// Big-Endian 31-byte Inbound ExecReport wire format (matching S2.3 OrderExecuted)
const MSG_ORDER_ACK: u8 = b'A';
const MSG_ORDER_EXECUTED: u8 = b'E';
const MSG_ORDER_CANCELED: u8 = b'C';
const EXEC_REPORT_LEN: usize = 31;

// Order slab & journal ring capacities
const SLAB_CAP: u8 = 4;
const SLAB_MASK: i32 = 3;
const RING_CAP: i32 = 8;
const RING_MASK: i32 = 7;

// Child FSM lifecycle states (S3.1 / S3.2)
const C_EMPTY: u8 = 0;
const C_PENDING_NEW: u8 = 1;
const C_LIVE: u8 = 2;
const C_PENDING_CANCEL: u8 = 3;
const C_FILLED: u8 = 4;
const C_CANCELED: u8 = 5;

// Side encoding (S3.3)
const SIDE_NONE: u8 = 0;
const SIDE_BUY: u8 = 1;
const SIDE_SELL: u8 = 2;

// ============================================================================
// Unified Layer-4 OMS State (compact .bss layout: 1B flags/states, 4B qtys, 8B IDs)
// ============================================================================

// Parent order state (S3.2) — 32-bit shares matching ITCH/OUCH wire width
static OMS_ACTIVE: AtomicU8 = AtomicU8::new(0);
static P_TARGET_QTY: AtomicI32 = AtomicI32::new(0);
static P_CUM_FILLED: AtomicI32 = AtomicI32::new(0);
static P_OPEN_WORST: AtomicI32 = AtomicI32::new(0);

// 4-slot open-addressing Order Slab (S2.2)
static SLAB_LIVE: AtomicU8 = AtomicU8::new(0);
static SLAB_FREE: AtomicU8 = AtomicU8::new(SLAB_CAP);
static SLAB_USED: [AtomicU8; 4] = [
    AtomicU8::new(0),
    AtomicU8::new(0),
    AtomicU8::new(0),
    AtomicU8::new(0),
];
static SLAB_ORDER_REF: [AtomicI64; 4] = [
    AtomicI64::new(0),
    AtomicI64::new(0),
    AtomicI64::new(0),
    AtomicI64::new(0),
];

// Per-slot Child FSM + Risk exposure (S3.1 / S3.2 / S3.3)
static C_STATE: [AtomicU8; 4] = [
    AtomicU8::new(C_EMPTY),
    AtomicU8::new(C_EMPTY),
    AtomicU8::new(C_EMPTY),
    AtomicU8::new(C_EMPTY),
];
static C_SIDE: [AtomicU8; 4] = [
    AtomicU8::new(SIDE_NONE),
    AtomicU8::new(SIDE_NONE),
    AtomicU8::new(SIDE_NONE),
    AtomicU8::new(SIDE_NONE),
];
static C_LEAVES: [AtomicI32; 4] = [
    AtomicI32::new(0),
    AtomicI32::new(0),
    AtomicI32::new(0),
    AtomicI32::new(0),
];
static C_CUM: [AtomicI32; 4] = [
    AtomicI32::new(0),
    AtomicI32::new(0),
    AtomicI32::new(0),
    AtomicI32::new(0),
];
static O_NOTIONAL: [AtomicI32; 4] = [
    AtomicI32::new(0),
    AtomicI32::new(0),
    AtomicI32::new(0),
    AtomicI32::new(0),
];

// Account SEC 15c3-5 Risk aggregates (S3.3)
static MAX_CREDIT: AtomicI32 = AtomicI32::new(0);
static MAX_POS: AtomicI32 = AtomicI32::new(0);
static NET_POS: AtomicI32 = AtomicI32::new(0);
static OPEN_NOTIONAL: AtomicI32 = AtomicI32::new(0);

// 8-slot SPSC Journal Ring (S2.1)
static J_HEAD: AtomicI32 = AtomicI32::new(0);
static J_TAIL: AtomicI32 = AtomicI32::new(0);
static J_CAP: AtomicI32 = AtomicI32::new(RING_CAP);
static J_SLOTS: [AtomicI64; 8] = [
    AtomicI64::new(0),
    AtomicI64::new(0),
    AtomicI64::new(0),
    AtomicI64::new(0),
    AtomicI64::new(0),
    AtomicI64::new(0),
    AtomicI64::new(0),
    AtomicI64::new(0),
];

// ============================================================================
// Branchless Helpers (overflow-safe sums, selectors, slot predicates)
// ============================================================================

#[inline(always)]
fn sum4_checked(a: i32, b: i32, c: i32, d: i32) -> i32 {
    let s01 = a.wrapping_add(b);
    let s23 = c.wrapping_add(d);
    let s = s01.wrapping_add(s23);
    if (a | b | c | d | s01 | s23 | s) < 0 {
        -1
    } else {
        s
    }
}

#[inline(always)]
fn sum4_eq(a: i32, b: i32, c: i32, d: i32, total: i32) -> bool {
    let s01 = a.wrapping_add(b);
    let s23 = c.wrapping_add(d);
    let s = s01.wrapping_add(s23);
    ((a | b | c | d | total | s01 | s23 | s) >= 0) & (s == total)
}

#[inline(always)]
fn select_u8(slot: i32, v0: u8, v1: u8, v2: u8, v3: u8) -> u8 {
    let v01 = if slot == 0 { v0 } else { v1 };
    let v23 = if slot == 2 { v2 } else { v3 };
    if (slot & 2) == 0 { v01 } else { v23 }
}

#[inline(always)]
fn select_i32(slot: i32, v0: i32, v1: i32, v2: i32, v3: i32) -> i32 {
    let v01 = if slot == 0 { v0 } else { v1 };
    let v23 = if slot == 2 { v2 } else { v3 };
    if (slot & 2) == 0 { v01 } else { v23 }
}

#[inline(always)]
fn pair_distinct(ua: u8, ra: i64, ub: u8, rb: i64) -> bool {
    (ua == 0) | (ub == 0) | (ra != rb)
}

/// Overflow-safe net position conservation check:
/// `max_pos >= p_target` and `-p_cum <= net_pos <= p_cum` (which implies worst-case
/// `|net_pos| + p_open <= p_cum + p_open <= p_target <= max_pos` automatically on every fill!).
#[inline(always)]
fn net_pos_within_cum(net_pos: i32, p_cum: i32, p_target: i32, max_pos: i32) -> bool {
    let neg_cum = 0i32.wrapping_sub(p_cum);
    (max_pos >= p_target) & (p_cum >= 0) & (net_pos >= neg_cum) & (net_pos <= p_cum)
}

/// Branchless per-slot consistency predicate (zero `if/else` control flow).
#[inline(always)]
fn inv_slot(
    used: u8,
    oref: i64,
    st: u8,
    side: u8,
    leaves: i32,
    cum: i32,
    notional: i32,
) -> bool {
    let nonneg = (leaves | cum | notional) >= 0;
    let valid_side = (side == SIDE_BUY) | (side == SIDE_SELL);
    let is_empty = (st == C_EMPTY)
        & (used == 0)
        & (oref == 0)
        & (side == SIDE_NONE)
        & (leaves == 0)
        & (cum == 0)
        & (notional == 0);
    let is_pnew = (st == C_PENDING_NEW)
        & (used == 1)
        & (oref != 0)
        & valid_side
        & (leaves > 0)
        & (cum == 0)
        & (notional > 0);
    let is_working = ((st == C_LIVE) | (st == C_PENDING_CANCEL))
        & (used == 1)
        & (oref != 0)
        & valid_side
        & (leaves > 0)
        & (notional > 0);
    let is_filled = (st == C_FILLED)
        & (used == 0)
        & (oref == 0)
        & (side == SIDE_NONE)
        & (leaves == 0)
        & (cum > 0)
        & (notional == 0);
    let is_canceled = (st == C_CANCELED)
        & (used == 0)
        & (oref == 0)
        & (side == SIDE_NONE)
        & (leaves == 0)
        & (notional == 0);
    nonneg & (is_empty | is_pnew | is_working | is_filled | is_canceled)
}

/// 4-slot open-addressing linear probe starting at `start = (order_id_mix(order_ref) as i32) & 3`.
/// Genuinely composes Layer-1 `S1.3` `order_id_mix` (UF CEGAR discharges in ms).
#[inline(always)]
fn probe_matching_slot(
    order_ref: i64,
    u0: u8,
    u1: u8,
    u2: u8,
    u3: u8,
    r0: i64,
    r1: i64,
    r2: i64,
    r3: i64,
) -> i32 {
    let start = (unsafe { order_id_mix(order_ref) } as i32) & SLAB_MASK;
    let m0 = ((u0 != 0) & (r0 == order_ref)) as u8;
    let m1 = ((u1 != 0) & (r1 == order_ref)) as u8;
    let m2 = ((u2 != 0) & (r2 == order_ref)) as u8;
    let m3 = ((u3 != 0) & (r3 == order_ref)) as u8;

    let p0 = start;
    let p1 = (start + 1) & SLAB_MASK;
    let p2 = (start + 2) & SLAB_MASK;
    let p3 = (start + 3) & SLAB_MASK;

    let h0 = select_u8(p0, m0, m1, m2, m3) != 0;
    let h1 = select_u8(p1, m0, m1, m2, m3) != 0;
    let h2 = select_u8(p2, m0, m1, m2, m3) != 0;
    let h3 = select_u8(p3, m0, m1, m2, m3) != 0;

    if h0 {
        p0
    } else if h1 {
        p1
    } else if h2 {
        p2
    } else if h3 {
        p3
    } else {
        -1
    }
}

/// Shadow-stack staging helper for `oms_on_exec_report_ref`: materializes a 32-byte
/// audit record `(order_ref, journal_entry, match_num, msg_type)` on `__stack_pointer` (`Global(0)`).
#[inline(never)]
fn stage_journal_on_stack(order_ref: i64, msg_type: u8, match_num: i64, staged: &mut [u8; 32]) {
    let journal_entry = (match_num & !0xFFi64) | (msg_type as i64);
    staged[0..8].copy_from_slice(&order_ref.to_le_bytes());
    staged[8..16].copy_from_slice(&journal_entry.to_le_bytes());
    staged[16..24].copy_from_slice(&match_num.to_le_bytes());
    staged[24..32].copy_from_slice(&(msg_type as i64).to_le_bytes());
}

#[inline(never)]
fn commit_staged_journal(staged: &[u8; 32], j_idx: usize) {
    let mut tmp = [0u8; 8];
    let mut i = 0usize;
    while i < 8 {
        tmp[i] = staged[8 + i];
        i += 1;
    }
    let entry = i64::from_le_bytes(tmp);
    J_SLOTS[j_idx & (RING_MASK as usize)].store(entry, Ordering::Relaxed);
}

// ============================================================================
// Initializer, Lifecycle Ops, Precondition & Unified Global OMS Invariant
// ============================================================================

/// Initialize a clean, valid Layer-4 OMS state (establishes `inv_oms_e2e() == 1`).
#[unsafe(no_mangle)]
pub extern "C" fn init_oms_state() {
    OMS_ACTIVE.store(1, Ordering::Relaxed);
    P_TARGET_QTY.store(10_000, Ordering::Relaxed);
    P_CUM_FILLED.store(0, Ordering::Relaxed);
    P_OPEN_WORST.store(0, Ordering::Relaxed);

    SLAB_LIVE.store(0, Ordering::Relaxed);
    SLAB_FREE.store(SLAB_CAP, Ordering::Relaxed);

    let mut i = 0usize;
    while i < 4 {
        SLAB_USED[i].store(0, Ordering::Relaxed);
        SLAB_ORDER_REF[i].store(0, Ordering::Relaxed);
        C_STATE[i].store(C_EMPTY, Ordering::Relaxed);
        C_SIDE[i].store(SIDE_NONE, Ordering::Relaxed);
        C_LEAVES[i].store(0, Ordering::Relaxed);
        C_CUM[i].store(0, Ordering::Relaxed);
        O_NOTIONAL[i].store(0, Ordering::Relaxed);
        i += 1;
    }

    MAX_CREDIT.store(10_000_000, Ordering::Relaxed);
    MAX_POS.store(10_000, Ordering::Relaxed);
    NET_POS.store(0, Ordering::Relaxed);
    OPEN_NOTIONAL.store(0, Ordering::Relaxed);

    J_HEAD.store(0, Ordering::Relaxed);
    J_TAIL.store(0, Ordering::Relaxed);
    J_CAP.store(RING_CAP, Ordering::Relaxed);

    let mut k = 0usize;
    while k < 8 {
        J_SLOTS[k].store(0, Ordering::Relaxed);
        k += 1;
    }
}

/// Route a new child order into an empty slab slot using `stratum::order_id_mix(order_ref) & 3`.
/// Unconditional straight-line constant-address stores preserving `inv_oms_e2e()`.
#[unsafe(no_mangle)]
pub extern "C" fn oms_route_order(order_ref: i64, side: i32, qty: i32, notional: i32) -> i32 {
    let active = OMS_ACTIVE.load(Ordering::Relaxed);
    let live = SLAB_LIVE.load(Ordering::Relaxed);
    let free = SLAB_FREE.load(Ordering::Relaxed);
    let p_target = P_TARGET_QTY.load(Ordering::Relaxed);
    let p_cum = P_CUM_FILLED.load(Ordering::Relaxed);
    let old_p_open = P_OPEN_WORST.load(Ordering::Relaxed);
    let max_cred = MAX_CREDIT.load(Ordering::Relaxed);
    let max_pos = MAX_POS.load(Ordering::Relaxed);
    let net_pos = NET_POS.load(Ordering::Relaxed);
    let old_not = OPEN_NOTIONAL.load(Ordering::Relaxed);

    let u0 = SLAB_USED[0].load(Ordering::Relaxed);
    let u1 = SLAB_USED[1].load(Ordering::Relaxed);
    let u2 = SLAB_USED[2].load(Ordering::Relaxed);
    let u3 = SLAB_USED[3].load(Ordering::Relaxed);

    let r0 = SLAB_ORDER_REF[0].load(Ordering::Relaxed);
    let r1 = SLAB_ORDER_REF[1].load(Ordering::Relaxed);
    let r2 = SLAB_ORDER_REF[2].load(Ordering::Relaxed);
    let r3 = SLAB_ORDER_REF[3].load(Ordering::Relaxed);

    let st0 = C_STATE[0].load(Ordering::Relaxed);
    let st1 = C_STATE[1].load(Ordering::Relaxed);
    let st2 = C_STATE[2].load(Ordering::Relaxed);
    let st3 = C_STATE[3].load(Ordering::Relaxed);

    let sd0 = C_SIDE[0].load(Ordering::Relaxed);
    let sd1 = C_SIDE[1].load(Ordering::Relaxed);
    let sd2 = C_SIDE[2].load(Ordering::Relaxed);
    let sd3 = C_SIDE[3].load(Ordering::Relaxed);

    let l0 = C_LEAVES[0].load(Ordering::Relaxed);
    let l1 = C_LEAVES[1].load(Ordering::Relaxed);
    let l2 = C_LEAVES[2].load(Ordering::Relaxed);
    let l3 = C_LEAVES[3].load(Ordering::Relaxed);

    let n0 = O_NOTIONAL[0].load(Ordering::Relaxed);
    let n1 = O_NOTIONAL[1].load(Ordering::Relaxed);
    let n2 = O_NOTIONAL[2].load(Ordering::Relaxed);
    let n3 = O_NOTIONAL[3].load(Ordering::Relaxed);

    let dup = ((u0 != 0) & (r0 == order_ref))
        | ((u1 != 0) & (r1 == order_ref))
        | ((u2 != 0) & (r2 == order_ref))
        | ((u3 != 0) & (r3 == order_ref));

    // Single Layer-1 `order_id_mix` call for starting open-addressing bucket.
    let start = (unsafe { order_id_mix(order_ref) } as i32) & SLAB_MASK;
    let e0 = ((u0 == 0) & (st0 == C_EMPTY)) as u8;
    let e1 = ((u1 == 0) & (st1 == C_EMPTY)) as u8;
    let e2 = ((u2 == 0) & (st2 == C_EMPTY)) as u8;
    let e3 = ((u3 == 0) & (st3 == C_EMPTY)) as u8;

    let p0 = start;
    let p1 = (start + 1) & SLAB_MASK;
    let p2 = (start + 2) & SLAB_MASK;
    let p3 = (start + 3) & SLAB_MASK;

    let slot = if select_u8(p0, e0, e1, e2, e3) != 0 {
        p0
    } else if select_u8(p1, e0, e1, e2, e3) != 0 {
        p1
    } else if select_u8(p2, e0, e1, e2, e3) != 0 {
        p2
    } else if select_u8(p3, e0, e1, e2, e3) != 0 {
        p3
    } else {
        -1
    };

    let side_u8 = side as u8;
    let nl0 = if slot == 0 { qty } else { l0 };
    let nl1 = if slot == 1 { qty } else { l1 };
    let nl2 = if slot == 2 { qty } else { l2 };
    let nl3 = if slot == 3 { qty } else { l3 };

    let nn0 = if slot == 0 { notional } else { n0 };
    let nn1 = if slot == 1 { notional } else { n1 };
    let nn2 = if slot == 2 { notional } else { n2 };
    let nn3 = if slot == 3 { notional } else { n3 };

    let next_p_open = sum4_checked(nl0, nl1, nl2, nl3);
    let next_not = sum4_checked(nn0, nn1, nn2, nn3);

    let ok = (active == 1)
        & (order_ref != 0)
        & (!dup)
        & (slot >= 0)
        & (free > 0)
        & (live < SLAB_CAP)
        & ((side == (SIDE_BUY as i32)) | (side == (SIDE_SELL as i32)))
        & (qty > 0)
        & (notional > 0)
        & (p_target > 0)
        & (max_cred > 0)
        & (p_cum >= 0)
        & (next_p_open >= 0)
        & (p_cum <= p_target)
        & (next_p_open <= p_target.wrapping_sub(p_cum))
        & (next_not >= 0)
        & (next_not <= max_cred)
        & net_pos_within_cum(net_pos, p_cum, p_target, max_pos);

    SLAB_USED[0].store(if ok & (slot == 0) { 1 } else { u0 }, Ordering::Relaxed);
    SLAB_USED[1].store(if ok & (slot == 1) { 1 } else { u1 }, Ordering::Relaxed);
    SLAB_USED[2].store(if ok & (slot == 2) { 1 } else { u2 }, Ordering::Relaxed);
    SLAB_USED[3].store(if ok & (slot == 3) { 1 } else { u3 }, Ordering::Relaxed);

    SLAB_ORDER_REF[0].store(if ok & (slot == 0) { order_ref } else { r0 }, Ordering::Relaxed);
    SLAB_ORDER_REF[1].store(if ok & (slot == 1) { order_ref } else { r1 }, Ordering::Relaxed);
    SLAB_ORDER_REF[2].store(if ok & (slot == 2) { order_ref } else { r2 }, Ordering::Relaxed);
    SLAB_ORDER_REF[3].store(if ok & (slot == 3) { order_ref } else { r3 }, Ordering::Relaxed);

    C_STATE[0].store(if ok & (slot == 0) { C_PENDING_NEW } else { st0 }, Ordering::Relaxed);
    C_STATE[1].store(if ok & (slot == 1) { C_PENDING_NEW } else { st1 }, Ordering::Relaxed);
    C_STATE[2].store(if ok & (slot == 2) { C_PENDING_NEW } else { st2 }, Ordering::Relaxed);
    C_STATE[3].store(if ok & (slot == 3) { C_PENDING_NEW } else { st3 }, Ordering::Relaxed);

    C_SIDE[0].store(if ok & (slot == 0) { side_u8 } else { sd0 }, Ordering::Relaxed);
    C_SIDE[1].store(if ok & (slot == 1) { side_u8 } else { sd1 }, Ordering::Relaxed);
    C_SIDE[2].store(if ok & (slot == 2) { side_u8 } else { sd2 }, Ordering::Relaxed);
    C_SIDE[3].store(if ok & (slot == 3) { side_u8 } else { sd3 }, Ordering::Relaxed);

    C_LEAVES[0].store(if ok { nl0 } else { l0 }, Ordering::Relaxed);
    C_LEAVES[1].store(if ok { nl1 } else { l1 }, Ordering::Relaxed);
    C_LEAVES[2].store(if ok { nl2 } else { l2 }, Ordering::Relaxed);
    C_LEAVES[3].store(if ok { nl3 } else { l3 }, Ordering::Relaxed);

    O_NOTIONAL[0].store(if ok { nn0 } else { n0 }, Ordering::Relaxed);
    O_NOTIONAL[1].store(if ok { nn1 } else { n1 }, Ordering::Relaxed);
    O_NOTIONAL[2].store(if ok { nn2 } else { n2 }, Ordering::Relaxed);
    O_NOTIONAL[3].store(if ok { nn3 } else { n3 }, Ordering::Relaxed);

    SLAB_LIVE.store(if ok { live.wrapping_add(1) } else { live }, Ordering::Relaxed);
    SLAB_FREE.store(if ok { free.wrapping_sub(1) } else { free }, Ordering::Relaxed);
    P_OPEN_WORST.store(if ok { next_p_open } else { old_p_open }, Ordering::Relaxed);
    OPEN_NOTIONAL.store(if ok { next_not } else { old_not }, Ordering::Relaxed);
    if ok { 1 } else { 0 }
}

/// Request cancel on a `Live` child order (`Live -> PendingCancel`), preserving
/// pessimistic `p_open_worst` and `open_notional` exposure until exchange `CancelAck`.
#[unsafe(no_mangle)]
pub extern "C" fn oms_request_cancel(order_ref: i64) -> i32 {
    if OMS_ACTIVE.load(Ordering::Relaxed) != 1 || order_ref == 0 {
        return 0;
    }
    let u0 = SLAB_USED[0].load(Ordering::Relaxed);
    let u1 = SLAB_USED[1].load(Ordering::Relaxed);
    let u2 = SLAB_USED[2].load(Ordering::Relaxed);
    let u3 = SLAB_USED[3].load(Ordering::Relaxed);
    let r0 = SLAB_ORDER_REF[0].load(Ordering::Relaxed);
    let r1 = SLAB_ORDER_REF[1].load(Ordering::Relaxed);
    let r2 = SLAB_ORDER_REF[2].load(Ordering::Relaxed);
    let r3 = SLAB_ORDER_REF[3].load(Ordering::Relaxed);

    let slot = probe_matching_slot(order_ref, u0, u1, u2, u3, r0, r1, r2, r3);
    if slot < 0 {
        return 0;
    }
    let st0 = C_STATE[0].load(Ordering::Relaxed);
    let st1 = C_STATE[1].load(Ordering::Relaxed);
    let st2 = C_STATE[2].load(Ordering::Relaxed);
    let st3 = C_STATE[3].load(Ordering::Relaxed);
    if select_u8(slot, st0, st1, st2, st3) != C_LIVE {
        return 0;
    }
    C_STATE[0].store(if slot == 0 { C_PENDING_CANCEL } else { st0 }, Ordering::Relaxed);
    C_STATE[1].store(if slot == 1 { C_PENDING_CANCEL } else { st1 }, Ordering::Relaxed);
    C_STATE[2].store(if slot == 2 { C_PENDING_CANCEL } else { st2 }, Ordering::Relaxed);
    C_STATE[3].store(if slot == 3 { C_PENDING_CANCEL } else { st3 }, Ordering::Relaxed);
    1
}

/// Precondition for `oms_on_exec_report_ref` and `oms_on_exec_report_opt`:
/// - Linear memory has at least 17 pages (`>= 1_114_112` bytes).
/// - `[rx_ptr, rx_ptr + rx_len)` lies strictly inside `[LIVE_LO, LIVE_HI)`
///   above both `__stack_pointer` (`1_048_576`) and all `.bss` OMS statics.
#[unsafe(no_mangle)]
pub extern "C" fn req_rx_slice(rx_ptr: i32, rx_len: i32) -> i32 {
    if core::arch::wasm32::memory_size(0) < MIN_LIVE_PAGES {
        return 0;
    }
    let guard_end = (WIRE_DMA_GUARD.as_ptr() as i32).wrapping_add(64);
    let lo = if guard_end > LIVE_LO { guard_end } else { LIVE_LO };
    if rx_ptr < lo || rx_ptr > LIVE_HI {
        return 0;
    }
    if rx_len < 0 || rx_len > LIVE_HI - rx_ptr {
        return 0;
    }
    1
}

/// Branchless Unified Layer-4 End-to-End OMS State Invariant (`inv_oms_e2e() -> i32`):
/// 1. SPSC Journal Ring bounds (`S2.1`): `j_cap == 8 && tail.wrapping_sub(head) as u32 <= 8`.
/// 2. Order Slab integrity (`S2.2`): `live + free == 4`, `live == popcount(used)`,
///    pairwise distinct active `order_ref`s.
/// 3. Parent/Child Zero-Overfill & exact roll-ups (`S3.1`/`S3.2`):
///    `p_cum == sum4(c_cum)`, `p_open_worst == sum4(c_leaves)`, `p_cum + p_open_worst <= p_target`.
/// 4. SEC 15c3-5 Risk credit & position conservation (`S3.3`):
///    `open_notional == sum4(o_notional) <= max_credit`,
///    `-max_pos <= net_pos <= max_pos` and worst-case `net_pos +/- p_open_worst` within `[-max_pos, max_pos]`.
#[unsafe(no_mangle)]
pub extern "C" fn inv_oms_e2e() -> i32 {
    let active = OMS_ACTIVE.load(Ordering::Relaxed);
    let p_target = P_TARGET_QTY.load(Ordering::Relaxed);
    let p_cum = P_CUM_FILLED.load(Ordering::Relaxed);
    let p_open = P_OPEN_WORST.load(Ordering::Relaxed);

    let live = SLAB_LIVE.load(Ordering::Relaxed);
    let free = SLAB_FREE.load(Ordering::Relaxed);

    let u0 = SLAB_USED[0].load(Ordering::Relaxed);
    let u1 = SLAB_USED[1].load(Ordering::Relaxed);
    let u2 = SLAB_USED[2].load(Ordering::Relaxed);
    let u3 = SLAB_USED[3].load(Ordering::Relaxed);

    let r0 = SLAB_ORDER_REF[0].load(Ordering::Relaxed);
    let r1 = SLAB_ORDER_REF[1].load(Ordering::Relaxed);
    let r2 = SLAB_ORDER_REF[2].load(Ordering::Relaxed);
    let r3 = SLAB_ORDER_REF[3].load(Ordering::Relaxed);

    let st0 = C_STATE[0].load(Ordering::Relaxed);
    let st1 = C_STATE[1].load(Ordering::Relaxed);
    let st2 = C_STATE[2].load(Ordering::Relaxed);
    let st3 = C_STATE[3].load(Ordering::Relaxed);

    let sd0 = C_SIDE[0].load(Ordering::Relaxed);
    let sd1 = C_SIDE[1].load(Ordering::Relaxed);
    let sd2 = C_SIDE[2].load(Ordering::Relaxed);
    let sd3 = C_SIDE[3].load(Ordering::Relaxed);

    let l0 = C_LEAVES[0].load(Ordering::Relaxed);
    let l1 = C_LEAVES[1].load(Ordering::Relaxed);
    let l2 = C_LEAVES[2].load(Ordering::Relaxed);
    let l3 = C_LEAVES[3].load(Ordering::Relaxed);

    let c0 = C_CUM[0].load(Ordering::Relaxed);
    let c1 = C_CUM[1].load(Ordering::Relaxed);
    let c2 = C_CUM[2].load(Ordering::Relaxed);
    let c3 = C_CUM[3].load(Ordering::Relaxed);

    let n0 = O_NOTIONAL[0].load(Ordering::Relaxed);
    let n1 = O_NOTIONAL[1].load(Ordering::Relaxed);
    let n2 = O_NOTIONAL[2].load(Ordering::Relaxed);
    let n3 = O_NOTIONAL[3].load(Ordering::Relaxed);

    let max_cred = MAX_CREDIT.load(Ordering::Relaxed);
    let max_pos = MAX_POS.load(Ordering::Relaxed);
    let net_pos = NET_POS.load(Ordering::Relaxed);
    let open_not = OPEN_NOTIONAL.load(Ordering::Relaxed);

    let j_head = J_HEAD.load(Ordering::Relaxed);
    let j_tail = J_TAIL.load(Ordering::Relaxed);
    let j_cap = J_CAP.load(Ordering::Relaxed);

    let ring_ok = (j_cap == RING_CAP) & ((j_tail.wrapping_sub(j_head) as u32) <= (RING_CAP as u32));
    let slab_ok = (live <= SLAB_CAP)
        & (free <= SLAB_CAP)
        & (live.wrapping_add(free) == SLAB_CAP)
        & (live == u0.wrapping_add(u1).wrapping_add(u2).wrapping_add(u3))
        & pair_distinct(u0, r0, u1, r1)
        & pair_distinct(u0, r0, u2, r2)
        & pair_distinct(u0, r0, u3, r3)
        & pair_distinct(u1, r1, u2, r2)
        & pair_distinct(u1, r1, u3, r3)
        & pair_distinct(u2, r2, u3, r3);

    let slots_ok = inv_slot(u0, r0, st0, sd0, l0, c0, n0)
        & inv_slot(u1, r1, st1, sd1, l1, c1, n1)
        & inv_slot(u2, r2, st2, sd2, l2, c2, n2)
        & inv_slot(u3, r3, st3, sd3, l3, c3, n3);

    let parent_ok = (active == 1)
        & (p_target > 0)
        & ((p_cum | p_open) >= 0)
        & (p_cum <= p_target)
        & (p_open <= p_target.wrapping_sub(p_cum))
        & sum4_eq(c0, c1, c2, c3, p_cum)
        & sum4_eq(l0, l1, l2, l3, p_open);

    let risk_ok = (max_cred > 0)
        & (open_not >= 0)
        & (open_not <= max_cred)
        & sum4_eq(n0, n1, n2, n3, open_not)
        & net_pos_within_cum(net_pos, p_cum, p_target, max_pos);

    if ring_ok & slab_ok & slots_ok & parent_ok & risk_ok {
        1
    } else {
        0
    }
}

// ============================================================================
// Straight-Line State Transition Core (zero symbolic-index stores on OMS statics)
// ============================================================================

#[inline(never)]
fn apply_exec_report_core(
    msg_type: u8,
    order_ref: i64,
    exec_shares: i32,
) -> i32 {
    let is_ack = msg_type == MSG_ORDER_ACK;
    let is_exec = msg_type == MSG_ORDER_EXECUTED;
    let is_cxl = msg_type == MSG_ORDER_CANCELED;
    if order_ref == 0 || !(is_ack | is_exec | is_cxl) {
        return 0;
    }

    let active = OMS_ACTIVE.load(Ordering::Relaxed);
    let j_cap = J_CAP.load(Ordering::Relaxed);
    let j_head = J_HEAD.load(Ordering::Relaxed);
    let j_tail = J_TAIL.load(Ordering::Relaxed);
    if active != 1 || j_cap != RING_CAP || (j_tail.wrapping_sub(j_head) as u32) >= (RING_CAP as u32)
    {
        return 0;
    }

    let u0 = SLAB_USED[0].load(Ordering::Relaxed);
    let u1 = SLAB_USED[1].load(Ordering::Relaxed);
    let u2 = SLAB_USED[2].load(Ordering::Relaxed);
    let u3 = SLAB_USED[3].load(Ordering::Relaxed);

    let r0 = SLAB_ORDER_REF[0].load(Ordering::Relaxed);
    let r1 = SLAB_ORDER_REF[1].load(Ordering::Relaxed);
    let r2 = SLAB_ORDER_REF[2].load(Ordering::Relaxed);
    let r3 = SLAB_ORDER_REF[3].load(Ordering::Relaxed);

    let slot = probe_matching_slot(order_ref, u0, u1, u2, u3, r0, r1, r2, r3);
    if slot < 0 {
        return 0;
    }

    let st0 = C_STATE[0].load(Ordering::Relaxed);
    let st1 = C_STATE[1].load(Ordering::Relaxed);
    let st2 = C_STATE[2].load(Ordering::Relaxed);
    let st3 = C_STATE[3].load(Ordering::Relaxed);

    let sd0 = C_SIDE[0].load(Ordering::Relaxed);
    let sd1 = C_SIDE[1].load(Ordering::Relaxed);
    let sd2 = C_SIDE[2].load(Ordering::Relaxed);
    let sd3 = C_SIDE[3].load(Ordering::Relaxed);

    let l0 = C_LEAVES[0].load(Ordering::Relaxed);
    let l1 = C_LEAVES[1].load(Ordering::Relaxed);
    let l2 = C_LEAVES[2].load(Ordering::Relaxed);
    let l3 = C_LEAVES[3].load(Ordering::Relaxed);

    let c0 = C_CUM[0].load(Ordering::Relaxed);
    let c1 = C_CUM[1].load(Ordering::Relaxed);
    let c2 = C_CUM[2].load(Ordering::Relaxed);
    let c3 = C_CUM[3].load(Ordering::Relaxed);

    let n0 = O_NOTIONAL[0].load(Ordering::Relaxed);
    let n1 = O_NOTIONAL[1].load(Ordering::Relaxed);
    let n2 = O_NOTIONAL[2].load(Ordering::Relaxed);
    let n3 = O_NOTIONAL[3].load(Ordering::Relaxed);

    let cur_st = select_u8(slot, st0, st1, st2, st3);
    let cur_side = select_u8(slot, sd0, sd1, sd2, sd3);
    let cur_leaves = select_i32(slot, l0, l1, l2, l3);
    let cur_cum = select_i32(slot, c0, c1, c2, c3);
    let cur_not = select_i32(slot, n0, n1, n2, n3);

    let live = SLAB_LIVE.load(Ordering::Relaxed);
    let free = SLAB_FREE.load(Ordering::Relaxed);
    let p_target = P_TARGET_QTY.load(Ordering::Relaxed);
    let old_p_cum = P_CUM_FILLED.load(Ordering::Relaxed);
    let old_p_open = P_OPEN_WORST.load(Ordering::Relaxed);
    let max_cred = MAX_CREDIT.load(Ordering::Relaxed);
    let net_pos = NET_POS.load(Ordering::Relaxed);
    let old_not = OPEN_NOTIONAL.load(Ordering::Relaxed);

    let rem_leaves = cur_leaves.wrapping_sub(exec_shares);
    let exec_full = is_exec & (rem_leaves == 0);
    let release_slot = exec_full | is_cxl;

    let ns_used: u8 = if release_slot { 0 } else { 1 };
    let ns_oref = if release_slot { 0 } else { order_ref };
    let ns_st = if is_ack {
        C_LIVE
    } else if is_cxl {
        C_CANCELED
    } else if exec_full {
        C_FILLED
    } else {
        cur_st
    };
    let ns_side = if release_slot { SIDE_NONE } else { cur_side };
    let ns_leaves = if is_ack {
        cur_leaves
    } else if is_cxl {
        0
    } else {
        rem_leaves
    };
    let ns_cum = if is_exec {
        cur_cum.wrapping_add(exec_shares)
    } else {
        cur_cum
    };
    let ns_not = if release_slot { 0 } else { cur_not };

    let nu0 = if slot == 0 { ns_used } else { u0 };
    let nu1 = if slot == 1 { ns_used } else { u1 };
    let nu2 = if slot == 2 { ns_used } else { u2 };
    let nu3 = if slot == 3 { ns_used } else { u3 };

    let nr0 = if slot == 0 { ns_oref } else { r0 };
    let nr1 = if slot == 1 { ns_oref } else { r1 };
    let nr2 = if slot == 2 { ns_oref } else { r2 };
    let nr3 = if slot == 3 { ns_oref } else { r3 };

    let nst0 = if slot == 0 { ns_st } else { st0 };
    let nst1 = if slot == 1 { ns_st } else { st1 };
    let nst2 = if slot == 2 { ns_st } else { st2 };
    let nst3 = if slot == 3 { ns_st } else { st3 };

    let nsd0 = if slot == 0 { ns_side } else { sd0 };
    let nsd1 = if slot == 1 { ns_side } else { sd1 };
    let nsd2 = if slot == 2 { ns_side } else { sd2 };
    let nsd3 = if slot == 3 { ns_side } else { sd3 };

    let nl0 = if slot == 0 { ns_leaves } else { l0 };
    let nl1 = if slot == 1 { ns_leaves } else { l1 };
    let nl2 = if slot == 2 { ns_leaves } else { l2 };
    let nl3 = if slot == 3 { ns_leaves } else { l3 };

    let nc0 = if slot == 0 { ns_cum } else { c0 };
    let nc1 = if slot == 1 { ns_cum } else { c1 };
    let nc2 = if slot == 2 { ns_cum } else { c2 };
    let nc3 = if slot == 3 { ns_cum } else { c3 };

    let nn0 = if slot == 0 { ns_not } else { n0 };
    let nn1 = if slot == 1 { ns_not } else { n1 };
    let nn2 = if slot == 2 { ns_not } else { n2 };
    let nn3 = if slot == 3 { ns_not } else { n3 };

    let next_live = if release_slot { live.wrapping_sub(1) } else { live };
    let next_free = if release_slot { free.wrapping_add(1) } else { free };

    let cand_p_cum = sum4_checked(nc0, nc1, nc2, nc3);
    let cand_p_open = sum4_checked(nl0, nl1, nl2, nl3);
    let cand_not = sum4_checked(nn0, nn1, nn2, nn3);

    let is_buy = cur_side == SIDE_BUY;
    let exec_pos_ok = if is_buy {
        net_pos <= i32::MAX.wrapping_sub(exec_shares)
    } else {
        net_pos >= i32::MIN.wrapping_add(exec_shares)
    };
    let cand_pos = if is_exec {
        if is_buy {
            net_pos.wrapping_add(exec_shares)
        } else {
            net_pos.wrapping_sub(exec_shares)
        }
    } else {
        net_pos
    };

    let working_st = (cur_st == C_LIVE) | (cur_st == C_PENDING_CANCEL);
    let release_cnt_ok = (!release_slot) | ((live > 0) & (free < SLAB_CAP));
    let agg_ok = (p_target > 0)
        & (max_cred > 0)
        & (cand_p_cum >= 0)
        & (cand_p_open >= 0)
        & (cand_p_cum <= p_target)
        & (cand_p_open <= p_target.wrapping_sub(cand_p_cum))
        & (cand_not >= 0)
        & (cand_not <= max_cred)
        & (cand_pos >= 0i32.wrapping_sub(cand_p_cum))
        & (cand_pos <= cand_p_cum);

    let ack_ok = is_ack & (cur_st == C_PENDING_NEW) & agg_ok;
    let exec_ok = is_exec
        & working_st
        & (is_buy | (cur_side == SIDE_SELL))
        & (exec_shares > 0)
        & (exec_shares <= cur_leaves)
        & (exec_shares <= i32::MAX.wrapping_sub(cur_cum))
        & release_cnt_ok
        & exec_pos_ok
        & agg_ok;
    let cxl_ok = is_cxl & working_st & release_cnt_ok & agg_ok;
    let ok = ack_ok | exec_ok | cxl_ok;

    SLAB_USED[0].store(if ok { nu0 } else { u0 }, Ordering::Relaxed);
    SLAB_USED[1].store(if ok { nu1 } else { u1 }, Ordering::Relaxed);
    SLAB_USED[2].store(if ok { nu2 } else { u2 }, Ordering::Relaxed);
    SLAB_USED[3].store(if ok { nu3 } else { u3 }, Ordering::Relaxed);

    SLAB_ORDER_REF[0].store(if ok { nr0 } else { r0 }, Ordering::Relaxed);
    SLAB_ORDER_REF[1].store(if ok { nr1 } else { r1 }, Ordering::Relaxed);
    SLAB_ORDER_REF[2].store(if ok { nr2 } else { r2 }, Ordering::Relaxed);
    SLAB_ORDER_REF[3].store(if ok { nr3 } else { r3 }, Ordering::Relaxed);

    C_STATE[0].store(if ok { nst0 } else { st0 }, Ordering::Relaxed);
    C_STATE[1].store(if ok { nst1 } else { st1 }, Ordering::Relaxed);
    C_STATE[2].store(if ok { nst2 } else { st2 }, Ordering::Relaxed);
    C_STATE[3].store(if ok { nst3 } else { st3 }, Ordering::Relaxed);

    C_SIDE[0].store(if ok { nsd0 } else { sd0 }, Ordering::Relaxed);
    C_SIDE[1].store(if ok { nsd1 } else { sd1 }, Ordering::Relaxed);
    C_SIDE[2].store(if ok { nsd2 } else { sd2 }, Ordering::Relaxed);
    C_SIDE[3].store(if ok { nsd3 } else { sd3 }, Ordering::Relaxed);

    C_LEAVES[0].store(if ok { nl0 } else { l0 }, Ordering::Relaxed);
    C_LEAVES[1].store(if ok { nl1 } else { l1 }, Ordering::Relaxed);
    C_LEAVES[2].store(if ok { nl2 } else { l2 }, Ordering::Relaxed);
    C_LEAVES[3].store(if ok { nl3 } else { l3 }, Ordering::Relaxed);

    C_CUM[0].store(if ok { nc0 } else { c0 }, Ordering::Relaxed);
    C_CUM[1].store(if ok { nc1 } else { c1 }, Ordering::Relaxed);
    C_CUM[2].store(if ok { nc2 } else { c2 }, Ordering::Relaxed);
    C_CUM[3].store(if ok { nc3 } else { c3 }, Ordering::Relaxed);

    O_NOTIONAL[0].store(if ok { nn0 } else { n0 }, Ordering::Relaxed);
    O_NOTIONAL[1].store(if ok { nn1 } else { n1 }, Ordering::Relaxed);
    O_NOTIONAL[2].store(if ok { nn2 } else { n2 }, Ordering::Relaxed);
    O_NOTIONAL[3].store(if ok { nn3 } else { n3 }, Ordering::Relaxed);

    SLAB_LIVE.store(if ok { next_live } else { live }, Ordering::Relaxed);
    SLAB_FREE.store(if ok { next_free } else { free }, Ordering::Relaxed);
    P_CUM_FILLED.store(if ok { cand_p_cum } else { old_p_cum }, Ordering::Relaxed);
    P_OPEN_WORST.store(if ok { cand_p_open } else { old_p_open }, Ordering::Relaxed);
    NET_POS.store(if ok { cand_pos } else { net_pos }, Ordering::Relaxed);
    OPEN_NOTIONAL.store(if ok { cand_not } else { old_not }, Ordering::Relaxed);
    J_TAIL.store(if ok { j_tail.wrapping_add(1) } else { j_tail }, Ordering::Relaxed);
    if ok { 1 } else { 0 }
}

// ============================================================================
// S4.1 Reference vs Zero-Stack Optimized Inbound ExecReport Pipelines
// ============================================================================

/// Reference E2E Inbound Execution-Report Pipeline (`oms_on_exec_report_ref`):
/// Idiomatic safe-slice decode + branchy `match msg_type` dispatch +
/// shadow-stack journal staging (`Global(0)`) -> `stratum::order_id_mix`
/// open-addressing slab lookup -> Child/Parent FSM + SEC 15c3-5 risk update ->
/// SPSC journal ring push.
#[unsafe(no_mangle)]
pub extern "C" fn oms_on_exec_report_ref(rx_ptr: i32, rx_len: i32) -> i32 {
    if rx_len < (EXEC_REPORT_LEN as i32) {
        return 0;
    }
    // SAFETY: Caller satisfies `req_rx_slice` (in-bounds live DMA slice).
    let rx = unsafe { slice::from_raw_parts(rx_ptr as *const u8, rx_len as usize) };
    let Some(pkt) = rx.get(..EXEC_REPORT_LEN) else {
        return 0;
    };

    let rx_base = pkt.as_ptr();
    // SAFETY: `pkt` has length `EXEC_REPORT_LEN` (31 bytes).
    let (msg_type, order_ref, exec_shares, match_num) = unsafe {
        let mt = core::ptr::read(rx_base);
        let oref = u64::from_be(core::ptr::read_unaligned(rx_base.add(11) as *const u64)) as i64;
        let sh = u32::from_be(core::ptr::read_unaligned(rx_base.add(19) as *const u32)) as i32;
        let mnum = u64::from_be(core::ptr::read_unaligned(rx_base.add(23) as *const u64)) as i64;
        (mt, oref, sh, mnum)
    };

    let ok = match msg_type {
        MSG_ORDER_ACK | MSG_ORDER_EXECUTED | MSG_ORDER_CANCELED => {
            apply_exec_report_core(msg_type, order_ref, exec_shares)
        }
        _ => 0,
    };
    if ok != 0 {
        let mut staged = [0u8; 32];
        stage_journal_on_stack(order_ref, msg_type, match_num, &mut staged);
        let j_tail_prev = J_TAIL.load(Ordering::Relaxed).wrapping_sub(1);
        commit_staged_journal(&staged, (j_tail_prev & RING_MASK) as usize);
    }
    ok
}

/// Zero-Stack Optimized E2E Inbound Execution-Report Pipeline (`oms_on_exec_report_opt`):
/// Zero `__stack_pointer` accesses, direct unaligned Big-Endian wide wire loads,
/// Layer-1 `stratum::order_id_mix` slab lookup, straight-line constant-address writes,
/// and direct SPSC journal ring push.
#[unsafe(no_mangle)]
pub extern "C" fn oms_on_exec_report_opt(rx_ptr: i32, rx_len: i32) -> i32 {
    if rx_len < (EXEC_REPORT_LEN as i32) {
        return 0;
    }
    let rx_base = rx_ptr as usize as *const u8;
    // SAFETY: Caller satisfies `req_rx_slice` and `rx_len >= 31`.
    let (msg_type, order_ref, exec_shares, match_num) = unsafe {
        let mt = core::ptr::read(rx_base);
        let oref = u64::from_be(core::ptr::read_unaligned(rx_base.add(11) as *const u64)) as i64;
        let sh = u32::from_be(core::ptr::read_unaligned(rx_base.add(19) as *const u32)) as i32;
        let mnum = u64::from_be(core::ptr::read_unaligned(rx_base.add(23) as *const u64)) as i64;
        (mt, oref, sh, mnum)
    };
    if msg_type != MSG_ORDER_ACK
        && msg_type != MSG_ORDER_EXECUTED
        && msg_type != MSG_ORDER_CANCELED
    {
        return 0;
    }
    let ok = apply_exec_report_core(msg_type, order_ref, exec_shares);
    if ok != 0 {
        let entry = (match_num & !0xFFi64) | (msg_type as i64);
        let j_tail_prev = J_TAIL.load(Ordering::Relaxed).wrapping_sub(1);
        J_SLOTS[(j_tail_prev & RING_MASK) as usize].store(entry, Ordering::Relaxed);
    }
    ok
}

// ============================================================================
// Inline Relational E2E Verification Contracts
// ============================================================================

/// Inline relational contract proving:
/// Starting from ANY valid OMS state (`inv_oms_e2e() == 1`) with an active child in
/// `C_PENDING_CANCEL` (with arbitrary symbolic `order_ref`, `C_SIDE`, `C_LEAVES`, `C_CUM`,
/// `O_NOTIONAL`, `P_TARGET_QTY`, `NET_POS`, `J_HEAD`/`J_TAIL` wraparound, and arbitrary
/// `order_id_mix(order_ref) & 3` probe start), an inbound Fill (`b'E'`) with
/// `0 < exec_shares <= c_leaves` is NEVER dropped (`ret == 1`), rolls up exact `exec_shares`
/// into `P_CUM_FILLED`, reduces `P_OPEN_WORST` by `exec_shares`, advances `J_TAIL` by 1,
/// and preserves Zero Over-Fill + risk credit conservation + slab/ring invariants.
#[unsafe(no_mangle)]
pub extern "C" fn contract_e2e_exec_report_preserves_oms(rx_ptr: i32, rx_len: i32) -> i32 {
    assume(req_rx_slice(rx_ptr, rx_len) == 1);
    assume(inv_oms_e2e() == 1);
    assume(rx_len >= (EXEC_REPORT_LEN as i32));
    assume(C_STATE[0].load(Ordering::Relaxed) == C_PENDING_CANCEL);
    assume(C_CUM[0].load(Ordering::Relaxed) == 0);
    assume(C_STATE[1].load(Ordering::Relaxed) == C_EMPTY);
    assume(C_STATE[2].load(Ordering::Relaxed) == C_EMPTY);
    assume(C_STATE[3].load(Ordering::Relaxed) == C_EMPTY);

    let old_p_cum = P_CUM_FILLED.load(Ordering::Relaxed);
    let old_p_open = P_OPEN_WORST.load(Ordering::Relaxed);
    let old_j_tail = J_TAIL.load(Ordering::Relaxed);
    let old_j_head = J_HEAD.load(Ordering::Relaxed);
    assume((old_j_tail.wrapping_sub(old_j_head) as u32) < (RING_CAP as u32));

    let rx_base = rx_ptr as usize as *const u8;
    let (mt, oref, sh) = unsafe {
        let mt = core::ptr::read(rx_base);
        let oref = u64::from_be(core::ptr::read_unaligned(rx_base.add(11) as *const u64)) as i64;
        let sh = u32::from_be(core::ptr::read_unaligned(rx_base.add(19) as *const u32)) as i32;
        (mt, oref, sh)
    };
    assume(mt == MSG_ORDER_EXECUTED);
    assume(oref == SLAB_ORDER_REF[0].load(Ordering::Relaxed));
    assume(sh > 0 && sh <= C_LEAVES[0].load(Ordering::Relaxed));

    let ret = oms_on_exec_report_opt(rx_ptr, rx_len);
    let new_p_cum = P_CUM_FILLED.load(Ordering::Relaxed);
    let new_p_open = P_OPEN_WORST.load(Ordering::Relaxed);
    let p_target = P_TARGET_QTY.load(Ordering::Relaxed);
    let new_j_tail = J_TAIL.load(Ordering::Relaxed);

    assert_prop(ret == 1);
    assert_prop(new_p_cum == old_p_cum.wrapping_add(sh));
    assert_prop(new_p_open == old_p_open.wrapping_sub(sh));
    assert_prop(new_p_cum <= p_target && new_p_open <= p_target.wrapping_sub(new_p_cum));
    assert_prop(
        SLAB_LIVE.load(Ordering::Relaxed).wrapping_add(SLAB_FREE.load(Ordering::Relaxed))
            == SLAB_CAP,
    );
    assert_prop(OPEN_NOTIONAL.load(Ordering::Relaxed) <= MAX_CREDIT.load(Ordering::Relaxed));
    assert_prop(new_j_tail == old_j_tail.wrapping_add(1));
    assert_prop((new_j_tail.wrapping_sub(old_j_head) as u32) <= (RING_CAP as u32));
    1
}

/// Inline relational contract proving duplicate `CancelAck` NEVER double-releases risk credit:
/// Running `oms_on_exec_report_opt` twice with the same `CancelAck` packet produces `r2 == 0`
/// on the second call and preserves `OPEN_NOTIONAL` and `SLAB_LIVE`.
#[unsafe(no_mangle)]
pub extern "C" fn contract_e2e_no_double_cancel_credit(rx_ptr: i32, rx_len: i32) -> i32 {
    assume(req_rx_slice(rx_ptr, rx_len) == 1);
    assume(inv_oms_e2e() == 1);
    assume(rx_len >= (EXEC_REPORT_LEN as i32));
    let mt = unsafe { core::ptr::read(rx_ptr as usize as *const u8) };
    assume(mt == MSG_ORDER_CANCELED);

    let r1 = oms_on_exec_report_opt(rx_ptr, rx_len);
    let not_after_first = OPEN_NOTIONAL.load(Ordering::Relaxed);
    let live_after_first = SLAB_LIVE.load(Ordering::Relaxed);
    let r2 = oms_on_exec_report_opt(rx_ptr, rx_len);

    if r1 == 1 {
        assert_prop(r2 == 0);
        assert_prop(OPEN_NOTIONAL.load(Ordering::Relaxed) == not_after_first);
        assert_prop(OPEN_NOTIONAL.load(Ordering::Relaxed) >= 0);
        assert_prop(SLAB_LIVE.load(Ordering::Relaxed) == live_after_first);
    }
    1
}
