#![no_std]

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

static WIRE_DMA_GUARD: [u8; 64] = [0; 64];

const STACK_TOP: i32 = 1_048_576;
const LIVE_LO: i32 = STACK_TOP + 4_096;
const LIVE_HI: i32 = STACK_TOP + 32_768;
const MIN_LIVE_PAGES: usize = 17;

const MSG_ORDER_ACK: u8 = b'A';
const MSG_ORDER_EXECUTED: u8 = b'E';
const MSG_ORDER_CANCELED: u8 = b'C';
const EXEC_REPORT_LEN: usize = 31;

const SLAB_CAP: u8 = 4;
const SLAB_MASK: i32 = 3;
const RING_CAP: i32 = 8;
const RING_MASK: i32 = 7;

const C_EMPTY: u8 = 0;
const C_PENDING_NEW: u8 = 1;
const C_LIVE: u8 = 2;
const C_PENDING_CANCEL: u8 = 3;
const C_FILLED: u8 = 4;
const C_CANCELED: u8 = 5;

const SIDE_NONE: u8 = 0;
const SIDE_BUY: u8 = 1;
const SIDE_SELL: u8 = 2;

static OMS_ACTIVE: AtomicU8 = AtomicU8::new(0);
static P_TARGET_QTY: AtomicI32 = AtomicI32::new(0);
static P_CUM_FILLED: AtomicI32 = AtomicI32::new(0);
static P_OPEN_WORST: AtomicI32 = AtomicI32::new(0);

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

static MAX_CREDIT: AtomicI32 = AtomicI32::new(0);
static MAX_POS: AtomicI32 = AtomicI32::new(0);
static NET_POS: AtomicI32 = AtomicI32::new(0);
static OPEN_NOTIONAL: AtomicI32 = AtomicI32::new(0);

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

#[inline(always)]
fn sum4_checked(a: i32, b: i32, c: i32, d: i32) -> i32 {
    let s01 = a.wrapping_add(b);
    let s23 = c.wrapping_add(d);
    let s = s01.wrapping_add(s23);
    if (a | b | c | d | s01 | s23 | s) < 0 { -1 } else { s }
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

#[inline(always)]
fn net_pos_within_cum(net_pos: i32, p_cum: i32, p_target: i32, max_pos: i32) -> bool {
    let neg_cum = 0i32.wrapping_sub(p_cum);
    (max_pos >= p_target) & (p_cum >= 0) & (net_pos >= neg_cum) & (net_pos <= p_cum)
}

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

    if select_u8(p0, m0, m1, m2, m3) != 0 {
        p0
    } else if select_u8(p1, m0, m1, m2, m3) != 0 {
        p1
    } else if select_u8(p2, m0, m1, m2, m3) != 0 {
        p2
    } else if select_u8(p3, m0, m1, m2, m3) != 0 {
        p3
    } else {
        -1
    }
}

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
}

#[unsafe(no_mangle)]
pub extern "C" fn oms_route_order(order_ref: i64, side: i32, qty: i32, notional: i32) -> i32 {
    if OMS_ACTIVE.load(Ordering::Relaxed) != 1
        || order_ref == 0
        || (side != (SIDE_BUY as i32) && side != (SIDE_SELL as i32))
        || qty <= 0
        || notional <= 0
    {
        return 0;
    }
    let live = SLAB_LIVE.load(Ordering::Relaxed);
    let free = SLAB_FREE.load(Ordering::Relaxed);
    if free == 0 || live >= SLAB_CAP {
        return 0;
    }
    SLAB_USED[0].store(1, Ordering::Relaxed);
    SLAB_ORDER_REF[0].store(order_ref, Ordering::Relaxed);
    C_STATE[0].store(C_PENDING_NEW, Ordering::Relaxed);
    C_SIDE[0].store(side as u8, Ordering::Relaxed);
    C_LEAVES[0].store(qty, Ordering::Relaxed);
    O_NOTIONAL[0].store(notional, Ordering::Relaxed);
    SLAB_LIVE.store(live.wrapping_add(1), Ordering::Relaxed);
    SLAB_FREE.store(free.wrapping_sub(1), Ordering::Relaxed);
    P_OPEN_WORST.store(P_OPEN_WORST.load(Ordering::Relaxed).wrapping_add(qty), Ordering::Relaxed);
    OPEN_NOTIONAL.store(OPEN_NOTIONAL.load(Ordering::Relaxed).wrapping_add(notional), Ordering::Relaxed);
    1
}

#[unsafe(no_mangle)]
pub extern "C" fn oms_request_cancel(order_ref: i64) -> i32 {
    if OMS_ACTIVE.load(Ordering::Relaxed) != 1 || order_ref == 0 {
        return 0;
    }
    C_STATE[0].store(C_PENDING_CANCEL, Ordering::Relaxed);
    1
}

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

/// Mutant 1 (`oms_on_exec_report_buggy_drops_pending_cancel_fill`):
/// Rejects fills when `cur_st == C_PENDING_CANCEL` (classic race-condition bug where
/// an exchange fill racing with a cancel request is silently dropped!) ->
/// FALSIFIED by `contract_e2e_exec_report_preserves_oms_buggy`!
#[unsafe(no_mangle)]
pub extern "C" fn oms_on_exec_report_buggy_drops_pending_cancel_fill(
    rx_ptr: i32,
    rx_len: i32,
) -> i32 {
    if rx_len < (EXEC_REPORT_LEN as i32) {
        return 0;
    }
    let rx_base = rx_ptr as usize as *const u8;
    let (msg_type, order_ref, exec_shares, match_num) = unsafe {
        let mt = core::ptr::read(rx_base);
        let oref = u64::from_be(core::ptr::read_unaligned(rx_base.add(11) as *const u64)) as i64;
        let sh = u32::from_be(core::ptr::read_unaligned(rx_base.add(19) as *const u32)) as i32;
        let mnum = u64::from_be(core::ptr::read_unaligned(rx_base.add(23) as *const u64)) as i64;
        (mt, oref, sh, mnum)
    };
    if order_ref == 0
        || (msg_type != MSG_ORDER_ACK
            && msg_type != MSG_ORDER_EXECUTED
            && msg_type != MSG_ORDER_CANCELED)
    {
        return 0;
    }
    let j_head = J_HEAD.load(Ordering::Relaxed);
    let j_tail = J_TAIL.load(Ordering::Relaxed);
    if OMS_ACTIVE.load(Ordering::Relaxed) != 1
        || J_CAP.load(Ordering::Relaxed) != RING_CAP
        || (j_tail.wrapping_sub(j_head) as u32) >= (RING_CAP as u32)
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
    let cur_st = select_u8(slot, st0, st1, st2, st3);

    // BUG: drops fills during C_PENDING_CANCEL (only checks C_LIVE)!
    if msg_type == MSG_ORDER_EXECUTED && cur_st != C_LIVE {
        return 0;
    }
    let _ = (exec_shares, match_num);
    if msg_type == MSG_ORDER_ACK && cur_st == C_PENDING_NEW {
        C_STATE[slot as usize].store(C_LIVE, Ordering::Relaxed);
        J_SLOTS[(j_tail & RING_MASK) as usize].store((match_num & !0xFF) | (msg_type as i64), Ordering::Relaxed);
        J_TAIL.store(j_tail.wrapping_add(1), Ordering::Relaxed);
        return 1;
    }
    0
}

/// Mutant 2 (`oms_on_exec_report_buggy_double_cancel_credit`):
/// On `CancelAck` (`b'C'`), subtracts `O_NOTIONAL[slot]` from `OPEN_NOTIONAL` without
/// clearing `SLAB_USED[slot]`/`O_NOTIONAL[slot]`, violating exact risk credit conservation
/// and allowing duplicate `CancelAck` to double-release credit ->
/// FALSIFIED by BOTH `--invariant inv_oms_e2e` AND `contract_e2e_no_double_cancel_credit_buggy`!
#[unsafe(no_mangle)]
pub extern "C" fn oms_on_exec_report_buggy_double_cancel_credit(
    rx_ptr: i32,
    rx_len: i32,
) -> i32 {
    if rx_len < (EXEC_REPORT_LEN as i32) {
        return 0;
    }
    let rx_base = rx_ptr as usize as *const u8;
    let (msg_type, order_ref, match_num) = unsafe {
        let mt = core::ptr::read(rx_base);
        let oref = u64::from_be(core::ptr::read_unaligned(rx_base.add(11) as *const u64)) as i64;
        let mnum = u64::from_be(core::ptr::read_unaligned(rx_base.add(23) as *const u64)) as i64;
        (mt, oref, mnum)
    };
    if msg_type != MSG_ORDER_CANCELED || order_ref == 0 {
        return 0;
    }
    let j_head = J_HEAD.load(Ordering::Relaxed);
    let j_tail = J_TAIL.load(Ordering::Relaxed);
    if OMS_ACTIVE.load(Ordering::Relaxed) != 1
        || J_CAP.load(Ordering::Relaxed) != RING_CAP
        || (j_tail.wrapping_sub(j_head) as u32) >= (RING_CAP as u32)
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
    let cur_st = select_u8(slot, st0, st1, st2, st3);
    if cur_st != C_LIVE && cur_st != C_PENDING_CANCEL {
        return 0;
    }

    let n0 = O_NOTIONAL[0].load(Ordering::Relaxed);
    let n1 = O_NOTIONAL[1].load(Ordering::Relaxed);
    let n2 = O_NOTIONAL[2].load(Ordering::Relaxed);
    let n3 = O_NOTIONAL[3].load(Ordering::Relaxed);
    let cur_not = select_i32(slot, n0, n1, n2, n3);

    // BUG: subtracts `cur_not` from `OPEN_NOTIONAL` without deactivating the slab slot
    // or zeroing `O_NOTIONAL[slot]` -> duplicate CancelAck double-releases credit & breaks inv!
    let next_not = OPEN_NOTIONAL.load(Ordering::Relaxed).wrapping_sub(cur_not);
    OPEN_NOTIONAL.store(next_not, Ordering::Relaxed);
    let _ = sum4_checked(n0, n1, n2, n3);
    J_SLOTS[(j_tail & RING_MASK) as usize]
        .store((match_num & !0xFFi64) | (msg_type as i64), Ordering::Relaxed);
    J_TAIL.store(j_tail.wrapping_add(1), Ordering::Relaxed);
    1
}

/// Inline contract exposing Mutant 1 (drops fill during `PendingCancel`) -> FALSIFIED!
#[unsafe(no_mangle)]
pub extern "C" fn contract_e2e_exec_report_preserves_oms_buggy(rx_ptr: i32, rx_len: i32) -> i32 {
    assume(req_rx_slice(rx_ptr, rx_len) == 1);
    assume(inv_oms_e2e() == 1);
    assume(rx_len >= (EXEC_REPORT_LEN as i32));
    assume(C_STATE[0].load(Ordering::Relaxed) == C_PENDING_CANCEL);
    assume(C_CUM[0].load(Ordering::Relaxed) == 0);
    assume(C_STATE[1].load(Ordering::Relaxed) == C_EMPTY);
    assume(C_STATE[2].load(Ordering::Relaxed) == C_EMPTY);
    assume(C_STATE[3].load(Ordering::Relaxed) == C_EMPTY);

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

    let ret = oms_on_exec_report_buggy_drops_pending_cancel_fill(rx_ptr, rx_len);
    assert_prop(ret == 1);
    1
}

/// Inline contract exposing Mutant 2 (duplicate `CancelAck` double-releases credit) -> FALSIFIED!
#[unsafe(no_mangle)]
pub extern "C" fn contract_e2e_no_double_cancel_credit_buggy(rx_ptr: i32, rx_len: i32) -> i32 {
    assume(req_rx_slice(rx_ptr, rx_len) == 1);
    assume(inv_oms_e2e() == 1);
    assume(rx_len >= (EXEC_REPORT_LEN as i32));
    let mt = unsafe { core::ptr::read(rx_ptr as usize as *const u8) };
    assume(mt == MSG_ORDER_CANCELED);

    let r1 = oms_on_exec_report_buggy_double_cancel_credit(rx_ptr, rx_len);
    let not_after_first = OPEN_NOTIONAL.load(Ordering::Relaxed);
    let r2 = oms_on_exec_report_buggy_double_cancel_credit(rx_ptr, rx_len);

    if r1 == 1 {
        assert_prop(r2 == 0);
        assert_prop(OPEN_NOTIONAL.load(Ordering::Relaxed) == not_after_first);
        assert_prop(OPEN_NOTIONAL.load(Ordering::Relaxed) >= 0);
    }
    1
}
