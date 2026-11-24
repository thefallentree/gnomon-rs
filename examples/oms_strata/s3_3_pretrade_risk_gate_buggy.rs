#![no_std]

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

#[link(wasm_import_module = "stratum")]
unsafe extern "C" {
    fn checked_notional(price: i64, qty: i64, max_notional: i64) -> i32;
    fn price_collar_ok(price: i64, ref_price: i64, collar_bps: i64) -> i32;
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

#[inline(always)]
fn call_checked_notional(price: i64, qty: i64, max_notional: i64) -> i32 {
    unsafe { checked_notional(price, qty, max_notional) }
}

#[inline(always)]
fn call_price_collar_ok(price: i64, ref_price: i64, collar_bps: i64) -> i32 {
    unsafe { price_collar_ok(price, ref_price, collar_bps) }
}

const SIDE_NONE: u8 = 0;
const SIDE_BUY: u8 = 1;
const SIDE_SELL: u8 = 2;

static RISK_INIT: AtomicU8 = AtomicU8::new(0);
static KILL_SWITCH: AtomicU8 = AtomicU8::new(0);
static MAX_ORDER_NOTIONAL: AtomicI64 = AtomicI64::new(0);
static MAX_CREDIT: AtomicI64 = AtomicI64::new(0);
static MAX_POS: AtomicI64 = AtomicI64::new(0);
static REF_PRICE: AtomicI64 = AtomicI64::new(0);
static COLLAR_BPS: AtomicI64 = AtomicI64::new(0);

static NET_POS: AtomicI64 = AtomicI64::new(0);
static OPEN_BUY_QTY: AtomicI64 = AtomicI64::new(0);
static OPEN_SELL_QTY: AtomicI64 = AtomicI64::new(0);
static OPEN_NOTIONAL: AtomicI64 = AtomicI64::new(0);

static O_ACTIVE: [AtomicU8; 4] = [
    AtomicU8::new(0),
    AtomicU8::new(0),
    AtomicU8::new(0),
    AtomicU8::new(0),
];
static O_SIDE: [AtomicU8; 4] = [
    AtomicU8::new(SIDE_NONE),
    AtomicU8::new(SIDE_NONE),
    AtomicU8::new(SIDE_NONE),
    AtomicU8::new(SIDE_NONE),
];
static O_QTY: [AtomicI64; 4] = [
    AtomicI64::new(0),
    AtomicI64::new(0),
    AtomicI64::new(0),
    AtomicI64::new(0),
];
static O_NOTIONAL: [AtomicI64; 4] = [
    AtomicI64::new(0),
    AtomicI64::new(0),
    AtomicI64::new(0),
    AtomicI64::new(0),
];

#[inline(always)]
fn sum4_checked(a: i64, b: i64, c: i64, d: i64) -> i64 {
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
fn sum4_eq(a: i64, b: i64, c: i64, d: i64, total: i64) -> bool {
    let s01 = a.wrapping_add(b);
    let s23 = c.wrapping_add(d);
    let s = s01.wrapping_add(s23);
    ((a | b | c | d | total | s01 | s23 | s) >= 0) && (s == total)
}

#[inline(always)]
fn select_u8(slot: i32, v0: u8, v1: u8, v2: u8, v3: u8) -> u8 {
    if slot == 0 {
        v0
    } else if slot == 1 {
        v1
    } else if slot == 2 {
        v2
    } else {
        v3
    }
}

#[inline(always)]
fn select_i64(slot: i32, v0: i64, v1: i64, v2: i64, v3: i64) -> i64 {
    if slot == 0 {
        v0
    } else if slot == 1 {
        v1
    } else if slot == 2 {
        v2
    } else {
        v3
    }
}

#[inline(always)]
fn load_o_active(slot: i32) -> u8 {
    select_u8(
        slot,
        O_ACTIVE[0].load(Ordering::Relaxed),
        O_ACTIVE[1].load(Ordering::Relaxed),
        O_ACTIVE[2].load(Ordering::Relaxed),
        O_ACTIVE[3].load(Ordering::Relaxed),
    )
}

#[inline(always)]
fn load_o_notional(slot: i32) -> i64 {
    select_i64(
        slot,
        O_NOTIONAL[0].load(Ordering::Relaxed),
        O_NOTIONAL[1].load(Ordering::Relaxed),
        O_NOTIONAL[2].load(Ordering::Relaxed),
        O_NOTIONAL[3].load(Ordering::Relaxed),
    )
}

#[inline(always)]
fn slot_side_qty(active: u8, side: u8, qty: i64, target_side: u8) -> i64 {
    if active == 1 && side == target_side { qty } else { 0 }
}

#[inline(always)]
fn inv_order_slot(active: u8, side: u8, qty: i64, notional: i64, max_ord: i64) -> bool {
    if active == 0 {
        side == SIDE_NONE && qty == 0 && notional == 0
    } else if active == 1 {
        (side == SIDE_BUY || side == SIDE_SELL) && qty > 0 && notional > 0 && notional <= max_ord
    } else {
        false
    }
}

#[inline(always)]
fn fits_long_limit(net_pos: i64, open_buy: i64, max_pos: i64) -> bool {
    if max_pos <= 0 || open_buy < 0 {
        return false;
    }
    let neg_max_pos = 0i64.wrapping_sub(max_pos);
    if net_pos < neg_max_pos || net_pos > max_pos {
        return false;
    }
    let buy_room_u = (max_pos as u64).wrapping_sub(net_pos as u64);
    (open_buy as u64) <= buy_room_u
}

#[inline(always)]
fn fits_short_limit(net_pos: i64, open_sell: i64, max_pos: i64) -> bool {
    if max_pos <= 0 || open_sell < 0 {
        return false;
    }
    let neg_max_pos = 0i64.wrapping_sub(max_pos);
    if net_pos < neg_max_pos || net_pos > max_pos {
        return false;
    }
    let sell_room_u = (net_pos as u64).wrapping_sub(neg_max_pos as u64);
    (open_sell as u64) <= sell_room_u
}

#[inline(never)]
fn write_slot_at<const S: usize>(active: u8, side: u8, qty: i64, notional: i64) {
    O_ACTIVE[S].store(active, Ordering::Relaxed);
    O_SIDE[S].store(side, Ordering::Relaxed);
    O_QTY[S].store(qty, Ordering::Relaxed);
    O_NOTIONAL[S].store(notional, Ordering::Relaxed);
}

#[inline(never)]
fn write_replace_slot_at<const S: usize>(qty: i64, notional: i64) {
    O_QTY[S].store(qty, Ordering::Relaxed);
    O_NOTIONAL[S].store(notional, Ordering::Relaxed);
}

#[inline(always)]
fn write_slot(slot: i32, active: u8, side: u8, qty: i64, notional: i64) {
    if slot == 0 {
        write_slot_at::<0>(active, side, qty, notional);
    } else if slot == 1 {
        write_slot_at::<1>(active, side, qty, notional);
    } else if slot == 2 {
        write_slot_at::<2>(active, side, qty, notional);
    } else {
        write_slot_at::<3>(active, side, qty, notional);
    }
}

/// Baseline `init_risk` (exported so all state fields remain live and cannot be constant-folded).
#[unsafe(no_mangle)]
pub extern "C" fn init_risk(
    max_order_notional: i64,
    max_credit: i64,
    max_pos: i64,
    ref_price: i64,
    collar_bps: i64,
) -> i32 {
    if max_order_notional <= 0
        || max_credit <= 0
        || max_pos <= 0
        || ref_price <= 0
        || collar_bps < 0
        || collar_bps > 10_000
    {
        return 0;
    }
    RISK_INIT.store(1, Ordering::Relaxed);
    KILL_SWITCH.store(0, Ordering::Relaxed);
    MAX_ORDER_NOTIONAL.store(max_order_notional, Ordering::Relaxed);
    MAX_CREDIT.store(max_credit, Ordering::Relaxed);
    MAX_POS.store(max_pos, Ordering::Relaxed);
    REF_PRICE.store(ref_price, Ordering::Relaxed);
    COLLAR_BPS.store(collar_bps, Ordering::Relaxed);

    NET_POS.store(0, Ordering::Relaxed);
    OPEN_BUY_QTY.store(0, Ordering::Relaxed);
    OPEN_SELL_QTY.store(0, Ordering::Relaxed);
    OPEN_NOTIONAL.store(0, Ordering::Relaxed);

    let mut i = 0;
    while i < 4 {
        O_ACTIVE[i].store(0, Ordering::Relaxed);
        O_SIDE[i].store(SIDE_NONE, Ordering::Relaxed);
        O_QTY[i].store(0, Ordering::Relaxed);
        O_NOTIONAL[i].store(0, Ordering::Relaxed);
        i += 1;
    }
    1
}

/// Baseline `trip_kill_switch`.
#[unsafe(no_mangle)]
pub extern "C" fn trip_kill_switch() -> i32 {
    if RISK_INIT.load(Ordering::Relaxed) != 1 {
        return 0;
    }
    KILL_SWITCH.store(1, Ordering::Relaxed);
    1
}

/// Baseline `on_fill`.
#[unsafe(no_mangle)]
pub extern "C" fn on_fill(slot: i32, fill_qty: i64) -> i32 {
    if RISK_INIT.load(Ordering::Relaxed) != 1 || slot < 0 || slot >= 4 || fill_qty <= 0 {
        return 0;
    }
    let a0 = O_ACTIVE[0].load(Ordering::Relaxed);
    let a1 = O_ACTIVE[1].load(Ordering::Relaxed);
    let a2 = O_ACTIVE[2].load(Ordering::Relaxed);
    let a3 = O_ACTIVE[3].load(Ordering::Relaxed);
    if select_u8(slot, a0, a1, a2, a3) != 1 {
        return 0;
    }
    let s0 = O_SIDE[0].load(Ordering::Relaxed);
    let s1 = O_SIDE[1].load(Ordering::Relaxed);
    let s2 = O_SIDE[2].load(Ordering::Relaxed);
    let s3 = O_SIDE[3].load(Ordering::Relaxed);
    let cur_side = select_u8(slot, s0, s1, s2, s3);
    if cur_side != SIDE_BUY && cur_side != SIDE_SELL {
        return 0;
    }
    let q0_old = O_QTY[0].load(Ordering::Relaxed);
    let q1_old = O_QTY[1].load(Ordering::Relaxed);
    let q2_old = O_QTY[2].load(Ordering::Relaxed);
    let q3_old = O_QTY[3].load(Ordering::Relaxed);
    let old_qty = select_i64(slot, q0_old, q1_old, q2_old, q3_old);
    if fill_qty > old_qty {
        return 0;
    }
    let n0_old = O_NOTIONAL[0].load(Ordering::Relaxed);
    let n1_old = O_NOTIONAL[1].load(Ordering::Relaxed);
    let n2_old = O_NOTIONAL[2].load(Ordering::Relaxed);
    let n3_old = O_NOTIONAL[3].load(Ordering::Relaxed);
    let old_not = select_i64(slot, n0_old, n1_old, n2_old, n3_old);

    let rem_qty = old_qty.wrapping_sub(fill_qty);
    let (new_active, new_side, new_not) = if rem_qty == 0 {
        (0u8, SIDE_NONE, 0i64)
    } else {
        (1u8, cur_side, old_not)
    };
    let n0 = if slot == 0 { new_not } else { n0_old };
    let n1 = if slot == 1 { new_not } else { n1_old };
    let n2 = if slot == 2 { new_not } else { n2_old };
    let n3 = if slot == 3 { new_not } else { n3_old };
    let next_not = sum4_checked(n0, n1, n2, n3);
    if next_not < 0 || next_not > MAX_CREDIT.load(Ordering::Relaxed) {
        return 0;
    }

    let na0 = if slot == 0 { new_active } else { a0 };
    let na1 = if slot == 1 { new_active } else { a1 };
    let na2 = if slot == 2 { new_active } else { a2 };
    let na3 = if slot == 3 { new_active } else { a3 };
    let ns0 = if slot == 0 { new_side } else { s0 };
    let ns1 = if slot == 1 { new_side } else { s1 };
    let ns2 = if slot == 2 { new_side } else { s2 };
    let ns3 = if slot == 3 { new_side } else { s3 };
    let q0 = if slot == 0 { rem_qty } else { q0_old };
    let q1 = if slot == 1 { rem_qty } else { q1_old };
    let q2 = if slot == 2 { rem_qty } else { q2_old };
    let q3 = if slot == 3 { rem_qty } else { q3_old };

    let max_pos = MAX_POS.load(Ordering::Relaxed);
    let net_pos = NET_POS.load(Ordering::Relaxed);
    if cur_side == SIDE_BUY {
        if net_pos > i64::MAX.wrapping_sub(fill_qty) {
            return 0;
        }
        let next_pos = net_pos.wrapping_add(fill_qty);
        let next_buy = sum4_checked(
            slot_side_qty(na0, ns0, q0, SIDE_BUY),
            slot_side_qty(na1, ns1, q1, SIDE_BUY),
            slot_side_qty(na2, ns2, q2, SIDE_BUY),
            slot_side_qty(na3, ns3, q3, SIDE_BUY),
        );
        if next_buy < 0
            || !fits_long_limit(next_pos, next_buy, max_pos)
            || !fits_short_limit(next_pos, OPEN_SELL_QTY.load(Ordering::Relaxed), max_pos)
        {
            return 0;
        }
        NET_POS.store(next_pos, Ordering::Relaxed);
        OPEN_BUY_QTY.store(next_buy, Ordering::Relaxed);
    } else {
        if net_pos < i64::MIN.wrapping_add(fill_qty) {
            return 0;
        }
        let next_pos = net_pos.wrapping_sub(fill_qty);
        let next_sell = sum4_checked(
            slot_side_qty(na0, ns0, q0, SIDE_SELL),
            slot_side_qty(na1, ns1, q1, SIDE_SELL),
            slot_side_qty(na2, ns2, q2, SIDE_SELL),
            slot_side_qty(na3, ns3, q3, SIDE_SELL),
        );
        if next_sell < 0
            || !fits_long_limit(next_pos, OPEN_BUY_QTY.load(Ordering::Relaxed), max_pos)
            || !fits_short_limit(next_pos, next_sell, max_pos)
        {
            return 0;
        }
        NET_POS.store(next_pos, Ordering::Relaxed);
        OPEN_SELL_QTY.store(next_sell, Ordering::Relaxed);
    }

    write_slot(slot, new_active, new_side, rem_qty, new_not);
    OPEN_NOTIONAL.store(next_not, Ordering::Relaxed);
    1
}

/// Baseline `submit_order` (used alongside Mutant 1 in kill-switch harness).
#[unsafe(no_mangle)]
pub extern "C" fn submit_order(slot: i32, side: i32, price: i64, qty: i64) -> i32 {
    if RISK_INIT.load(Ordering::Relaxed) != 1 || KILL_SWITCH.load(Ordering::Relaxed) != 0 {
        return 0;
    }
    if slot < 0
        || slot >= 4
        || (side != (SIDE_BUY as i32) && side != (SIDE_SELL as i32))
        || price <= 0
        || qty <= 0
    {
        return 0;
    }

    let a0 = O_ACTIVE[0].load(Ordering::Relaxed);
    let a1 = O_ACTIVE[1].load(Ordering::Relaxed);
    let a2 = O_ACTIVE[2].load(Ordering::Relaxed);
    let a3 = O_ACTIVE[3].load(Ordering::Relaxed);
    if select_u8(slot, a0, a1, a2, a3) != 0 {
        return 0;
    }

    let max_ord = MAX_ORDER_NOTIONAL.load(Ordering::Relaxed);
    let ref_px = REF_PRICE.load(Ordering::Relaxed);
    let collar = COLLAR_BPS.load(Ordering::Relaxed);

    if call_checked_notional(price, qty, max_ord) == 0 {
        return 0;
    }
    if call_price_collar_ok(price, ref_px, collar) == 0 {
        return 0;
    }

    let notional = price.wrapping_mul(qty);
    if notional <= 0 || notional > max_ord {
        return 0;
    }

    let max_cred = MAX_CREDIT.load(Ordering::Relaxed);
    let n0 = if slot == 0 { notional } else { O_NOTIONAL[0].load(Ordering::Relaxed) };
    let n1 = if slot == 1 { notional } else { O_NOTIONAL[1].load(Ordering::Relaxed) };
    let n2 = if slot == 2 { notional } else { O_NOTIONAL[2].load(Ordering::Relaxed) };
    let n3 = if slot == 3 { notional } else { O_NOTIONAL[3].load(Ordering::Relaxed) };
    let next_not = sum4_checked(n0, n1, n2, n3);
    if next_not < 0 || next_not > max_cred {
        return 0;
    }

    let side_u8 = side as u8;
    let na0 = if slot == 0 { 1 } else { a0 };
    let na1 = if slot == 1 { 1 } else { a1 };
    let na2 = if slot == 2 { 1 } else { a2 };
    let na3 = if slot == 3 { 1 } else { a3 };
    let s0 = if slot == 0 { side_u8 } else { O_SIDE[0].load(Ordering::Relaxed) };
    let s1 = if slot == 1 { side_u8 } else { O_SIDE[1].load(Ordering::Relaxed) };
    let s2 = if slot == 2 { side_u8 } else { O_SIDE[2].load(Ordering::Relaxed) };
    let s3 = if slot == 3 { side_u8 } else { O_SIDE[3].load(Ordering::Relaxed) };
    let q0 = if slot == 0 { qty } else { O_QTY[0].load(Ordering::Relaxed) };
    let q1 = if slot == 1 { qty } else { O_QTY[1].load(Ordering::Relaxed) };
    let q2 = if slot == 2 { qty } else { O_QTY[2].load(Ordering::Relaxed) };
    let q3 = if slot == 3 { qty } else { O_QTY[3].load(Ordering::Relaxed) };

    let max_pos = MAX_POS.load(Ordering::Relaxed);
    let net_pos = NET_POS.load(Ordering::Relaxed);
    if side_u8 == SIDE_BUY {
        let next_buy = sum4_checked(
            slot_side_qty(na0, s0, q0, SIDE_BUY),
            slot_side_qty(na1, s1, q1, SIDE_BUY),
            slot_side_qty(na2, s2, q2, SIDE_BUY),
            slot_side_qty(na3, s3, q3, SIDE_BUY),
        );
        if next_buy < 0 || !fits_long_limit(net_pos, next_buy, max_pos) {
            return 0;
        }
        OPEN_BUY_QTY.store(next_buy, Ordering::Relaxed);
    } else {
        let next_sell = sum4_checked(
            slot_side_qty(na0, s0, q0, SIDE_SELL),
            slot_side_qty(na1, s1, q1, SIDE_SELL),
            slot_side_qty(na2, s2, q2, SIDE_SELL),
            slot_side_qty(na3, s3, q3, SIDE_SELL),
        );
        if next_sell < 0 || !fits_short_limit(net_pos, next_sell, max_pos) {
            return 0;
        }
        OPEN_SELL_QTY.store(next_sell, Ordering::Relaxed);
    }

    write_slot(slot, 1, side_u8, qty, notional);
    OPEN_NOTIONAL.store(next_not, Ordering::Relaxed);
    1
}

/// MUTANT 1 (SEC 15c3-5 kill-switch bypass on cancel/replace):
/// Forgets to check `KILL_SWITCH != 0`, allowing a rogue strategy to modify price/qty
/// on live orders even after the emergency kill switch has been tripped!
#[unsafe(no_mangle)]
pub extern "C" fn cancel_replace_buggy_bypasses_kill_switch(
    slot: i32,
    new_price: i64,
    new_qty: i64,
) -> i32 {
    // BUG: missing `|| KILL_SWITCH.load(Ordering::Relaxed) != 0`!
    if RISK_INIT.load(Ordering::Relaxed) != 1 {
        return 0;
    }
    if slot < 0 || slot >= 4 || new_price <= 0 || new_qty <= 0 {
        return 0;
    }

    let a0 = O_ACTIVE[0].load(Ordering::Relaxed);
    let a1 = O_ACTIVE[1].load(Ordering::Relaxed);
    let a2 = O_ACTIVE[2].load(Ordering::Relaxed);
    let a3 = O_ACTIVE[3].load(Ordering::Relaxed);
    if select_u8(slot, a0, a1, a2, a3) != 1 {
        return 0;
    }

    let s0 = O_SIDE[0].load(Ordering::Relaxed);
    let s1 = O_SIDE[1].load(Ordering::Relaxed);
    let s2 = O_SIDE[2].load(Ordering::Relaxed);
    let s3 = O_SIDE[3].load(Ordering::Relaxed);
    let cur_side = select_u8(slot, s0, s1, s2, s3);
    if cur_side != SIDE_BUY && cur_side != SIDE_SELL {
        return 0;
    }

    let max_ord = MAX_ORDER_NOTIONAL.load(Ordering::Relaxed);
    let ref_px = REF_PRICE.load(Ordering::Relaxed);
    let collar = COLLAR_BPS.load(Ordering::Relaxed);

    if call_checked_notional(new_price, new_qty, max_ord) == 0 {
        return 0;
    }
    if call_price_collar_ok(new_price, ref_px, collar) == 0 {
        return 0;
    }

    let new_notional = new_price.wrapping_mul(new_qty);
    if new_notional <= 0 || new_notional > max_ord {
        return 0;
    }

    let max_cred = MAX_CREDIT.load(Ordering::Relaxed);
    let n0 = if slot == 0 { new_notional } else { O_NOTIONAL[0].load(Ordering::Relaxed) };
    let n1 = if slot == 1 { new_notional } else { O_NOTIONAL[1].load(Ordering::Relaxed) };
    let n2 = if slot == 2 { new_notional } else { O_NOTIONAL[2].load(Ordering::Relaxed) };
    let n3 = if slot == 3 { new_notional } else { O_NOTIONAL[3].load(Ordering::Relaxed) };
    let next_not = sum4_checked(n0, n1, n2, n3);
    if next_not < 0 || next_not > max_cred {
        return 0;
    }

    let q0 = if slot == 0 { new_qty } else { O_QTY[0].load(Ordering::Relaxed) };
    let q1 = if slot == 1 { new_qty } else { O_QTY[1].load(Ordering::Relaxed) };
    let q2 = if slot == 2 { new_qty } else { O_QTY[2].load(Ordering::Relaxed) };
    let q3 = if slot == 3 { new_qty } else { O_QTY[3].load(Ordering::Relaxed) };

    let max_pos = MAX_POS.load(Ordering::Relaxed);
    let net_pos = NET_POS.load(Ordering::Relaxed);
    if cur_side == SIDE_BUY {
        let next_buy = sum4_checked(
            slot_side_qty(a0, s0, q0, SIDE_BUY),
            slot_side_qty(a1, s1, q1, SIDE_BUY),
            slot_side_qty(a2, s2, q2, SIDE_BUY),
            slot_side_qty(a3, s3, q3, SIDE_BUY),
        );
        if next_buy < 0 || !fits_long_limit(net_pos, next_buy, max_pos) {
            return 0;
        }
        OPEN_BUY_QTY.store(next_buy, Ordering::Relaxed);
    } else {
        let next_sell = sum4_checked(
            slot_side_qty(a0, s0, q0, SIDE_SELL),
            slot_side_qty(a1, s1, q1, SIDE_SELL),
            slot_side_qty(a2, s2, q2, SIDE_SELL),
            slot_side_qty(a3, s3, q3, SIDE_SELL),
        );
        if next_sell < 0 || !fits_short_limit(net_pos, next_sell, max_pos) {
            return 0;
        }
        OPEN_SELL_QTY.store(next_sell, Ordering::Relaxed);
    }

    if slot == 0 {
        write_replace_slot_at::<0>(new_qty, new_notional);
    } else if slot == 1 {
        write_replace_slot_at::<1>(new_qty, new_notional);
    } else if slot == 2 {
        write_replace_slot_at::<2>(new_qty, new_notional);
    } else {
        write_replace_slot_at::<3>(new_qty, new_notional);
    }
    OPEN_NOTIONAL.store(next_not, Ordering::Relaxed);
    1
}

/// MUTANT 2 (double credit release / credit underflow):
/// Releases `o_notional[slot]` and `o_qty[slot]` from aggregate risk counters
/// WITHOUT clearing `o_active[slot]`, allowing duplicate cancel acks to underflow `open_notional`
/// and manufacture infinite phantom trading credit!
#[unsafe(no_mangle)]
pub extern "C" fn on_cancel_buggy_double_release(slot: i32) -> i32 {
    if RISK_INIT.load(Ordering::Relaxed) != 1 || slot < 0 || slot >= 4 {
        return 0;
    }
    if load_o_active(slot) != 1 {
        return 0;
    }
    let old_qty = select_i64(
        slot,
        O_QTY[0].load(Ordering::Relaxed),
        O_QTY[1].load(Ordering::Relaxed),
        O_QTY[2].load(Ordering::Relaxed),
        O_QTY[3].load(Ordering::Relaxed),
    );
    let old_notional = load_o_notional(slot);
    let cur_side = select_u8(
        slot,
        O_SIDE[0].load(Ordering::Relaxed),
        O_SIDE[1].load(Ordering::Relaxed),
        O_SIDE[2].load(Ordering::Relaxed),
        O_SIDE[3].load(Ordering::Relaxed),
    );
    let open_not = OPEN_NOTIONAL.load(Ordering::Relaxed);

    if cur_side == SIDE_BUY {
        OPEN_BUY_QTY.store(
            OPEN_BUY_QTY.load(Ordering::Relaxed).wrapping_sub(old_qty),
            Ordering::Relaxed,
        );
    } else if cur_side == SIDE_SELL {
        OPEN_SELL_QTY.store(
            OPEN_SELL_QTY.load(Ordering::Relaxed).wrapping_sub(old_qty),
            Ordering::Relaxed,
        );
    } else {
        return 0;
    }
    // BUG: forgets to clear `O_ACTIVE[slot] = 0`, `O_QTY[slot] = 0`, `O_NOTIONAL[slot] = 0`!
    OPEN_NOTIONAL.store(open_not.wrapping_sub(old_notional), Ordering::Relaxed);
    1
}

/// MUTANT 3 (64-bit signed notional overflow fat-finger bypass):
/// Skips Layer-1 `checked_notional` and uses naive `price.wrapping_mul(qty) <= max_order_notional`,
/// letting a fat-finger order wrap `price * qty` modulo 2^64 and bypass `max_order_notional`!
#[unsafe(no_mangle)]
pub extern "C" fn submit_order_buggy_notional_overflow(
    slot: i32,
    side: i32,
    price: i64,
    qty: i64,
) -> i32 {
    if RISK_INIT.load(Ordering::Relaxed) != 1 || KILL_SWITCH.load(Ordering::Relaxed) != 0 {
        return 0;
    }
    if slot < 0
        || slot >= 4
        || (side != (SIDE_BUY as i32) && side != (SIDE_SELL as i32))
        || price <= 0
        || qty <= 0
    {
        return 0;
    }

    let a0 = O_ACTIVE[0].load(Ordering::Relaxed);
    let a1 = O_ACTIVE[1].load(Ordering::Relaxed);
    let a2 = O_ACTIVE[2].load(Ordering::Relaxed);
    let a3 = O_ACTIVE[3].load(Ordering::Relaxed);
    if select_u8(slot, a0, a1, a2, a3) != 0 {
        return 0;
    }

    let max_ord = MAX_ORDER_NOTIONAL.load(Ordering::Relaxed);
    let max_cred = MAX_CREDIT.load(Ordering::Relaxed);
    let ref_px = REF_PRICE.load(Ordering::Relaxed);
    let collar = COLLAR_BPS.load(Ordering::Relaxed);

    if call_price_collar_ok(price, ref_px, collar) == 0 {
        return 0;
    }

    // BUG: naive 64-bit wrapping multiplication instead of Layer-1 `checked_notional`!
    let notional = price.wrapping_mul(qty);
    if notional > max_ord {
        return 0;
    }

    let open_not = OPEN_NOTIONAL.load(Ordering::Relaxed);
    if open_not < 0 || open_not > max_cred || notional > max_cred.wrapping_sub(open_not) {
        return 0;
    }

    let side_u8 = side as u8;
    let na0 = if slot == 0 { 1 } else { a0 };
    let na1 = if slot == 1 { 1 } else { a1 };
    let na2 = if slot == 2 { 1 } else { a2 };
    let na3 = if slot == 3 { 1 } else { a3 };
    let s0 = if slot == 0 { side_u8 } else { O_SIDE[0].load(Ordering::Relaxed) };
    let s1 = if slot == 1 { side_u8 } else { O_SIDE[1].load(Ordering::Relaxed) };
    let s2 = if slot == 2 { side_u8 } else { O_SIDE[2].load(Ordering::Relaxed) };
    let s3 = if slot == 3 { side_u8 } else { O_SIDE[3].load(Ordering::Relaxed) };
    let q0 = if slot == 0 { qty } else { O_QTY[0].load(Ordering::Relaxed) };
    let q1 = if slot == 1 { qty } else { O_QTY[1].load(Ordering::Relaxed) };
    let q2 = if slot == 2 { qty } else { O_QTY[2].load(Ordering::Relaxed) };
    let q3 = if slot == 3 { qty } else { O_QTY[3].load(Ordering::Relaxed) };

    let max_pos = MAX_POS.load(Ordering::Relaxed);
    let net_pos = NET_POS.load(Ordering::Relaxed);
    if side_u8 == SIDE_BUY {
        let next_buy = sum4_checked(
            slot_side_qty(na0, s0, q0, SIDE_BUY),
            slot_side_qty(na1, s1, q1, SIDE_BUY),
            slot_side_qty(na2, s2, q2, SIDE_BUY),
            slot_side_qty(na3, s3, q3, SIDE_BUY),
        );
        if next_buy < 0 || !fits_long_limit(net_pos, next_buy, max_pos) {
            return 0;
        }
        OPEN_BUY_QTY.store(next_buy, Ordering::Relaxed);
    } else {
        let next_sell = sum4_checked(
            slot_side_qty(na0, s0, q0, SIDE_SELL),
            slot_side_qty(na1, s1, q1, SIDE_SELL),
            slot_side_qty(na2, s2, q2, SIDE_SELL),
            slot_side_qty(na3, s3, q3, SIDE_SELL),
        );
        if next_sell < 0 || !fits_short_limit(net_pos, next_sell, max_pos) {
            return 0;
        }
        OPEN_SELL_QTY.store(next_sell, Ordering::Relaxed);
    }

    write_slot(slot, 1, side_u8, qty, notional);
    OPEN_NOTIONAL.store(open_not.wrapping_add(notional), Ordering::Relaxed);
    1
}

/// Same inductive invariant `inv_risk_gate()` as `s3_3_pretrade_risk_gate.rs`.
#[unsafe(no_mangle)]
pub extern "C" fn inv_risk_gate() -> i32 {
    let init = RISK_INIT.load(Ordering::Relaxed);
    let ks = KILL_SWITCH.load(Ordering::Relaxed);
    let max_ord = MAX_ORDER_NOTIONAL.load(Ordering::Relaxed);
    let max_cred = MAX_CREDIT.load(Ordering::Relaxed);
    let max_pos = MAX_POS.load(Ordering::Relaxed);
    let ref_px = REF_PRICE.load(Ordering::Relaxed);
    let collar = COLLAR_BPS.load(Ordering::Relaxed);

    let net_pos = NET_POS.load(Ordering::Relaxed);
    let open_buy = OPEN_BUY_QTY.load(Ordering::Relaxed);
    let open_sell = OPEN_SELL_QTY.load(Ordering::Relaxed);
    let open_not = OPEN_NOTIONAL.load(Ordering::Relaxed);

    let a0 = O_ACTIVE[0].load(Ordering::Relaxed);
    let a1 = O_ACTIVE[1].load(Ordering::Relaxed);
    let a2 = O_ACTIVE[2].load(Ordering::Relaxed);
    let a3 = O_ACTIVE[3].load(Ordering::Relaxed);

    let s0 = O_SIDE[0].load(Ordering::Relaxed);
    let s1 = O_SIDE[1].load(Ordering::Relaxed);
    let s2 = O_SIDE[2].load(Ordering::Relaxed);
    let s3 = O_SIDE[3].load(Ordering::Relaxed);

    let q0 = O_QTY[0].load(Ordering::Relaxed);
    let q1 = O_QTY[1].load(Ordering::Relaxed);
    let q2 = O_QTY[2].load(Ordering::Relaxed);
    let q3 = O_QTY[3].load(Ordering::Relaxed);

    let n0 = O_NOTIONAL[0].load(Ordering::Relaxed);
    let n1 = O_NOTIONAL[1].load(Ordering::Relaxed);
    let n2 = O_NOTIONAL[2].load(Ordering::Relaxed);
    let n3 = O_NOTIONAL[3].load(Ordering::Relaxed);

    if init == 0 {
        if (ks | a0 | a1 | a2 | a3 | s0 | s1 | s2 | s3) == 0
            && (max_ord | max_cred | max_pos | ref_px | collar | net_pos | open_buy | open_sell
                | open_not | q0 | q1 | q2 | q3 | n0 | n1 | n2 | n3)
                == 0
        {
            return 1;
        }
        return 0;
    }

    if init != 1 || ks > 1 {
        return 0;
    }
    if max_ord <= 0 || max_cred <= 0 || max_pos <= 0 || ref_px <= 0 || collar < 0 || collar > 10_000
    {
        return 0;
    }
    if (open_buy | open_sell | open_not) < 0 || open_not > max_cred {
        return 0;
    }
    if !fits_long_limit(net_pos, open_buy, max_pos)
        || !fits_short_limit(net_pos, open_sell, max_pos)
    {
        return 0;
    }

    if !inv_order_slot(a0, s0, q0, n0, max_ord)
        || !inv_order_slot(a1, s1, q1, n1, max_ord)
        || !inv_order_slot(a2, s2, q2, n2, max_ord)
        || !inv_order_slot(a3, s3, q3, n3, max_ord)
    {
        return 0;
    }

    if !sum4_eq(n0, n1, n2, n3, open_not) {
        return 0;
    }

    if !sum4_eq(
        slot_side_qty(a0, s0, q0, SIDE_BUY),
        slot_side_qty(a1, s1, q1, SIDE_BUY),
        slot_side_qty(a2, s2, q2, SIDE_BUY),
        slot_side_qty(a3, s3, q3, SIDE_BUY),
        open_buy,
    ) {
        return 0;
    }

    if !sum4_eq(
        slot_side_qty(a0, s0, q0, SIDE_SELL),
        slot_side_qty(a1, s1, q1, SIDE_SELL),
        slot_side_qty(a2, s2, q2, SIDE_SELL),
        slot_side_qty(a3, s3, q3, SIDE_SELL),
        open_sell,
    ) {
        return 0;
    }
    1
}

/// Contract harness exposing Mutant 1 (`cancel_replace_buggy_bypasses_kill_switch`):
/// Expected result: FALSIFIED (`r_rep == 1` while `kill_switch == 1`).
#[unsafe(no_mangle)]
pub extern "C" fn contract_kill_switch_blocks_new_and_replace_buggy(
    slot: i32,
    side: i32,
    price: i64,
    qty: i64,
) -> i32 {
    assume(inv_risk_gate() != 0);
    assume(RISK_INIT.load(Ordering::Relaxed) == 1);
    assume(KILL_SWITCH.load(Ordering::Relaxed) != 0);

    let old_not = OPEN_NOTIONAL.load(Ordering::Relaxed);
    let old_buy = OPEN_BUY_QTY.load(Ordering::Relaxed);
    let old_sell = OPEN_SELL_QTY.load(Ordering::Relaxed);

    let r_sub = submit_order(slot, side, price, qty);
    let r_rep = cancel_replace_buggy_bypasses_kill_switch(slot, price, qty);

    assert_prop(r_sub == 0);
    assert_prop(r_rep == 0);
    assert_prop(OPEN_NOTIONAL.load(Ordering::Relaxed) == old_not);
    assert_prop(OPEN_BUY_QTY.load(Ordering::Relaxed) == old_buy);
    assert_prop(OPEN_SELL_QTY.load(Ordering::Relaxed) == old_sell);
    1
}

/// Contract harness exposing Mutant 2 (`on_cancel_buggy_double_release`):
/// Expected result: FALSIFIED (`r2 == 1`, `open_notional` double-subtracted).
#[unsafe(no_mangle)]
pub extern "C" fn contract_cancel_no_double_release_buggy(slot: i32) -> i32 {
    assume(inv_risk_gate() != 0);
    assume(RISK_INIT.load(Ordering::Relaxed) == 1);
    assume(slot >= 0 && slot < 4);
    assume(load_o_active(slot) == 1);

    let r1 = on_cancel_buggy_double_release(slot);
    let after_first = OPEN_NOTIONAL.load(Ordering::Relaxed);
    let r2 = on_cancel_buggy_double_release(slot);

    if r1 == 1 {
        assert_prop(load_o_active(slot) == 0);
        assert_prop(load_o_notional(slot) == 0);
        assert_prop(r2 == 0);
        assert_prop(OPEN_NOTIONAL.load(Ordering::Relaxed) == after_first);
        assert_prop(OPEN_NOTIONAL.load(Ordering::Relaxed) >= 0);
        assert_prop(sum4_eq(
            O_NOTIONAL[0].load(Ordering::Relaxed),
            O_NOTIONAL[1].load(Ordering::Relaxed),
            O_NOTIONAL[2].load(Ordering::Relaxed),
            O_NOTIONAL[3].load(Ordering::Relaxed),
            after_first,
        ));
    }
    1
}

/// Contract harness exposing Mutant 3 (`submit_order_buggy_notional_overflow`):
/// Expected result: FALSIFIED (64-bit wraparound lets `price * qty` bypass `max_order_notional`).
#[unsafe(no_mangle)]
pub extern "C" fn contract_submit_no_notional_overflow_buggy(
    slot: i32,
    side: i32,
    price: i64,
    qty: i64,
) -> i32 {
    assume(inv_risk_gate() != 0);
    assume(RISK_INIT.load(Ordering::Relaxed) == 1);
    assume(KILL_SWITCH.load(Ordering::Relaxed) == 0);
    assume(slot >= 0 && slot < 4);
    assume(load_o_active(slot) == 0);
    assume(side == (SIDE_BUY as i32) || side == (SIDE_SELL as i32));

    let ok = submit_order_buggy_notional_overflow(slot, side, price, qty);
    if ok == 1 {
        let max_ord = MAX_ORDER_NOTIONAL.load(Ordering::Relaxed);
        let ref_px = REF_PRICE.load(Ordering::Relaxed);
        let collar = COLLAR_BPS.load(Ordering::Relaxed);
        assert_prop(price > 0 && qty > 0);
        assert_prop(price <= max_ord && qty <= max_ord);
        assert_prop(call_checked_notional(price, qty, max_ord) == 1);
        assert_prop(call_price_collar_ok(price, ref_px, collar) == 1);
    }
    1
}
