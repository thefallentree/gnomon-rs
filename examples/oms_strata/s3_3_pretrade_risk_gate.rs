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

// Multi-layer Strata composition: Layer-3 Risk Gate imports verified Layer-1 S1.1 ops.
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

// AccountRiskState limits & kill switch in fixed linear memory (globals: 0, zero .rodata).
static RISK_INIT: AtomicU8 = AtomicU8::new(0);
static KILL_SWITCH: AtomicU8 = AtomicU8::new(0);
static MAX_ORDER_NOTIONAL: AtomicI64 = AtomicI64::new(0);
static MAX_CREDIT: AtomicI64 = AtomicI64::new(0);
static MAX_POS: AtomicI64 = AtomicI64::new(0);
static REF_PRICE: AtomicI64 = AtomicI64::new(0);
static COLLAR_BPS: AtomicI64 = AtomicI64::new(0);

// AccountRiskState live exposure counters.
static NET_POS: AtomicI64 = AtomicI64::new(0);
static OPEN_BUY_QTY: AtomicI64 = AtomicI64::new(0);
static OPEN_SELL_QTY: AtomicI64 = AtomicI64::new(0);
static OPEN_NOTIONAL: AtomicI64 = AtomicI64::new(0);

// 4 tracked live order slots in contiguous arrays (zero `.rodata`, zero bounds traps).
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

/// Branchless, overflow-safe exact 4-way non-negative sum in Z via symmetric depth-2 tree.
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

/// Branchless, overflow-safe exact 4-way non-negative sum equality check: `a + b + c + d == total` in Z.
#[inline(always)]
fn sum4_eq(a: i64, b: i64, c: i64, d: i64, total: i64) -> bool {
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
fn select_i64(slot: i32, v0: i64, v1: i64, v2: i64, v3: i64) -> i64 {
    let v01 = if slot == 0 { v0 } else { v1 };
    let v23 = if slot == 2 { v2 } else { v3 };
    if (slot & 2) == 0 { v01 } else { v23 }
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

/// Side-filtered slot quantity (`qty` iff `side == target_side`, else `0`).
/// Equivalent to `active == 1 && side == target_side` under `inv_order_slot`.
#[inline(always)]
fn side_qty(side: u8, qty: i64, target_side: u8) -> i64 {
    if side == target_side { qty } else { 0 }
}

#[inline(always)]
fn inv_order_slot(active: u8, side: u8, qty: i64, notional: i64, max_ord: i64) -> bool {
    let inactive_ok = (active == 0) & (side == SIDE_NONE) & (qty == 0) & (notional == 0);
    let active_ok = (active == 1)
        & ((side == SIDE_BUY) | (side == SIDE_SELL))
        & (qty > 0)
        & (notional > 0)
        & (notional <= max_ord);
    inactive_ok | active_ok
}

/// Overflow-safe worst-case long & short position bounds:
/// `max_pos > 0`, `-max_pos <= net_pos <= max_pos`,
/// `net_pos + open_buy <= max_pos`, and `net_pos - open_sell >= -max_pos`.
#[inline(always)]
fn fits_pos_limits(net_pos: i64, open_buy: i64, open_sell: i64, max_pos: i64) -> bool {
    let neg_max_pos = 0i64.wrapping_sub(max_pos);
    let buy_room_u = (max_pos as u64).wrapping_sub(net_pos as u64);
    let sell_room_u = (net_pos as u64).wrapping_sub(neg_max_pos as u64);
    (max_pos > 0)
        & (open_buy >= 0)
        & (open_sell >= 0)
        & (net_pos >= neg_max_pos)
        & (net_pos <= max_pos)
        & ((open_buy as u64) <= buy_room_u)
        & ((open_sell as u64) <= sell_room_u)
}

/// Initialize the SEC 15c3-5 pre-trade risk gate with configured account limits.
/// Returns `0` (no-op, preserving valid state) if limits are invalid; returns `1` on success.
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

    O_ACTIVE[0].store(0, Ordering::Relaxed);
    O_ACTIVE[1].store(0, Ordering::Relaxed);
    O_ACTIVE[2].store(0, Ordering::Relaxed);
    O_ACTIVE[3].store(0, Ordering::Relaxed);

    O_SIDE[0].store(SIDE_NONE, Ordering::Relaxed);
    O_SIDE[1].store(SIDE_NONE, Ordering::Relaxed);
    O_SIDE[2].store(SIDE_NONE, Ordering::Relaxed);
    O_SIDE[3].store(SIDE_NONE, Ordering::Relaxed);

    O_QTY[0].store(0, Ordering::Relaxed);
    O_QTY[1].store(0, Ordering::Relaxed);
    O_QTY[2].store(0, Ordering::Relaxed);
    O_QTY[3].store(0, Ordering::Relaxed);

    O_NOTIONAL[0].store(0, Ordering::Relaxed);
    O_NOTIONAL[1].store(0, Ordering::Relaxed);
    O_NOTIONAL[2].store(0, Ordering::Relaxed);
    O_NOTIONAL[3].store(0, Ordering::Relaxed);
    1
}

/// Pre-trade risk gate check & admission for a new order into `slot` (`0..=3`).
/// Enforces: kill switch, Layer-1 S1.1 `checked_notional` & `price_collar_ok`,
/// aggregate credit limit (`open_notional <= max_credit`), and worst-case long/short position bounds.
#[unsafe(no_mangle)]
pub extern "C" fn submit_order(slot: i32, side: i32, price: i64, qty: i64) -> i32 {
    let init = RISK_INIT.load(Ordering::Relaxed);
    let ks = KILL_SWITCH.load(Ordering::Relaxed);
    let max_ord = MAX_ORDER_NOTIONAL.load(Ordering::Relaxed);
    let max_cred = MAX_CREDIT.load(Ordering::Relaxed);
    let max_pos = MAX_POS.load(Ordering::Relaxed);
    let ref_px = REF_PRICE.load(Ordering::Relaxed);
    let collar = COLLAR_BPS.load(Ordering::Relaxed);
    let net_pos = NET_POS.load(Ordering::Relaxed);
    let old_buy = OPEN_BUY_QTY.load(Ordering::Relaxed);
    let old_sell = OPEN_SELL_QTY.load(Ordering::Relaxed);
    let old_not = OPEN_NOTIONAL.load(Ordering::Relaxed);

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

    // Layer-1 S1.1 Stratum checks.
    let cn_ok = call_checked_notional(price, qty, max_ord) != 0;
    let col_ok = call_price_collar_ok(price, ref_px, collar) != 0;
    let notional = price.wrapping_mul(qty);
    let side_u8 = side as u8;

    let c_a0 = if slot == 0 { 1 } else { a0 };
    let c_a1 = if slot == 1 { 1 } else { a1 };
    let c_a2 = if slot == 2 { 1 } else { a2 };
    let c_a3 = if slot == 3 { 1 } else { a3 };
    let c_s0 = if slot == 0 { side_u8 } else { s0 };
    let c_s1 = if slot == 1 { side_u8 } else { s1 };
    let c_s2 = if slot == 2 { side_u8 } else { s2 };
    let c_s3 = if slot == 3 { side_u8 } else { s3 };
    let c_q0 = if slot == 0 { qty } else { q0 };
    let c_q1 = if slot == 1 { qty } else { q1 };
    let c_q2 = if slot == 2 { qty } else { q2 };
    let c_q3 = if slot == 3 { qty } else { q3 };
    let c_n0 = if slot == 0 { notional } else { n0 };
    let c_n1 = if slot == 1 { notional } else { n1 };
    let c_n2 = if slot == 2 { notional } else { n2 };
    let c_n3 = if slot == 3 { notional } else { n3 };

    let next_not = sum4_checked(c_n0, c_n1, c_n2, c_n3);
    let next_buy = sum4_checked(
        side_qty(c_s0, c_q0, SIDE_BUY),
        side_qty(c_s1, c_q1, SIDE_BUY),
        side_qty(c_s2, c_q2, SIDE_BUY),
        side_qty(c_s3, c_q3, SIDE_BUY),
    );
    let next_sell = sum4_checked(
        side_qty(c_s0, c_q0, SIDE_SELL),
        side_qty(c_s1, c_q1, SIDE_SELL),
        side_qty(c_s2, c_q2, SIDE_SELL),
        side_qty(c_s3, c_q3, SIDE_SELL),
    );

    let ok = (init == 1)
        & (ks == 0)
        & (slot >= 0)
        & (slot < 4)
        & ((side == (SIDE_BUY as i32)) | (side == (SIDE_SELL as i32)))
        & (price > 0)
        & (qty > 0)
        & (select_u8(slot, a0, a1, a2, a3) == 0)
        & cn_ok
        & col_ok
        & (notional > 0)
        & (notional <= max_ord)
        & (next_not >= 0)
        & (next_not <= max_cred)
        & (next_buy >= 0)
        & (next_sell >= 0)
        & fits_pos_limits(net_pos, next_buy, next_sell, max_pos);

    O_ACTIVE[0].store(if ok { c_a0 } else { a0 }, Ordering::Relaxed);
    O_ACTIVE[1].store(if ok { c_a1 } else { a1 }, Ordering::Relaxed);
    O_ACTIVE[2].store(if ok { c_a2 } else { a2 }, Ordering::Relaxed);
    O_ACTIVE[3].store(if ok { c_a3 } else { a3 }, Ordering::Relaxed);
    O_SIDE[0].store(if ok { c_s0 } else { s0 }, Ordering::Relaxed);
    O_SIDE[1].store(if ok { c_s1 } else { s1 }, Ordering::Relaxed);
    O_SIDE[2].store(if ok { c_s2 } else { s2 }, Ordering::Relaxed);
    O_SIDE[3].store(if ok { c_s3 } else { s3 }, Ordering::Relaxed);
    O_QTY[0].store(if ok { c_q0 } else { q0 }, Ordering::Relaxed);
    O_QTY[1].store(if ok { c_q1 } else { q1 }, Ordering::Relaxed);
    O_QTY[2].store(if ok { c_q2 } else { q2 }, Ordering::Relaxed);
    O_QTY[3].store(if ok { c_q3 } else { q3 }, Ordering::Relaxed);
    O_NOTIONAL[0].store(if ok { c_n0 } else { n0 }, Ordering::Relaxed);
    O_NOTIONAL[1].store(if ok { c_n1 } else { n1 }, Ordering::Relaxed);
    O_NOTIONAL[2].store(if ok { c_n2 } else { n2 }, Ordering::Relaxed);
    O_NOTIONAL[3].store(if ok { c_n3 } else { n3 }, Ordering::Relaxed);
    OPEN_NOTIONAL.store(if ok { next_not } else { old_not }, Ordering::Relaxed);
    OPEN_BUY_QTY.store(if ok { next_buy } else { old_buy }, Ordering::Relaxed);
    OPEN_SELL_QTY.store(if ok { next_sell } else { old_sell }, Ordering::Relaxed);
    if ok { 1 } else { 0 }
}

/// Pre-trade risk gate check & update for cancel/replace on an active order slot.
/// Enforces kill switch, S1.1 `checked_notional` & `price_collar_ok`, credit headroom, and position bounds.
#[unsafe(no_mangle)]
pub extern "C" fn cancel_replace_order(slot: i32, new_price: i64, new_qty: i64) -> i32 {
    let init = RISK_INIT.load(Ordering::Relaxed);
    let ks = KILL_SWITCH.load(Ordering::Relaxed);
    let max_ord = MAX_ORDER_NOTIONAL.load(Ordering::Relaxed);
    let max_cred = MAX_CREDIT.load(Ordering::Relaxed);
    let max_pos = MAX_POS.load(Ordering::Relaxed);
    let ref_px = REF_PRICE.load(Ordering::Relaxed);
    let collar = COLLAR_BPS.load(Ordering::Relaxed);
    let net_pos = NET_POS.load(Ordering::Relaxed);
    let old_buy = OPEN_BUY_QTY.load(Ordering::Relaxed);
    let old_sell = OPEN_SELL_QTY.load(Ordering::Relaxed);
    let old_not = OPEN_NOTIONAL.load(Ordering::Relaxed);

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

    let cur_active = select_u8(slot, a0, a1, a2, a3);
    let cur_side = select_u8(slot, s0, s1, s2, s3);

    // Layer-1 S1.1 Stratum checks.
    let cn_ok = call_checked_notional(new_price, new_qty, max_ord) != 0;
    let col_ok = call_price_collar_ok(new_price, ref_px, collar) != 0;
    let new_notional = new_price.wrapping_mul(new_qty);

    let c_q0 = if slot == 0 { new_qty } else { q0 };
    let c_q1 = if slot == 1 { new_qty } else { q1 };
    let c_q2 = if slot == 2 { new_qty } else { q2 };
    let c_q3 = if slot == 3 { new_qty } else { q3 };
    let c_n0 = if slot == 0 { new_notional } else { n0 };
    let c_n1 = if slot == 1 { new_notional } else { n1 };
    let c_n2 = if slot == 2 { new_notional } else { n2 };
    let c_n3 = if slot == 3 { new_notional } else { n3 };

    let next_not = sum4_checked(c_n0, c_n1, c_n2, c_n3);
    let next_buy = sum4_checked(
        side_qty(s0, c_q0, SIDE_BUY),
        side_qty(s1, c_q1, SIDE_BUY),
        side_qty(s2, c_q2, SIDE_BUY),
        side_qty(s3, c_q3, SIDE_BUY),
    );
    let next_sell = sum4_checked(
        side_qty(s0, c_q0, SIDE_SELL),
        side_qty(s1, c_q1, SIDE_SELL),
        side_qty(s2, c_q2, SIDE_SELL),
        side_qty(s3, c_q3, SIDE_SELL),
    );

    let ok = (init == 1)
        & (ks == 0)
        & (slot >= 0)
        & (slot < 4)
        & (new_price > 0)
        & (new_qty > 0)
        & (cur_active == 1)
        & ((cur_side == SIDE_BUY) | (cur_side == SIDE_SELL))
        & cn_ok
        & col_ok
        & (new_notional > 0)
        & (new_notional <= max_ord)
        & (next_not >= 0)
        & (next_not <= max_cred)
        & (next_buy >= 0)
        & (next_sell >= 0)
        & fits_pos_limits(net_pos, next_buy, next_sell, max_pos);

    O_QTY[0].store(if ok { c_q0 } else { q0 }, Ordering::Relaxed);
    O_QTY[1].store(if ok { c_q1 } else { q1 }, Ordering::Relaxed);
    O_QTY[2].store(if ok { c_q2 } else { q2 }, Ordering::Relaxed);
    O_QTY[3].store(if ok { c_q3 } else { q3 }, Ordering::Relaxed);
    O_NOTIONAL[0].store(if ok { c_n0 } else { n0 }, Ordering::Relaxed);
    O_NOTIONAL[1].store(if ok { c_n1 } else { n1 }, Ordering::Relaxed);
    O_NOTIONAL[2].store(if ok { c_n2 } else { n2 }, Ordering::Relaxed);
    O_NOTIONAL[3].store(if ok { c_n3 } else { n3 }, Ordering::Relaxed);
    OPEN_NOTIONAL.store(if ok { next_not } else { old_not }, Ordering::Relaxed);
    OPEN_BUY_QTY.store(if ok { next_buy } else { old_buy }, Ordering::Relaxed);
    OPEN_SELL_QTY.store(if ok { next_sell } else { old_sell }, Ordering::Relaxed);
    if ok { 1 } else { 0 }
}

/// Process exchange fill on tracked order `slot` (always permitted even when kill switch is tripped).
/// Converts open buy/sell exposure into `net_pos` and releases slot credit upon full fill.
#[unsafe(no_mangle)]
pub extern "C" fn on_fill(slot: i32, fill_qty: i64) -> i32 {
    let init = RISK_INIT.load(Ordering::Relaxed);
    let max_cred = MAX_CREDIT.load(Ordering::Relaxed);
    let max_pos = MAX_POS.load(Ordering::Relaxed);
    let net_pos = NET_POS.load(Ordering::Relaxed);

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

    let cur_active = select_u8(slot, a0, a1, a2, a3);
    let cur_side = select_u8(slot, s0, s1, s2, s3);
    let old_qty = select_i64(slot, q0, q1, q2, q3);

    let rem_qty = old_qty.wrapping_sub(fill_qty);
    let is_full = rem_qty == 0;

    let c_a0 = if (slot == 0) & is_full { 0 } else { a0 };
    let c_a1 = if (slot == 1) & is_full { 0 } else { a1 };
    let c_a2 = if (slot == 2) & is_full { 0 } else { a2 };
    let c_a3 = if (slot == 3) & is_full { 0 } else { a3 };
    let c_s0 = if (slot == 0) & is_full { SIDE_NONE } else { s0 };
    let c_s1 = if (slot == 1) & is_full { SIDE_NONE } else { s1 };
    let c_s2 = if (slot == 2) & is_full { SIDE_NONE } else { s2 };
    let c_s3 = if (slot == 3) & is_full { SIDE_NONE } else { s3 };
    let c_q0 = if slot == 0 { rem_qty } else { q0 };
    let c_q1 = if slot == 1 { rem_qty } else { q1 };
    let c_q2 = if slot == 2 { rem_qty } else { q2 };
    let c_q3 = if slot == 3 { rem_qty } else { q3 };
    let c_n0 = if (slot == 0) & is_full { 0 } else { n0 };
    let c_n1 = if (slot == 1) & is_full { 0 } else { n1 };
    let c_n2 = if (slot == 2) & is_full { 0 } else { n2 };
    let c_n3 = if (slot == 3) & is_full { 0 } else { n3 };

    let next_not = sum4_checked(c_n0, c_n1, c_n2, c_n3);
    let next_buy = sum4_checked(
        side_qty(s0, c_q0, SIDE_BUY),
        side_qty(s1, c_q1, SIDE_BUY),
        side_qty(s2, c_q2, SIDE_BUY),
        side_qty(s3, c_q3, SIDE_BUY),
    );
    let next_sell = sum4_checked(
        side_qty(s0, c_q0, SIDE_SELL),
        side_qty(s1, c_q1, SIDE_SELL),
        side_qty(s2, c_q2, SIDE_SELL),
        side_qty(s3, c_q3, SIDE_SELL),
    );

    let is_buy = cur_side == SIDE_BUY;
    let pos_ok = if is_buy {
        net_pos <= i64::MAX.wrapping_sub(fill_qty)
    } else {
        net_pos >= i64::MIN.wrapping_add(fill_qty)
    };
    let next_pos = if is_buy {
        net_pos.wrapping_add(fill_qty)
    } else {
        net_pos.wrapping_sub(fill_qty)
    };

    let ok = (init == 1)
        & (slot >= 0)
        & (slot < 4)
        & (fill_qty > 0)
        & (cur_active == 1)
        & (is_buy | (cur_side == SIDE_SELL))
        & (fill_qty <= old_qty)
        & pos_ok
        & (next_not >= 0)
        & (next_not <= max_cred)
        & (next_buy >= 0)
        & (next_sell >= 0)
        & fits_pos_limits(next_pos, next_buy, next_sell, max_pos);

    if !ok {
        return 0;
    }
    O_ACTIVE[0].store(c_a0, Ordering::Relaxed);
    O_ACTIVE[1].store(c_a1, Ordering::Relaxed);
    O_ACTIVE[2].store(c_a2, Ordering::Relaxed);
    O_ACTIVE[3].store(c_a3, Ordering::Relaxed);
    O_SIDE[0].store(c_s0, Ordering::Relaxed);
    O_SIDE[1].store(c_s1, Ordering::Relaxed);
    O_SIDE[2].store(c_s2, Ordering::Relaxed);
    O_SIDE[3].store(c_s3, Ordering::Relaxed);
    O_QTY[0].store(c_q0, Ordering::Relaxed);
    O_QTY[1].store(c_q1, Ordering::Relaxed);
    O_QTY[2].store(c_q2, Ordering::Relaxed);
    O_QTY[3].store(c_q3, Ordering::Relaxed);
    O_NOTIONAL[0].store(c_n0, Ordering::Relaxed);
    O_NOTIONAL[1].store(c_n1, Ordering::Relaxed);
    O_NOTIONAL[2].store(c_n2, Ordering::Relaxed);
    O_NOTIONAL[3].store(c_n3, Ordering::Relaxed);
    NET_POS.store(next_pos, Ordering::Relaxed);
    OPEN_NOTIONAL.store(next_not, Ordering::Relaxed);
    OPEN_BUY_QTY.store(next_buy, Ordering::Relaxed);
    OPEN_SELL_QTY.store(next_sell, Ordering::Relaxed);
    1
}

/// Process exchange cancel on tracked order `slot` (always permitted even when kill switch is tripped).
/// Atomically deactivates `slot` and releases its exact credit & open side qty once and only once.
#[unsafe(no_mangle)]
pub extern "C" fn on_cancel(slot: i32) -> i32 {
    let init = RISK_INIT.load(Ordering::Relaxed);
    let max_cred = MAX_CREDIT.load(Ordering::Relaxed);
    let max_pos = MAX_POS.load(Ordering::Relaxed);
    let net_pos = NET_POS.load(Ordering::Relaxed);
    let old_buy = OPEN_BUY_QTY.load(Ordering::Relaxed);
    let old_sell = OPEN_SELL_QTY.load(Ordering::Relaxed);
    let old_not = OPEN_NOTIONAL.load(Ordering::Relaxed);

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

    let c_a0 = if slot == 0 { 0 } else { a0 };
    let c_a1 = if slot == 1 { 0 } else { a1 };
    let c_a2 = if slot == 2 { 0 } else { a2 };
    let c_a3 = if slot == 3 { 0 } else { a3 };
    let c_s0 = if slot == 0 { SIDE_NONE } else { s0 };
    let c_s1 = if slot == 1 { SIDE_NONE } else { s1 };
    let c_s2 = if slot == 2 { SIDE_NONE } else { s2 };
    let c_s3 = if slot == 3 { SIDE_NONE } else { s3 };
    let c_q0 = if slot == 0 { 0 } else { q0 };
    let c_q1 = if slot == 1 { 0 } else { q1 };
    let c_q2 = if slot == 2 { 0 } else { q2 };
    let c_q3 = if slot == 3 { 0 } else { q3 };
    let c_n0 = if slot == 0 { 0 } else { n0 };
    let c_n1 = if slot == 1 { 0 } else { n1 };
    let c_n2 = if slot == 2 { 0 } else { n2 };
    let c_n3 = if slot == 3 { 0 } else { n3 };

    let next_not = sum4_checked(c_n0, c_n1, c_n2, c_n3);
    let next_buy = sum4_checked(
        side_qty(c_s0, c_q0, SIDE_BUY),
        side_qty(c_s1, c_q1, SIDE_BUY),
        side_qty(c_s2, c_q2, SIDE_BUY),
        side_qty(c_s3, c_q3, SIDE_BUY),
    );
    let next_sell = sum4_checked(
        side_qty(c_s0, c_q0, SIDE_SELL),
        side_qty(c_s1, c_q1, SIDE_SELL),
        side_qty(c_s2, c_q2, SIDE_SELL),
        side_qty(c_s3, c_q3, SIDE_SELL),
    );

    let ok = (init == 1)
        & (slot >= 0)
        & (slot < 4)
        & (select_u8(slot, a0, a1, a2, a3) == 1)
        & (next_not >= 0)
        & (next_not <= max_cred)
        & (next_buy >= 0)
        & (next_sell >= 0)
        & fits_pos_limits(net_pos, next_buy, next_sell, max_pos);

    O_ACTIVE[0].store(if ok { c_a0 } else { a0 }, Ordering::Relaxed);
    O_ACTIVE[1].store(if ok { c_a1 } else { a1 }, Ordering::Relaxed);
    O_ACTIVE[2].store(if ok { c_a2 } else { a2 }, Ordering::Relaxed);
    O_ACTIVE[3].store(if ok { c_a3 } else { a3 }, Ordering::Relaxed);
    O_SIDE[0].store(if ok { c_s0 } else { s0 }, Ordering::Relaxed);
    O_SIDE[1].store(if ok { c_s1 } else { s1 }, Ordering::Relaxed);
    O_SIDE[2].store(if ok { c_s2 } else { s2 }, Ordering::Relaxed);
    O_SIDE[3].store(if ok { c_s3 } else { s3 }, Ordering::Relaxed);
    O_QTY[0].store(if ok { c_q0 } else { q0 }, Ordering::Relaxed);
    O_QTY[1].store(if ok { c_q1 } else { q1 }, Ordering::Relaxed);
    O_QTY[2].store(if ok { c_q2 } else { q2 }, Ordering::Relaxed);
    O_QTY[3].store(if ok { c_q3 } else { q3 }, Ordering::Relaxed);
    O_NOTIONAL[0].store(if ok { c_n0 } else { n0 }, Ordering::Relaxed);
    O_NOTIONAL[1].store(if ok { c_n1 } else { n1 }, Ordering::Relaxed);
    O_NOTIONAL[2].store(if ok { c_n2 } else { n2 }, Ordering::Relaxed);
    O_NOTIONAL[3].store(if ok { c_n3 } else { n3 }, Ordering::Relaxed);
    OPEN_NOTIONAL.store(if ok { next_not } else { old_not }, Ordering::Relaxed);
    OPEN_BUY_QTY.store(if ok { next_buy } else { old_buy }, Ordering::Relaxed);
    OPEN_SELL_QTY.store(if ok { next_sell } else { old_sell }, Ordering::Relaxed);
    if ok { 1 } else { 0 }
}

/// Trip the SEC 15c3-5 emergency kill switch (blocks all subsequent new & cancel/replace orders).
#[unsafe(no_mangle)]
pub extern "C" fn trip_kill_switch() -> i32 {
    if RISK_INIT.load(Ordering::Relaxed) != 1 {
        return 0;
    }
    KILL_SWITCH.store(1, Ordering::Relaxed);
    1
}

/// Full inductive state invariant for the SEC 15c3-5 Pre-Trade Risk Gate (`1` iff all clauses hold):
/// 1. Exact credit conservation (zero leak): `open_notional == sum(o_active[i] ? o_notional[i] : 0)`.
/// 2. Exact open buy/sell quantity conservation across the 4 live order slots.
/// 3. Aggregate credit bound: `0 <= open_notional <= max_credit`.
/// 4. Worst-case long & short position bounds (overflow-free):
///    `net_pos + open_buy_qty <= max_pos` and `net_pos - open_sell_qty >= -max_pos`.
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

    let uninit_ok = (init == 0)
        & ((ks | a0 | a1 | a2 | a3 | s0 | s1 | s2 | s3) == 0)
        & ((max_ord | max_cred | max_pos | ref_px | collar | net_pos | open_buy | open_sell
            | open_not | q0 | q1 | q2 | q3 | n0 | n1 | n2 | n3)
            == 0);

    let active_ok = (init == 1)
        & (ks <= 1)
        & (max_ord > 0)
        & (max_cred > 0)
        & (max_pos > 0)
        & (ref_px > 0)
        & (collar >= 0)
        & (collar <= 10_000)
        & ((open_buy | open_sell | open_not) >= 0)
        & (open_not <= max_cred)
        & fits_pos_limits(net_pos, open_buy, open_sell, max_pos)
        & inv_order_slot(a0, s0, q0, n0, max_ord)
        & inv_order_slot(a1, s1, q1, n1, max_ord)
        & inv_order_slot(a2, s2, q2, n2, max_ord)
        & inv_order_slot(a3, s3, q3, n3, max_ord)
        & sum4_eq(n0, n1, n2, n3, open_not)
        & sum4_eq(
            side_qty(s0, q0, SIDE_BUY),
            side_qty(s1, q1, SIDE_BUY),
            side_qty(s2, q2, SIDE_BUY),
            side_qty(s3, q3, SIDE_BUY),
            open_buy,
        )
        & sum4_eq(
            side_qty(s0, q0, SIDE_SELL),
            side_qty(s1, q1, SIDE_SELL),
            side_qty(s2, q2, SIDE_SELL),
            side_qty(s3, q3, SIDE_SELL),
            open_sell,
        );

    if uninit_ok | active_ok { 1 } else { 0 }
}

/// Inline relational contract:
/// Proves that whenever `kill_switch != 0`, BOTH `submit_order` AND `cancel_replace_order`
/// MUST return `0` and leave all risk counters untouched.
#[unsafe(no_mangle)]
pub extern "C" fn contract_kill_switch_blocks_new_and_replace(
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
    let r_rep = cancel_replace_order(slot, price, qty);

    assert_prop(r_sub == 0);
    assert_prop(r_rep == 0);
    assert_prop(OPEN_NOTIONAL.load(Ordering::Relaxed) == old_not);
    assert_prop(OPEN_BUY_QTY.load(Ordering::Relaxed) == old_buy);
    assert_prop(OPEN_SELL_QTY.load(Ordering::Relaxed) == old_sell);
    1
}

/// Inline relational contract:
/// Proves that cancelling the same active slot twice NEVER double-releases credit or underflows
/// `open_notional`: the first cancel releases `o_notional[slot]` exactly once (`r1 == 1`),
/// and the duplicate cancel is a strict no-op (`r2 == 0`).
#[unsafe(no_mangle)]
pub extern "C" fn contract_cancel_no_double_release(slot: i32) -> i32 {
    assume(inv_risk_gate() != 0);
    assume(RISK_INIT.load(Ordering::Relaxed) == 1);
    assume(slot >= 0 && slot < 4);
    assume(load_o_active(slot) == 1);

    let r1 = on_cancel(slot);
    let after_first = OPEN_NOTIONAL.load(Ordering::Relaxed);
    let r2 = on_cancel(slot);

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

/// Inline relational contract:
/// Proves that any order admitted by `submit_order` satisfies the exact Layer-1 S1.1
/// notional cap (no 64-bit wraparound bypass) and price collar.
#[unsafe(no_mangle)]
pub extern "C" fn contract_submit_no_notional_overflow(
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

    let ok = submit_order(slot, side, price, qty);
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
