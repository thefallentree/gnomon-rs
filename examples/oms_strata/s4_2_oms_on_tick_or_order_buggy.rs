#![no_std]

use core::arch::wasm32::*;
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

// Layer-1 Stratum imports (`S1.1` overflow-free notional cap & 128-bit price collar).
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

static WIRE_DMA_GUARD: [u8; 64] = [0; 64];

const STACK_TOP: i32 = 1_048_576;
const TX_LO: i32 = STACK_TOP + 4_096;
const TX_HI: i32 = STACK_TOP + 16_384;
const RX_LO: i32 = STACK_TOP + 16_384;
const RX_HI: i32 = STACK_TOP + 32_768;
const MIN_LIVE_PAGES: usize = 17;

const MSG_ADD_ORDER: u8 = b'A';
const ADD_ORDER_LEN: usize = 36;
const OUCH_ENTER_ORDER_TAG: u8 = b'O';
const OUCH_FRAME_LEN: usize = 48;
const OUCH_FIRM_ID: u64 = 0x474E_4F4D_4F4E_3031;

const MAX_TICK_PX: i32 = 1_000_000;
const MAX_TICK_QTY: i32 = 10_000;
const MAX_HALF_SPREAD: i32 = 10_000;
const MAX_RISK_NOTIONAL_CAP: i64 = 1_000_000_000;
const RING_CAP: i32 = 8;
const RING_MASK: i32 = 7;

#[repr(C, align(16))]
struct Book4([AtomicI32; 4]);

const fn zero_book4() -> Book4 {
    Book4([
        AtomicI32::new(0),
        AtomicI32::new(0),
        AtomicI32::new(0),
        AtomicI32::new(0),
    ])
}

static BOOK_PX: Book4 = zero_book4();
static BOOK_QTY: Book4 = zero_book4();
static HALF_SPREAD: AtomicI32 = AtomicI32::new(1);

static OMS_INIT: AtomicI32 = AtomicI32::new(0);
static KILL_SWITCH: AtomicI32 = AtomicI32::new(0);
static P_TARGET_QTY: AtomicI32 = AtomicI32::new(0);
static P_CUM_FILLED: AtomicI32 = AtomicI32::new(0);
static P_OPEN_WORST: AtomicI32 = AtomicI32::new(0);

static MAX_ORDER_NOTIONAL: AtomicI64 = AtomicI64::new(0);
static MAX_CREDIT: AtomicI64 = AtomicI64::new(0);
static OPEN_NOTIONAL: AtomicI64 = AtomicI64::new(0);
static REF_PRICE: AtomicI64 = AtomicI64::new(0);
static COLLAR_BPS: AtomicI64 = AtomicI64::new(0);

static MAX_POS: AtomicI32 = AtomicI32::new(0);
static NET_POS: AtomicI32 = AtomicI32::new(0);
static OPEN_BUY_QTY: AtomicI32 = AtomicI32::new(0);
static OPEN_SELL_QTY: AtomicI32 = AtomicI32::new(0);

static LAST_BID_TICK: AtomicI32 = AtomicI32::new(0);
static LAST_ASK_TICK: AtomicI32 = AtomicI32::new(1);

static TX_HEAD: AtomicI32 = AtomicI32::new(0);
static TX_TAIL: AtomicI32 = AtomicI32::new(0);
static TX_CAP: AtomicI32 = AtomicI32::new(RING_CAP);
static TX_SLOTS: [AtomicI64; 8] = [
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
fn load_book4_v128(book: &Book4) -> v128 {
    unsafe { v128_load(book.0.as_ptr() as *const v128) }
}

#[inline(always)]
fn fits_pos_limits(net_pos: i32, open_buy: i32, open_sell: i32, max_pos: i32) -> bool {
    let neg_max = 0i32.wrapping_sub(max_pos);
    let buy_room = (max_pos as u32).wrapping_sub(net_pos as u32);
    let sell_room = (net_pos as u32).wrapping_sub(neg_max as u32);
    (max_pos > 0)
        & (open_buy >= 0)
        & (open_sell >= 0)
        & (net_pos >= neg_max)
        & (net_pos <= max_pos)
        & ((open_buy as u32) <= buy_room)
        & ((open_sell as u32) <= sell_room)
}

#[unsafe(no_mangle)]
pub extern "C" fn init_t2t_state() {
    BOOK_PX.0[0].store(1_000, Ordering::Relaxed);
    BOOK_PX.0[1].store(1_001, Ordering::Relaxed);
    BOOK_PX.0[2].store(1_002, Ordering::Relaxed);
    BOOK_PX.0[3].store(1_003, Ordering::Relaxed);
    BOOK_QTY.0[0].store(100, Ordering::Relaxed);
    BOOK_QTY.0[1].store(200, Ordering::Relaxed);
    BOOK_QTY.0[2].store(300, Ordering::Relaxed);
    BOOK_QTY.0[3].store(400, Ordering::Relaxed);
    HALF_SPREAD.store(1, Ordering::Relaxed);
    OMS_INIT.store(1, Ordering::Relaxed);
    KILL_SWITCH.store(0, Ordering::Relaxed);
    P_TARGET_QTY.store(10_000, Ordering::Relaxed);
    P_CUM_FILLED.store(0, Ordering::Relaxed);
    P_OPEN_WORST.store(0, Ordering::Relaxed);
    MAX_ORDER_NOTIONAL.store(50_000_000, Ordering::Relaxed);
    MAX_CREDIT.store(200_000_000, Ordering::Relaxed);
    OPEN_NOTIONAL.store(0, Ordering::Relaxed);
    REF_PRICE.store(1_000, Ordering::Relaxed);
    COLLAR_BPS.store(500, Ordering::Relaxed);
    MAX_POS.store(10_000, Ordering::Relaxed);
    NET_POS.store(0, Ordering::Relaxed);
    OPEN_BUY_QTY.store(0, Ordering::Relaxed);
    OPEN_SELL_QTY.store(0, Ordering::Relaxed);
    LAST_BID_TICK.store(999, Ordering::Relaxed);
    LAST_ASK_TICK.store(1_001, Ordering::Relaxed);
    TX_HEAD.store(0, Ordering::Relaxed);
    TX_TAIL.store(0, Ordering::Relaxed);
    TX_CAP.store(RING_CAP, Ordering::Relaxed);
}

#[unsafe(no_mangle)]
pub extern "C" fn trip_t2t_kill_switch() -> i32 {
    if OMS_INIT.load(Ordering::Relaxed) != 1 {
        return 0;
    }
    KILL_SWITCH.store(1, Ordering::Relaxed);
    1
}

#[unsafe(no_mangle)]
pub extern "C" fn req_t2t_slices(rx_ptr: i32, rx_len: i32, tx_ptr: i32, tx_len: i32) -> i32 {
    if core::arch::wasm32::memory_size(0) < MIN_LIVE_PAGES {
        return 0;
    }
    let guard_end = (WIRE_DMA_GUARD.as_ptr() as i32).wrapping_add(64);
    let tx_lo = if guard_end > TX_LO { guard_end } else { TX_LO };
    if tx_ptr < tx_lo || tx_ptr > TX_HI || tx_len < 0 || tx_len > TX_HI - tx_ptr {
        return 0;
    }
    if rx_ptr < RX_LO || rx_ptr > RX_HI || rx_len < 0 || rx_len > RX_HI - rx_ptr {
        return 0;
    }
    1
}

#[unsafe(no_mangle)]
pub extern "C" fn req_t2t_kill_switch_tripped(
    rx_ptr: i32,
    rx_len: i32,
    tx_ptr: i32,
    tx_len: i32,
) -> i32 {
    if req_t2t_slices(rx_ptr, rx_len, tx_ptr, tx_len) != 0
        && inv_t2t_oms() != 0
        && KILL_SWITCH.load(Ordering::Relaxed) != 0
    {
        1
    } else {
        0
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn ens_t2t_blocked(
    _rx_ptr: i32,
    _rx_len: i32,
    _tx_ptr: i32,
    _tx_len: i32,
    ret: i32,
) -> i32 {
    if ret == 0 { 1 } else { 0 }
}

#[unsafe(no_mangle)]
pub extern "C" fn inv_t2t_oms() -> i32 {
    let init = OMS_INIT.load(Ordering::Relaxed);
    let ks = KILL_SWITCH.load(Ordering::Relaxed);
    let hs = HALF_SPREAD.load(Ordering::Relaxed);

    let px_v = load_book4_v128(&BOOK_PX);
    let qty_v = load_book4_v128(&BOOK_QTY);
    let px_ok_v = v128_and(
        i32x4_gt(px_v, i32x4_splat(0)),
        i32x4_le(px_v, i32x4_splat(MAX_TICK_PX)),
    );
    let qty_ok_v = v128_and(
        i32x4_ge(qty_v, i32x4_splat(0)),
        i32x4_le(qty_v, i32x4_splat(MAX_TICK_QTY)),
    );

    let p_target = P_TARGET_QTY.load(Ordering::Relaxed);
    let p_cum = P_CUM_FILLED.load(Ordering::Relaxed);
    let p_open = P_OPEN_WORST.load(Ordering::Relaxed);

    let max_ord = MAX_ORDER_NOTIONAL.load(Ordering::Relaxed);
    let max_cred = MAX_CREDIT.load(Ordering::Relaxed);
    let open_not = OPEN_NOTIONAL.load(Ordering::Relaxed);
    let ref_px = REF_PRICE.load(Ordering::Relaxed);
    let collar = COLLAR_BPS.load(Ordering::Relaxed);

    let max_pos = MAX_POS.load(Ordering::Relaxed);
    let net_pos = NET_POS.load(Ordering::Relaxed);
    let open_buy = OPEN_BUY_QTY.load(Ordering::Relaxed);
    let open_sell = OPEN_SELL_QTY.load(Ordering::Relaxed);

    let last_bid = LAST_BID_TICK.load(Ordering::Relaxed);
    let last_ask = LAST_ASK_TICK.load(Ordering::Relaxed);

    let tx_head = TX_HEAD.load(Ordering::Relaxed);
    let tx_tail = TX_TAIL.load(Ordering::Relaxed);
    let tx_cap = TX_CAP.load(Ordering::Relaxed);

    let book_ok = (i32x4_bitmask(v128_and(px_ok_v, qty_ok_v)) == 0xF)
        & (hs >= 1)
        & (hs <= MAX_HALF_SPREAD);
    let parent_ok = (init == 1)
        & ((ks == 0) | (ks == 1))
        & (p_target > 0)
        & ((p_cum | p_open) >= 0)
        & (p_cum <= p_target)
        & (p_open <= p_target.wrapping_sub(p_cum));
    let risk_ok = (max_ord > 0)
        & (max_ord <= MAX_RISK_NOTIONAL_CAP)
        & (max_cred > 0)
        & (max_cred <= MAX_RISK_NOTIONAL_CAP)
        & (open_not >= 0)
        & (open_not <= max_cred)
        & (ref_px > 0)
        & (ref_px <= (MAX_TICK_PX as i64))
        & (collar >= 0)
        & (collar <= 10_000)
        & fits_pos_limits(net_pos, open_buy, open_sell, max_pos);
    let quote_ok = last_bid < last_ask;
    let ring_ok = (tx_cap == RING_CAP)
        & ((tx_tail.wrapping_sub(tx_head) as u32) <= (RING_CAP as u32));

    if book_ok & parent_ok & risk_ok & quote_ok & ring_ok {
        1
    } else {
        0
    }
}

#[inline(always)]
fn write_ouch_tx(
    tx_ptr: i32,
    cl_ord_id: u64,
    side: u8,
    quote_qty: u32,
    symbol: u64,
    quote_px: u64,
) {
    let tx_base = tx_ptr as usize as *mut u8;
    unsafe {
        core::ptr::write(tx_base, OUCH_ENTER_ORDER_TAG);
        core::ptr::write_unaligned(tx_base.add(1) as *mut u64, cl_ord_id.to_be());
        core::ptr::write(tx_base.add(9), side);
        core::ptr::write_unaligned(tx_base.add(10) as *mut u32, quote_qty.to_be());
        core::ptr::write_unaligned(tx_base.add(14) as *mut u64, symbol);
        core::ptr::write_unaligned(tx_base.add(22) as *mut u64, quote_px.to_be());
        core::ptr::write_unaligned(tx_base.add(30) as *mut u32, 0u32);
        core::ptr::write_unaligned(tx_base.add(34) as *mut u64, OUCH_FIRM_ID.to_be());
        core::ptr::write_unaligned(tx_base.add(42) as *mut u32, 0u32);
        core::ptr::write_unaligned(tx_base.add(46) as *mut u16, 0u16);
    }
}

/// Mutant 1 (`oms_on_tick_buggy_bypasses_kill_switch`):
/// Omits the `KILL_SWITCH != 0` gate on tick-triggered OUCH quoting ->
/// FALSIFIED by `ens_t2t_blocked` + `--slice-frame readonly` and `contract_t2t_kill_switch_blocks_ouch_buggy`!
#[unsafe(no_mangle)]
pub extern "C" fn oms_on_tick_buggy_bypasses_kill_switch(
    rx_ptr: i32,
    rx_len: i32,
    tx_ptr: i32,
    tx_len: i32,
) -> i32 {
    // BUG: missing `|| KILL_SWITCH.load(Ordering::Relaxed) != 0` guard!
    if OMS_INIT.load(Ordering::Relaxed) != 1
        || rx_len < (ADD_ORDER_LEN as i32)
        || tx_len < (OUCH_FRAME_LEN as i32)
    {
        return 0;
    }
    let tx_cap = TX_CAP.load(Ordering::Relaxed);
    let tx_head = TX_HEAD.load(Ordering::Relaxed);
    let tx_tail = TX_TAIL.load(Ordering::Relaxed);
    if tx_cap != RING_CAP || (tx_tail.wrapping_sub(tx_head) as u32) >= (RING_CAP as u32) {
        return 0;
    }

    let rx_base = rx_ptr as usize as *const u8;
    let (msg_type, side, cl_ord_id, tick_shares, symbol, tick_price) = unsafe {
        let mt = core::ptr::read(rx_base);
        let sd = core::ptr::read(rx_base.add(19));
        let oid = u64::from_be(core::ptr::read_unaligned(rx_base.add(11) as *const u64)) as i64;
        let sh = u32::from_be(core::ptr::read_unaligned(rx_base.add(20) as *const u32)) as i32;
        let sym = core::ptr::read_unaligned(rx_base.add(24) as *const u64);
        let px = u32::from_be(core::ptr::read_unaligned(rx_base.add(32) as *const u32)) as i32;
        (mt, sd, oid, sh, sym, px)
    };
    if msg_type != MSG_ADD_ORDER
        || (side != b'B' && side != b'S')
        || cl_ord_id == 0
        || tick_shares <= 0
        || tick_shares > MAX_TICK_QTY
        || tick_price <= 0
        || tick_price > MAX_TICK_PX
    {
        return 0;
    }

    let px_v = load_book4_v128(&BOOK_PX);
    let qty_v = load_book4_v128(&BOOK_QTY);
    let elig = v128_and(
        i32x4_le(px_v, i32x4_splat(tick_price)),
        i32x4_gt(qty_v, i32x4_splat(0)),
    );
    let avail = v128_and(qty_v, elig);
    let sweep_qty = i32x4_extract_lane::<0>(avail)
        .wrapping_add(i32x4_extract_lane::<1>(avail))
        .wrapping_add(i32x4_extract_lane::<2>(avail).wrapping_add(i32x4_extract_lane::<3>(avail)));
    if sweep_qty <= 0 {
        return 0;
    }

    let p_f = f32x4_convert_i32x4(px_v);
    let pw = f32x4_mul(p_f, f32x4(0.4, 0.3, 0.2, 0.1));
    let fair_f32 = (f32x4_extract_lane::<0>(pw) + f32x4_extract_lane::<1>(pw))
        + (f32x4_extract_lane::<2>(pw) + f32x4_extract_lane::<3>(pw));
    let fv = f32x4_splat(fair_f32);
    let hs = HALF_SPREAD.load(Ordering::Relaxed);
    if hs < 1 || hs > MAX_HALF_SPREAD {
        return 0;
    }
    let bid_tick = (f32x4_extract_lane::<0>(f32x4_floor(fv)) as i32).wrapping_sub(hs);
    let ask_tick = (f32x4_extract_lane::<0>(f32x4_ceil(fv)) as i32).wrapping_add(hs);
    if bid_tick <= 0 || bid_tick >= ask_tick {
        return 0;
    }

    let quote_px = if side == b'B' { bid_tick as i64 } else { ask_tick as i64 };
    let quote_qty = if tick_shares <= sweep_qty { tick_shares } else { sweep_qty };

    let max_ord = MAX_ORDER_NOTIONAL.load(Ordering::Relaxed);
    let max_cred = MAX_CREDIT.load(Ordering::Relaxed);
    let open_not = OPEN_NOTIONAL.load(Ordering::Relaxed);
    let ref_px = REF_PRICE.load(Ordering::Relaxed);
    let collar = COLLAR_BPS.load(Ordering::Relaxed);
    if max_ord <= 0 || max_ord > MAX_RISK_NOTIONAL_CAP || max_cred <= 0 || max_cred > MAX_RISK_NOTIONAL_CAP {
        return 0;
    }
    if unsafe { checked_notional(quote_px, quote_qty as i64, max_ord) } == 0
        || unsafe { price_collar_ok(quote_px, ref_px, collar) } == 0
    {
        return 0;
    }
    let notional = quote_px.wrapping_mul(quote_qty as i64);
    let next_not = open_not.wrapping_add(notional);
    let p_target = P_TARGET_QTY.load(Ordering::Relaxed);
    let p_cum = P_CUM_FILLED.load(Ordering::Relaxed);
    let next_p_open = P_OPEN_WORST.load(Ordering::Relaxed).wrapping_add(quote_qty);
    let next_buy = if side == b'B' {
        OPEN_BUY_QTY.load(Ordering::Relaxed).wrapping_add(quote_qty)
    } else {
        OPEN_BUY_QTY.load(Ordering::Relaxed)
    };
    let next_sell = if side == b'S' {
        OPEN_SELL_QTY.load(Ordering::Relaxed).wrapping_add(quote_qty)
    } else {
        OPEN_SELL_QTY.load(Ordering::Relaxed)
    };
    if notional <= 0
        || next_not < 0
        || next_not > max_cred
        || next_p_open < 0
        || next_p_open > p_target.wrapping_sub(p_cum)
        || !fits_pos_limits(NET_POS.load(Ordering::Relaxed), next_buy, next_sell, MAX_POS.load(Ordering::Relaxed))
    {
        return 0;
    }

    TX_SLOTS[(tx_tail & RING_MASK) as usize].store(cl_ord_id, Ordering::Relaxed);
    P_OPEN_WORST.store(next_p_open, Ordering::Relaxed);
    OPEN_NOTIONAL.store(next_not, Ordering::Relaxed);
    OPEN_BUY_QTY.store(next_buy, Ordering::Relaxed);
    OPEN_SELL_QTY.store(next_sell, Ordering::Relaxed);
    LAST_BID_TICK.store(bid_tick, Ordering::Relaxed);
    LAST_ASK_TICK.store(ask_tick, Ordering::Relaxed);
    TX_TAIL.store(tx_tail.wrapping_add(1), Ordering::Relaxed);
    write_ouch_tx(tx_ptr, cl_ord_id as u64, side, quote_qty as u32, symbol, quote_px as u64);
    OUCH_FRAME_LEN as i32
}

/// Mutant 2 (`oms_on_tick_buggy_clobbers_rx`):
/// Accidentally overwrites `rx_ptr[0]` with an in-place consumed marker (`0x00`) ->
/// FALSIFIED by `SliceFrame(base=1048576, len=16384)`!
#[unsafe(no_mangle)]
pub extern "C" fn oms_on_tick_buggy_clobbers_rx(
    rx_ptr: i32,
    rx_len: i32,
    _tx_ptr: i32,
    _tx_len: i32,
) -> i32 {
    if rx_len < (ADD_ORDER_LEN as i32) {
        return 0;
    }
    // BUG: mutates the read-only RX DMA buffer!
    unsafe {
        core::ptr::write(rx_ptr as usize as *mut u8, 0u8);
    }
    0
}

#[inline(never)]
fn store_last_quotes(bid: i32, ask: i32) {
    LAST_BID_TICK.store(bid, Ordering::Relaxed);
    LAST_ASK_TICK.store(ask, Ordering::Relaxed);
}

/// Mutant 3 (`oms_on_tick_buggy_crossed_quote`):
/// Computes inverted/crossed ticks (`bid_tick = ceil(fair) + hs`, `ask_tick = floor(fair) - hs`)
/// without checking `bid_tick < ask_tick` -> FALSIFIED by `inv_t2t_oms()`!
#[unsafe(no_mangle)]
pub extern "C" fn oms_on_tick_buggy_crossed_quote(
    _rx_ptr: i32,
    rx_len: i32,
    _tx_ptr: i32,
    tx_len: i32,
) -> i32 {
    if OMS_INIT.load(Ordering::Relaxed) != 1
        || KILL_SWITCH.load(Ordering::Relaxed) != 0
        || rx_len < (ADD_ORDER_LEN as i32)
        || tx_len < (OUCH_FRAME_LEN as i32)
    {
        return 0;
    }
    let hs = HALF_SPREAD.load(Ordering::Relaxed);
    if hs < 1 || hs > MAX_HALF_SPREAD {
        return 0;
    }
    let px_v = load_book4_v128(&BOOK_PX);
    let p_f = f32x4_convert_i32x4(px_v);
    let pw = f32x4_mul(p_f, f32x4(0.4, 0.3, 0.2, 0.1));
    let fair_f32 = (f32x4_extract_lane::<0>(pw) + f32x4_extract_lane::<1>(pw))
        + (f32x4_extract_lane::<2>(pw) + f32x4_extract_lane::<3>(pw));
    let fv = f32x4_splat(fair_f32);
    // BUG: swapped bid/ask spread direction -> bid_tick > ask_tick (crossed quote!)
    let bid_tick = (f32x4_extract_lane::<0>(f32x4_ceil(fv)) as i32).wrapping_add(hs);
    let ask_tick = (f32x4_extract_lane::<0>(f32x4_floor(fv)) as i32).wrapping_sub(hs);
    store_last_quotes(bid_tick, ask_tick);
    OUCH_FRAME_LEN as i32
}

/// Inline contract exposing Mutant 1 (`oms_on_tick_buggy_bypasses_kill_switch`) -> FALSIFIED!
#[unsafe(no_mangle)]
pub extern "C" fn contract_t2t_kill_switch_blocks_ouch_buggy(
    rx_ptr: i32,
    rx_len: i32,
    tx_ptr: i32,
    tx_len: i32,
) -> i32 {
    assume(req_t2t_slices(rx_ptr, rx_len, tx_ptr, tx_len) == 1);
    assume(inv_t2t_oms() == 1);
    assume(KILL_SWITCH.load(Ordering::Relaxed) != 0);

    let ret = oms_on_tick_buggy_bypasses_kill_switch(rx_ptr, rx_len, tx_ptr, tx_len);
    assert_prop(ret == 0);
    1
}
