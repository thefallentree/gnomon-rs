#![no_std]

use core::arch::wasm32::*;
use core::convert::TryInto;
use core::slice;
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

// ============================================================================
// Memory Layout (min_pages >= 17, Disjoint .bss / TX DMA / RX DMA Arenas)
// ============================================================================

/// Guard static in `.bss` above 1 MiB shadow stack (`0x10_0000`), ensuring `min_pages >= 17`.
static WIRE_DMA_GUARD: [u8; 64] = [0; 64];

const STACK_TOP: i32 = 1_048_576; // 16 * 65536 (rustc default __stack_pointer init)
const TX_LO: i32 = STACK_TOP + 4_096; // 1_052_672 (strictly above .bss OMS state)
const TX_HI: i32 = STACK_TOP + 16_384; // 1_064_960 (12 KiB TX DMA arena)
const RX_LO: i32 = STACK_TOP + 16_384; // 1_064_960 (16 KiB RX DMA arena, disjoint from TX + .bss)
const RX_HI: i32 = STACK_TOP + 32_768; // 1_081_344 (strictly inside 17 pages = 1_114_112)
const MIN_LIVE_PAGES: usize = 17;

// ITCH 5.0 AddOrder RX tick layout (36 bytes, matching S2.3)
const MSG_ADD_ORDER: u8 = b'A';
const ADD_ORDER_LEN: usize = 36;

// OUCH 5.0 EnterOrder TX frame layout (48 bytes, matching S2.4)
const OUCH_ENTER_ORDER_TAG: u8 = b'O';
const OUCH_FRAME_LEN: usize = 48;
/// Fixed 8-byte ASCII firm identifier (`"GNOMON01"`), encoded big-endian at `[34..42]`.
const OUCH_FIRM_ID: u64 = 0x474E_4F4D_4F4E_3031;

// Realistic equities tick, lot, risk-cap & ring bounds
const MAX_TICK_PX: i32 = 1_000_000;
const MAX_TICK_QTY: i32 = 10_000;
const MAX_HALF_SPREAD: i32 = 10_000;
const MAX_RISK_NOTIONAL_CAP: i64 = 1_000_000_000;
const RING_CAP: i32 = 8;
const RING_MASK: i32 = 7;

// ============================================================================
// Layer-4 Tick-to-Trade OMS State (16-byte aligned L2 book + Risk + TX Ring)
// ============================================================================

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

// 4-level L2 book (S3.4)
static BOOK_PX: Book4 = zero_book4();
static BOOK_QTY: Book4 = zero_book4();
static HALF_SPREAD: AtomicI32 = AtomicI32::new(1);

// OMS & Risk state (S3.2 / S3.3)
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

// Most recent emitted quote ticks (always non-crossed: `LAST_BID_TICK < LAST_ASK_TICK`)
static LAST_BID_TICK: AtomicI32 = AtomicI32::new(0);
static LAST_ASK_TICK: AtomicI32 = AtomicI32::new(1);

// Outbound order staging registers in `.bss` (written only upon risk admission)
static OUT_CL_ORD_ID: AtomicI64 = AtomicI64::new(0);
static OUT_SIDE: AtomicI32 = AtomicI32::new(0);
static OUT_QTY: AtomicI32 = AtomicI32::new(0);
static OUT_SYMBOL: AtomicI64 = AtomicI64::new(0);
static OUT_PX: AtomicI64 = AtomicI64::new(0);

// 8-slot TX SPSC Journal/Audit Ring (S2.1)
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

// ============================================================================
// Pure Helpers & Scalar vs v128 Book Sweep + Fair-Value Kernels
// ============================================================================

#[inline(always)]
fn load_book4_v128(book: &Book4) -> v128 {
    // SAFETY: `Book4` is 16-byte aligned with 4 contiguous `AtomicI32` values (16 bytes).
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

/// Scalar 4-level L2 book sweep + weighted fair-value estimator (`0.4/0.3/0.2/0.1` depth
/// weights in exact `((w0 + w1) + (w2 + w3))` reduction tree).
/// Returns packed `i64`: low 32 bits = `sweep_qty`, high 32 bits = `fair_f32.to_bits()`.
#[unsafe(no_mangle)]
pub extern "C" fn sweep_fair_scalar(
    p0: i32,
    p1: i32,
    p2: i32,
    p3: i32,
    q0: i32,
    q1: i32,
    q2: i32,
    q3: i32,
    tick_price: i32,
) -> i64 {
    let a0 = if p0 <= tick_price && q0 > 0 { q0 } else { 0 };
    let a1 = if p1 <= tick_price && q1 > 0 { q1 } else { 0 };
    let a2 = if p2 <= tick_price && q2 > 0 { q2 } else { 0 };
    let a3 = if p3 <= tick_price && q3 > 0 { q3 } else { 0 };

    let sweep_qty = a0.wrapping_add(a1).wrapping_add(a2.wrapping_add(a3));
    if sweep_qty <= 0 {
        return 0;
    }

    let w0 = (p0 as f32) * 0.4f32;
    let w1 = (p1 as f32) * 0.3f32;
    let w2 = (p2 as f32) * 0.2f32;
    let w3 = (p3 as f32) * 0.1f32;
    let fair_f32 = (w0 + w1) + (w2 + w3);
    (((fair_f32.to_bits() as u64) << 32) | ((sweep_qty as u32) as u64)) as i64
}

/// Vectorized `v128` (`i32x4` + `f32x4`) 4-level L2 book sweep + weighted fair-value estimator.
/// Bit-identical to `sweep_fair_scalar` across all IEEE-754 inputs (`QF_ABVFP`).
#[unsafe(no_mangle)]
pub extern "C" fn sweep_fair_v128(
    p0: i32,
    p1: i32,
    p2: i32,
    p3: i32,
    q0: i32,
    q1: i32,
    q2: i32,
    q3: i32,
    tick_price: i32,
) -> i64 {
    let px_v = i32x4(p0, p1, p2, p3);
    let qty_v = i32x4(q0, q1, q2, q3);
    let elig = v128_and(
        i32x4_le(px_v, i32x4_splat(tick_price)),
        i32x4_gt(qty_v, i32x4_splat(0)),
    );
    let avail = v128_and(qty_v, elig);

    let a0 = i32x4_extract_lane::<0>(avail);
    let a1 = i32x4_extract_lane::<1>(avail);
    let a2 = i32x4_extract_lane::<2>(avail);
    let a3 = i32x4_extract_lane::<3>(avail);
    let sweep_qty = a0.wrapping_add(a1).wrapping_add(a2.wrapping_add(a3));
    if sweep_qty <= 0 {
        return 0;
    }

    let p_f = f32x4_convert_i32x4(px_v);
    let w_v = f32x4(0.4, 0.3, 0.2, 0.1);
    let pw = f32x4_mul(p_f, w_v);

    let even = f32x4(
        f32x4_extract_lane::<0>(pw),
        f32x4_extract_lane::<2>(pw),
        0.0,
        0.0,
    );
    let odd = f32x4(
        f32x4_extract_lane::<1>(pw),
        f32x4_extract_lane::<3>(pw),
        0.0,
        0.0,
    );
    let pair = f32x4_add(even, odd);
    let fair_f32 = f32x4_extract_lane::<0>(pair) + f32x4_extract_lane::<1>(pair);
    (((fair_f32.to_bits() as u64) << 32) | ((sweep_qty as u32) as u64)) as i64
}

/// Shadow-stack OUCH 5.0 48-byte `EnterOrder` frame builder for `oms_on_tick_ref` (`Global(0)`).
#[inline(never)]
fn build_ouch_frame_on_stack(
    frame: &mut [u8; OUCH_FRAME_LEN],
    cl_ord_id: u64,
    side: u8,
    shares: u32,
    symbol: u64,
    price: u64,
) {
    let base = frame.as_mut_ptr();
    unsafe {
        core::ptr::write(base, OUCH_ENTER_ORDER_TAG);
        core::ptr::write_unaligned(base.add(1) as *mut u64, cl_ord_id.to_be());
        core::ptr::write(base.add(9), side);
        core::ptr::write_unaligned(base.add(10) as *mut u32, shares.to_be());
        core::ptr::write_unaligned(base.add(14) as *mut u64, symbol);
        core::ptr::write_unaligned(base.add(22) as *mut u64, price.to_be());
        core::ptr::write_unaligned(base.add(30) as *mut u32, 0u32);
        core::ptr::write_unaligned(base.add(34) as *mut u64, OUCH_FIRM_ID.to_be());
        core::ptr::write_unaligned(base.add(42) as *mut u32, 0u32);
        core::ptr::write_unaligned(base.add(46) as *mut u16, 0u16);
    }
}

/// Shadow-stack commit helper for `oms_on_tick_ref`: copies staged 48-byte OUCH frame into `dst`.
#[inline(never)]
fn commit_ouch_frame(src: &[u8; OUCH_FRAME_LEN], dst: &mut [u8; OUCH_FRAME_LEN]) {
    let s = src.as_ptr();
    let d = dst.as_mut_ptr();
    unsafe {
        core::ptr::write(d, core::ptr::read(s));
        core::ptr::write_unaligned(
            d.add(1) as *mut u64,
            core::ptr::read_unaligned(s.add(1) as *const u64),
        );
        core::ptr::write(d.add(9), core::ptr::read(s.add(9)));
        core::ptr::write_unaligned(
            d.add(10) as *mut u32,
            core::ptr::read_unaligned(s.add(10) as *const u32),
        );
        core::ptr::write_unaligned(
            d.add(14) as *mut u64,
            core::ptr::read_unaligned(s.add(14) as *const u64),
        );
        core::ptr::write_unaligned(
            d.add(22) as *mut u64,
            core::ptr::read_unaligned(s.add(22) as *const u64),
        );
        core::ptr::write_unaligned(
            d.add(30) as *mut u32,
            core::ptr::read_unaligned(s.add(30) as *const u32),
        );
        core::ptr::write_unaligned(
            d.add(34) as *mut u64,
            core::ptr::read_unaligned(s.add(34) as *const u64),
        );
        core::ptr::write_unaligned(
            d.add(42) as *mut u32,
            core::ptr::read_unaligned(s.add(42) as *const u32),
        );
        core::ptr::write_unaligned(
            d.add(46) as *mut u16,
            core::ptr::read_unaligned(s.add(46) as *const u16),
        );
    }
}

// ============================================================================
// Initializer, Kill-Switch, Preconditions & Unified Tick-to-Trade Invariant
// ============================================================================

/// Initialize a valid Tick-to-Trade OMS state with a 4-level L2 book, SEC 15c3-5
/// risk caps, parent headroom, and empty TX SPSC ring (establishes `inv_t2t_oms() == 1`).
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

    let mut i = 0usize;
    while i < 8 {
        TX_SLOTS[i].store(0, Ordering::Relaxed);
        i += 1;
    }
}

/// Trip the SEC 15c3-5 emergency kill switch (blocks all subsequent outbound OUCH frames).
#[unsafe(no_mangle)]
pub extern "C" fn trip_t2t_kill_switch() -> i32 {
    if OMS_INIT.load(Ordering::Relaxed) != 1 {
        return 0;
    }
    KILL_SWITCH.store(1, Ordering::Relaxed);
    1
}

/// Precondition for `oms_on_tick_ref` and `oms_on_tick_opt`:
/// - Linear memory has at least 17 pages (`>= 1_114_112` bytes).
/// - TX slice `[tx_ptr, tx_ptr + tx_len)` lies inside the TX DMA arena `[TX_LO, TX_HI)`.
/// - RX slice `[rx_ptr, rx_ptr + rx_len)` lies inside the disjoint RX DMA arena `[RX_LO, RX_HI)`.
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

/// Precondition asserting `req_t2t_slices` + `inv_t2t_oms` + tripped kill switch (`KILL_SWITCH != 0`),
/// for standalone `check-contract` kill-switch + `--slice-frame readonly` proof.
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

/// Postcondition proving kill-switch blocks outbound OUCH frame (`ret == 0`).
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

/// Branchless Unified Layer-4 Tick-to-Trade OMS State Invariant (`inv_t2t_oms() -> i32`):
/// 1. 4-level L2 book bounds (`v128`): `0 < px[i] <= 1_000_000`, `0 <= qty[i] <= 10_000`,
///    `1 <= half_spread <= 10_000`.
/// 2. Parent Zero-Overfill: `p_target > 0`, `p_cum >= 0`, `p_open >= 0`, `p_cum + p_open <= p_target`.
/// 3. SEC 15c3-5 Risk bounds: `0 < max_ord <= 1e9`, `0 < max_cred <= 1e9`,
///    `0 <= open_notional <= max_credit`, `0 < ref_px <= 1e6`, `0 <= collar_bps <= 10_000`,
///    worst-case long/short position within `[-max_pos, max_pos]`.
/// 4. Non-crossed emitted quote invariant: `LAST_BID_TICK < LAST_ASK_TICK`.
/// 5. TX SPSC Ring bounds: `tx_cap == 8 && tx_tail.wrapping_sub(tx_head) as u32 <= 8`.
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

// ============================================================================
// Core Tick-to-Trade Evaluation & Risk Reservation (`v128` + `f32x4` + S1.1)
// ============================================================================

/// Zero-stack core evaluation & risk reservation:
/// 1. ITCH 5.0 36B market tick decode.
/// 2. `v128` (`i32x4`) 4-level L2 book sweep + `f32x4` weighted fair value +
///    `f32x4_floor`/`f32x4_ceil` non-crossed quote ticks (`bid_tick < ask_tick`).
/// 3. Parent headroom + Layer-1 `S1.1` `checked_notional` & `price_collar_ok` +
///    kill switch + SEC 15c3-5 credit & position checks.
/// 4. TX SPSC ring push + OMS state & outbound staging register commit.
/// Returns `1` if admitted (caller must emit 48-byte OUCH frame), `0` if rejected (zero writes).
#[inline(never)]
fn t2t_eval_and_reserve(rx_ptr: i32, rx_len: i32, tx_len: i32) -> i32 {
    if OMS_INIT.load(Ordering::Relaxed) != 1
        || KILL_SWITCH.load(Ordering::Relaxed) != 0
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
    // SAFETY: Caller satisfies `req_t2t_slices` and `rx_len >= 36`.
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

    // Vectorized `v128` (`i32x4`) 4-level L2 book sweep (S3.4)
    let px_v = load_book4_v128(&BOOK_PX);
    let qty_v = load_book4_v128(&BOOK_QTY);
    let elig = v128_and(
        i32x4_le(px_v, i32x4_splat(tick_price)),
        i32x4_gt(qty_v, i32x4_splat(0)),
    );
    let avail = v128_and(qty_v, elig);

    let a0 = i32x4_extract_lane::<0>(avail);
    let a1 = i32x4_extract_lane::<1>(avail);
    let a2 = i32x4_extract_lane::<2>(avail);
    let a3 = i32x4_extract_lane::<3>(avail);
    let sweep_qty = a0.wrapping_add(a1).wrapping_add(a2.wrapping_add(a3));
    if sweep_qty <= 0 {
        return 0;
    }

    // Vectorized `f32x4` 4-level weighted fair value & non-crossed tick rounding (S3.5)
    let p_f = f32x4_convert_i32x4(px_v);
    let w_v = f32x4(0.4, 0.3, 0.2, 0.1);
    let pw = f32x4_mul(p_f, w_v);

    let even = f32x4(
        f32x4_extract_lane::<0>(pw),
        f32x4_extract_lane::<2>(pw),
        0.0,
        0.0,
    );
    let odd = f32x4(
        f32x4_extract_lane::<1>(pw),
        f32x4_extract_lane::<3>(pw),
        0.0,
        0.0,
    );
    let pair = f32x4_add(even, odd);
    let fair_f32 = f32x4_extract_lane::<0>(pair) + f32x4_extract_lane::<1>(pair);

    let fv = f32x4_splat(fair_f32);
    let fl_i = f32x4_extract_lane::<0>(f32x4_floor(fv)) as i32;
    let cl_i = f32x4_extract_lane::<0>(f32x4_ceil(fv)) as i32;
    let hs = HALF_SPREAD.load(Ordering::Relaxed);
    if hs < 1 || hs > MAX_HALF_SPREAD {
        return 0;
    }
    let bid_tick = fl_i.wrapping_sub(hs);
    let ask_tick = cl_i.wrapping_add(hs);
    if bid_tick <= 0 || bid_tick >= ask_tick || ask_tick > (MAX_TICK_PX + MAX_HALF_SPREAD + 1) {
        return 0;
    }

    let quote_px = if side == b'B' { bid_tick as i64 } else { ask_tick as i64 };
    let quote_qty = if tick_shares <= sweep_qty { tick_shares } else { sweep_qty };

    // Parent headroom + Layer-1 S1.1 Strata + SEC 15c3-5 Pre-Trade Risk Gate
    let p_target = P_TARGET_QTY.load(Ordering::Relaxed);
    let p_cum = P_CUM_FILLED.load(Ordering::Relaxed);
    let p_open = P_OPEN_WORST.load(Ordering::Relaxed);
    let next_p_open = p_open.wrapping_add(quote_qty);

    let max_ord = MAX_ORDER_NOTIONAL.load(Ordering::Relaxed);
    let max_cred = MAX_CREDIT.load(Ordering::Relaxed);
    let open_not = OPEN_NOTIONAL.load(Ordering::Relaxed);
    let ref_px = REF_PRICE.load(Ordering::Relaxed);
    let collar = COLLAR_BPS.load(Ordering::Relaxed);

    let max_pos = MAX_POS.load(Ordering::Relaxed);
    let net_pos = NET_POS.load(Ordering::Relaxed);
    let open_buy = OPEN_BUY_QTY.load(Ordering::Relaxed);
    let open_sell = OPEN_SELL_QTY.load(Ordering::Relaxed);

    if max_ord <= 0
        || max_ord > MAX_RISK_NOTIONAL_CAP
        || max_cred <= 0
        || max_cred > MAX_RISK_NOTIONAL_CAP
    {
        return 0;
    }

    let cn_ok = unsafe { checked_notional(quote_px, quote_qty as i64, max_ord) } != 0;
    let col_ok = unsafe { price_collar_ok(quote_px, ref_px, collar) } != 0;
    let notional = quote_px.wrapping_mul(quote_qty as i64);
    let next_not = open_not.wrapping_add(notional);

    let next_buy = if side == b'B' {
        open_buy.wrapping_add(quote_qty)
    } else {
        open_buy
    };
    let next_sell = if side == b'S' {
        open_sell.wrapping_add(quote_qty)
    } else {
        open_sell
    };

    if !cn_ok
        || !col_ok
        || p_target <= 0
        || p_cum < 0
        || p_open < 0
        || next_p_open < 0
        || p_cum > p_target
        || next_p_open > p_target.wrapping_sub(p_cum)
        || notional <= 0
        || notional > max_ord
        || open_not < 0
        || next_not < 0
        || next_not > max_cred
        || !fits_pos_limits(net_pos, next_buy, next_sell, max_pos)
    {
        return 0;
    }

    // Push TX ring slot FIRST so scalar OMS stores sit cleanly on top of memory chain.
    TX_SLOTS[(tx_tail & RING_MASK) as usize].store(cl_ord_id, Ordering::Relaxed);
    OUT_CL_ORD_ID.store(cl_ord_id, Ordering::Relaxed);
    OUT_SIDE.store(side as i32, Ordering::Relaxed);
    OUT_QTY.store(quote_qty, Ordering::Relaxed);
    OUT_SYMBOL.store(symbol as i64, Ordering::Relaxed);
    OUT_PX.store(quote_px, Ordering::Relaxed);

    P_OPEN_WORST.store(next_p_open, Ordering::Relaxed);
    OPEN_NOTIONAL.store(next_not, Ordering::Relaxed);
    OPEN_BUY_QTY.store(next_buy, Ordering::Relaxed);
    OPEN_SELL_QTY.store(next_sell, Ordering::Relaxed);
    LAST_BID_TICK.store(bid_tick, Ordering::Relaxed);
    LAST_ASK_TICK.store(ask_tick, Ordering::Relaxed);
    TX_TAIL.store(tx_tail.wrapping_add(1), Ordering::Relaxed);
    1
}

// ============================================================================
// S4.2 Reference vs Zero-Copy Optimized Tick-to-Trade + OUCH Wire Out Pipelines
// ============================================================================

/// Reference E2E Tick-to-Trade + OUCH Wire Out Pipeline (`oms_on_tick_ref`):
/// Composes ITCH decode + `v128`/`f32x4` book sweep & fair value + Layer-1 `S1.1`
/// pre-trade risk gate + shadow-stack staged 48-byte OUCH `EnterOrder` frame build
/// (`Global(0)`) & commit into `tx_ptr[0..48]` + TX SPSC ring push.
#[unsafe(no_mangle)]
pub extern "C" fn oms_on_tick_ref(
    rx_ptr: i32,
    rx_len: i32,
    tx_ptr: i32,
    tx_len: i32,
) -> i32 {
    if t2t_eval_and_reserve(rx_ptr, rx_len, tx_len) == 0 {
        return 0;
    }
    let cl_ord_id = OUT_CL_ORD_ID.load(Ordering::Relaxed) as u64;
    let side = OUT_SIDE.load(Ordering::Relaxed) as u8;
    let quote_qty = OUT_QTY.load(Ordering::Relaxed) as u32;
    let symbol = OUT_SYMBOL.load(Ordering::Relaxed) as u64;
    let quote_px = OUT_PX.load(Ordering::Relaxed) as u64;

    // SAFETY: `t2t_eval_and_reserve` verified `tx_len >= 48` and caller satisfies `req_t2t_slices`.
    let tx = unsafe { slice::from_raw_parts_mut(tx_ptr as *mut u8, tx_len as usize) };
    let Some(dst_slice) = tx.get_mut(..OUCH_FRAME_LEN) else {
        return 0;
    };
    let Ok(dst_fixed): Result<&mut [u8; OUCH_FRAME_LEN], _> = dst_slice.try_into() else {
        return 0;
    };
    let mut frame = [0u8; OUCH_FRAME_LEN];
    build_ouch_frame_on_stack(&mut frame, cl_ord_id, side, quote_qty, symbol, quote_px);
    commit_ouch_frame(&frame, dst_fixed);
    OUCH_FRAME_LEN as i32
}

/// Zero-Copy Optimized E2E Tick-to-Trade + OUCH Wire Out Pipeline (`oms_on_tick_opt`):
/// Zero `__stack_pointer` accesses: directly writes the 48-byte Big-Endian OUCH 5.0
/// `EnterOrder` frame into `tx_ptr[0..48]` via unaligned wide stores after risk admission.
#[unsafe(no_mangle)]
pub extern "C" fn oms_on_tick_opt(
    rx_ptr: i32,
    rx_len: i32,
    tx_ptr: i32,
    tx_len: i32,
) -> i32 {
    if t2t_eval_and_reserve(rx_ptr, rx_len, tx_len) == 0 {
        return 0;
    }
    let cl_ord_id = OUT_CL_ORD_ID.load(Ordering::Relaxed) as u64;
    let side = OUT_SIDE.load(Ordering::Relaxed) as u8;
    let quote_qty = OUT_QTY.load(Ordering::Relaxed) as u32;
    let symbol = OUT_SYMBOL.load(Ordering::Relaxed) as u64;
    let quote_px = OUT_PX.load(Ordering::Relaxed) as u64;

    let tx_base = tx_ptr as usize as *mut u8;
    // SAFETY: `t2t_eval_and_reserve` verified `tx_len >= 48` and caller satisfies `req_t2t_slices`.
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
    OUCH_FRAME_LEN as i32
}

// ============================================================================
// Inline Relational E2E Contracts
// ============================================================================

/// Inline contract proving: whenever `KILL_SWITCH != 0`, `oms_on_tick_opt` MUST return `0`
/// and leave `TX_TAIL`, `OPEN_NOTIONAL`, `P_OPEN_WORST`, and `inv_t2t_oms()` untouched.
#[unsafe(no_mangle)]
pub extern "C" fn contract_t2t_kill_switch_blocks_ouch(
    rx_ptr: i32,
    rx_len: i32,
    tx_ptr: i32,
    tx_len: i32,
) -> i32 {
    assume(req_t2t_slices(rx_ptr, rx_len, tx_ptr, tx_len) == 1);
    assume(inv_t2t_oms() == 1);
    assume(KILL_SWITCH.load(Ordering::Relaxed) != 0);

    let old_tail = TX_TAIL.load(Ordering::Relaxed);
    let old_not = OPEN_NOTIONAL.load(Ordering::Relaxed);
    let old_open = P_OPEN_WORST.load(Ordering::Relaxed);

    let ret = oms_on_tick_opt(rx_ptr, rx_len, tx_ptr, tx_len);

    assert_prop(ret == 0);
    assert_prop(TX_TAIL.load(Ordering::Relaxed) == old_tail);
    assert_prop(OPEN_NOTIONAL.load(Ordering::Relaxed) == old_not);
    assert_prop(P_OPEN_WORST.load(Ordering::Relaxed) == old_open);
    assert_prop(inv_t2t_oms() == 1);
    1
}

/// Inline contract proving `oms_on_tick_opt` preserves `inv_t2t_oms()` AND guarantees
/// non-crossed quote ticks (`LAST_BID_TICK < LAST_ASK_TICK`) on every admitted tick.
#[unsafe(no_mangle)]
pub extern "C" fn contract_t2t_preserves_oms_and_non_crossed(
    rx_ptr: i32,
    rx_len: i32,
    tx_ptr: i32,
    tx_len: i32,
) -> i32 {
    assume(req_t2t_slices(rx_ptr, rx_len, tx_ptr, tx_len) == 1);
    assume(inv_t2t_oms() == 1);

    let ret = oms_on_tick_opt(rx_ptr, rx_len, tx_ptr, tx_len);

    assert_prop(ret == 0 || ret == (OUCH_FRAME_LEN as i32));
    assert_prop(LAST_BID_TICK.load(Ordering::Relaxed) < LAST_ASK_TICK.load(Ordering::Relaxed));
    assert_prop(inv_t2t_oms() == 1);
    1
}
