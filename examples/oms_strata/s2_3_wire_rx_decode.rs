#![no_std]

use core::convert::TryInto;
use core::slice;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

/// 64-byte static guard placed in `.bss` right above the 1 MiB shadow stack
/// (`0x10_0000`), forcing `wasm-ld` to reserve `min_pages >= 17` (`1_114_112`
/// bytes) without emitting an extra exported global.
static WIRE_DMA_GUARD: [u8; 64] = [0; 64];

const STACK_TOP: i32 = 1_048_576; // 16 * 65536 (rustc default __stack_pointer init)
const LIVE_LO: i32 = STACK_TOP + 64; // 1_048_640 (strictly above SP_in + 64B guard)
const LIVE_HI: i32 = STACK_TOP + 32_768; // 1_081_344 (well inside 17 pages = 1_114_112)
const MIN_LIVE_PAGES: usize = 17;

// Nasdaq ITCH 5.0 wire constants
const MSG_ADD_ORDER: u8 = b'A';
const MSG_ORDER_EXECUTED: u8 = b'E';
const ADD_ORDER_LEN: usize = 36;
const ORDER_EXECUTED_LEN: usize = 31;
const OUT_RECORD_LEN: usize = 32;

// Normalized decoded output enums
const KIND_ADD_ORDER: i32 = 1;
const KIND_ORDER_EXECUTED: i32 = 2;
const SIDE_NONE: i32 = 0;
const SIDE_BUY: i32 = 1;
const SIDE_SELL: i32 = 2;

#[inline(always)]
fn decode_side(b: u8) -> i32 {
    match b {
        b'B' => SIDE_BUY,
        b'S' => SIDE_SELL,
        _ => SIDE_NONE,
    }
}

#[inline(always)]
fn read_be_u32_slice(buf: &[u8], off: usize) -> u32 {
    u32::from_be_bytes([buf[off], buf[off + 1], buf[off + 2], buf[off + 3]])
}

#[inline(always)]
fn read_be_u64_slice(buf: &[u8], off: usize) -> u64 {
    u64::from_be_bytes([
        buf[off],
        buf[off + 1],
        buf[off + 2],
        buf[off + 3],
        buf[off + 4],
        buf[off + 5],
        buf[off + 6],
        buf[off + 7],
    ])
}

/// Shadow-stack staging helper: materializes the 32-byte normalized decoded
/// ITCH record into a caller-allocated `[u8; 32]` buffer on `__stack_pointer`.
#[inline(never)]
fn stage_record_on_stack(
    out_buf: &mut [u8; OUT_RECORD_LEN],
    msg_kind: i32,
    side: i32,
    order_ref: i64,
    shares: i64,
    price_or_match: i64,
) {
    out_buf[0..4].copy_from_slice(&msg_kind.to_le_bytes());
    out_buf[4..8].copy_from_slice(&side.to_le_bytes());
    out_buf[8..16].copy_from_slice(&order_ref.to_le_bytes());
    out_buf[16..24].copy_from_slice(&shares.to_le_bytes());
    out_buf[24..32].copy_from_slice(&price_or_match.to_le_bytes());
}

/// Shadow-stack commit helper: copies staged 32-byte record from the shadow
/// stack into the caller's live destination slice `out_ptr[0..32]`.
#[inline(never)]
fn commit_record(src: &[u8; OUT_RECORD_LEN], dst: &mut [u8; OUT_RECORD_LEN]) {
    let mut i = 0usize;
    while i < OUT_RECORD_LEN {
        dst[i] = src[i];
        i += 1;
    }
}

/// Precondition for `itch_decode_ref` and `itch_decode_opt`:
/// - Linear memory has at least 17 pages (`>= 1_114_112` bytes).
/// - Both `[rx_ptr, rx_ptr + rx_len)` and `[out_ptr, out_ptr + out_len)` lie
///   within the live window `[1_048_576 + 64, 1_048_576 + 32_768)` with
///   non-negative lengths and no 32-bit wraparound.
/// - `rx` and `out` slices are disjoint.
#[unsafe(no_mangle)]
pub extern "C" fn req_itch_decode(
    rx_ptr: i32,
    rx_len: i32,
    out_ptr: i32,
    out_len: i32,
) -> i32 {
    if core::arch::wasm32::memory_size(0) < MIN_LIVE_PAGES {
        return 0;
    }
    // Keep WIRE_DMA_GUARD live in `.bss` so `min_pages >= 17`.
    let guard_lo = (WIRE_DMA_GUARD.as_ptr() as i32).wrapping_add(64);
    let live_lo = if guard_lo > LIVE_LO { guard_lo } else { LIVE_LO };
    if rx_ptr < live_lo || rx_ptr > LIVE_HI {
        return 0;
    }
    if rx_len < 0 || rx_len > LIVE_HI - rx_ptr {
        return 0;
    }
    if out_ptr < live_lo || out_ptr > LIVE_HI {
        return 0;
    }
    if out_len < 0 || out_len > LIVE_HI - out_ptr {
        return 0;
    }
    let rx_end = rx_ptr + rx_len;
    let out_end = out_ptr + out_len;
    if rx_end <= out_ptr || out_end <= rx_ptr {
        1
    } else {
        0
    }
}

/// Precondition for read-only `itch_validate_header(rx_ptr, rx_len)`.
#[unsafe(no_mangle)]
pub extern "C" fn req_itch_validate(rx_ptr: i32, rx_len: i32) -> i32 {
    if core::arch::wasm32::memory_size(0) < MIN_LIVE_PAGES {
        return 0;
    }
    let guard_lo = (WIRE_DMA_GUARD.as_ptr() as i32).wrapping_add(64);
    let live_lo = if guard_lo > LIVE_LO { guard_lo } else { LIVE_LO };
    if rx_ptr < live_lo || rx_ptr > LIVE_HI {
        return 0;
    }
    if rx_len < 0 || rx_len > LIVE_HI - rx_ptr {
        return 0;
    }
    1
}

/// S2.3 Reference ITCH 5.0 Wire RX Decoder (shadow-stack buffered):
/// Uses safe Rust slices + explicit shadow-stack `[u8; 32]` staging buffer
/// (`Global(0)` `__stack_pointer`).
/// Decodes `AddOrder` (`'A'`, 36B) and `OrderExecuted` (`'E'`, 31B) into a
/// normalized 32-byte record at `out_ptr[0..32]`:
///   `[0..4]   msg_kind: i32` (`1` = AddOrder, `2` = OrderExecuted)
///   `[4..8]   side: i32` (`1` = Buy `'B'`, `2` = Sell `'S'`, `0` = N/A)
///   `[8..16]  order_ref: i64`
///   `[16..24] shares: i64`
///   `[24..32] price_or_match: i64`
/// Returns `1` on valid packet, `0` on truncated/unknown/invalid packet
/// (without modifying `out_ptr` on rejection, and never panicking).
#[unsafe(no_mangle)]
pub extern "C" fn itch_decode_ref(
    rx_ptr: i32,
    rx_len: i32,
    out_ptr: i32,
    out_len: i32,
) -> i32 {
    if rx_len < 1 || out_len < (OUT_RECORD_LEN as i32) {
        return 0;
    }
    // SAFETY: Caller satisfies `req_itch_decode` (valid, non-overlapping, in-bounds slices).
    let rx = unsafe { slice::from_raw_parts(rx_ptr as *const u8, rx_len as usize) };
    let out = unsafe { slice::from_raw_parts_mut(out_ptr as *mut u8, out_len as usize) };

    let Some(out_arr) = out.get_mut(..OUT_RECORD_LEN) else {
        return 0;
    };
    let Ok(out_fixed): Result<&mut [u8; OUT_RECORD_LEN], _> = out_arr.try_into() else {
        return 0;
    };

    let (msg_kind, side, order_ref, shares, price_or_match) = match rx[0] {
        MSG_ADD_ORDER => {
            let Some(pkt) = rx.get(..ADD_ORDER_LEN) else {
                return 0;
            };
            let side = decode_side(pkt[19]);
            if side == SIDE_NONE {
                return 0;
            }
            let order_ref = read_be_u64_slice(pkt, 11) as i64;
            let shares = (read_be_u32_slice(pkt, 20) as u64) as i64;
            let price = (read_be_u32_slice(pkt, 32) as u64) as i64;
            (KIND_ADD_ORDER, side, order_ref, shares, price)
        }
        MSG_ORDER_EXECUTED => {
            let Some(pkt) = rx.get(..ORDER_EXECUTED_LEN) else {
                return 0;
            };
            let order_ref = read_be_u64_slice(pkt, 11) as i64;
            let exec_shares = (read_be_u32_slice(pkt, 19) as u64) as i64;
            let match_num = read_be_u64_slice(pkt, 23) as i64;
            (
                KIND_ORDER_EXECUTED,
                SIDE_NONE,
                order_ref,
                exec_shares,
                match_num,
            )
        }
        _ => return 0,
    };

    let mut out_scratch = [0u8; OUT_RECORD_LEN];
    stage_record_on_stack(
        &mut out_scratch,
        msg_kind,
        side,
        order_ref,
        shares,
        price_or_match,
    );
    commit_record(&out_scratch, out_fixed);
    1
}

/// S2.3 Zero-Copy Optimized ITCH 5.0 Wire RX Decoder:
/// Zero shadow-stack frame (no `Global(0)` accesses), fused bounds checks,
/// direct unaligned big-endian wide loads (`u64::from_be` / `u32::from_be`),
/// and direct 32-byte normalized record stores into `out_ptr[0..32]`.
#[unsafe(no_mangle)]
pub extern "C" fn itch_decode_opt(
    rx_ptr: i32,
    rx_len: i32,
    out_ptr: i32,
    out_len: i32,
) -> i32 {
    if rx_len < 1 || out_len < (OUT_RECORD_LEN as i32) {
        return 0;
    }
    let rx_base = rx_ptr as usize as *const u8;
    let out_base = out_ptr as usize as *mut u8;

    // SAFETY: Caller satisfies `req_itch_decode`; every offset below is guarded by
    // the explicit packet-length and output-length checks above.
    unsafe {
        let msg_type = core::ptr::read(rx_base);
        if msg_type == MSG_ADD_ORDER {
            if rx_len < (ADD_ORDER_LEN as i32) {
                return 0;
            }
            let side = decode_side(core::ptr::read(rx_base.add(19)));
            if side == SIDE_NONE {
                return 0;
            }
            let order_ref =
                u64::from_be(core::ptr::read_unaligned(rx_base.add(11) as *const u64)) as i64;
            let shares =
                (u32::from_be(core::ptr::read_unaligned(rx_base.add(20) as *const u32)) as u64)
                    as i64;
            let price =
                (u32::from_be(core::ptr::read_unaligned(rx_base.add(32) as *const u32)) as u64)
                    as i64;

            core::ptr::write_unaligned(out_base as *mut i32, KIND_ADD_ORDER);
            core::ptr::write_unaligned(out_base.add(4) as *mut i32, side);
            core::ptr::write_unaligned(out_base.add(8) as *mut i64, order_ref);
            core::ptr::write_unaligned(out_base.add(16) as *mut i64, shares);
            core::ptr::write_unaligned(out_base.add(24) as *mut i64, price);
            1
        } else if msg_type == MSG_ORDER_EXECUTED {
            if rx_len < (ORDER_EXECUTED_LEN as i32) {
                return 0;
            }
            let order_ref =
                u64::from_be(core::ptr::read_unaligned(rx_base.add(11) as *const u64)) as i64;
            let exec_shares =
                (u32::from_be(core::ptr::read_unaligned(rx_base.add(19) as *const u32)) as u64)
                    as i64;
            let match_num =
                u64::from_be(core::ptr::read_unaligned(rx_base.add(23) as *const u64)) as i64;

            core::ptr::write_unaligned(out_base as *mut i32, KIND_ORDER_EXECUTED);
            core::ptr::write_unaligned(out_base.add(4) as *mut i32, SIDE_NONE);
            core::ptr::write_unaligned(out_base.add(8) as *mut i64, order_ref);
            core::ptr::write_unaligned(out_base.add(16) as *mut i64, exec_shares);
            core::ptr::write_unaligned(out_base.add(24) as *mut i64, match_num);
            1
        } else {
            0
        }
    }
}

/// Pure read-only ITCH 5.0 header & length validator (for `SliceFrame` `len = 0`
/// read-only proofs: writes zero bytes to memory and touches zero stack).
#[unsafe(no_mangle)]
pub extern "C" fn itch_validate_header(rx_ptr: i32, rx_len: i32) -> i32 {
    if rx_len < 1 {
        return 0;
    }
    // SAFETY: Caller satisfies `req_itch_validate` and `rx_len >= 1`.
    let rx = unsafe { slice::from_raw_parts(rx_ptr as *const u8, rx_len as usize) };
    match rx[0] {
        MSG_ADD_ORDER => {
            if rx_len >= (ADD_ORDER_LEN as i32) && decode_side(rx[19]) != SIDE_NONE {
                1
            } else {
                0
            }
        }
        MSG_ORDER_EXECUTED => {
            if rx_len >= (ORDER_EXECUTED_LEN as i32) {
                1
            } else {
                0
            }
        }
        _ => 0,
    }
}
