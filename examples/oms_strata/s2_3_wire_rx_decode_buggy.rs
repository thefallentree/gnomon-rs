#![no_std]

use core::slice;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

/// 64-byte static guard placed in `.bss` right above the 1 MiB shadow stack
/// (`0x10_0000`), ensuring `min_pages >= 17` (`1_114_112` bytes).
static WIRE_DMA_GUARD: [u8; 64] = [0; 64];

const STACK_TOP: i32 = 1_048_576;
const LIVE_LO: i32 = STACK_TOP + 64;
const LIVE_HI: i32 = STACK_TOP + 32_768;
const MIN_LIVE_PAGES: usize = 17;

const MSG_ADD_ORDER: u8 = b'A';
const MSG_ORDER_EXECUTED: u8 = b'E';
const ADD_ORDER_LEN: usize = 36;
const ORDER_EXECUTED_LEN: usize = 31;
const OUT_RECORD_LEN: usize = 32;

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

/// Precondition matching `s2_3_wire_rx_decode::req_itch_decode`.
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

#[inline(always)]
fn slice_get_or_trap(s: &[u8], idx: usize) -> u8 {
    match s.get(idx) {
        Some(&b) => b,
        None => core::arch::wasm32::unreachable(),
    }
}

/// Buggy Mutant 1 (`itch_decode_buggy_short_pkt`):
/// Checks `rx_len < 32` instead of `rx_len < 36` for 36-byte `AddOrder` packets!
/// On 32..=35 byte `AddOrder` packets, bounds-checked slice access at bytes
/// `32..36` traps (`unreachable`) -> trap-freedom contract and equivalence
/// BOTH FALSIFIED!
#[unsafe(no_mangle)]
pub extern "C" fn itch_decode_buggy_short_pkt(
    rx_ptr: i32,
    rx_len: i32,
    out_ptr: i32,
    out_len: i32,
) -> i32 {
    if rx_len < 1 || out_len < (OUT_RECORD_LEN as i32) {
        return 0;
    }
    let rx = unsafe { slice::from_raw_parts(rx_ptr as *const u8, rx_len as usize) };
    let out_base = out_ptr as usize as *mut u8;

    match slice_get_or_trap(rx, 0) {
        MSG_ADD_ORDER => {
            // BUG: checks 32 instead of 36!
            if rx_len < 32 {
                return 0;
            }
            let side = decode_side(slice_get_or_trap(rx, 19));
            if side == SIDE_NONE {
                return 0;
            }
            let order_ref = u64::from_be_bytes([
                slice_get_or_trap(rx, 11),
                slice_get_or_trap(rx, 12),
                slice_get_or_trap(rx, 13),
                slice_get_or_trap(rx, 14),
                slice_get_or_trap(rx, 15),
                slice_get_or_trap(rx, 16),
                slice_get_or_trap(rx, 17),
                slice_get_or_trap(rx, 18),
            ]) as i64;
            let shares = (u32::from_be_bytes([
                slice_get_or_trap(rx, 20),
                slice_get_or_trap(rx, 21),
                slice_get_or_trap(rx, 22),
                slice_get_or_trap(rx, 23),
            ]) as u64) as i64;
            // Traps on rx_len in 32..=35!
            let price = (u32::from_be_bytes([
                slice_get_or_trap(rx, 32),
                slice_get_or_trap(rx, 33),
                slice_get_or_trap(rx, 34),
                slice_get_or_trap(rx, 35),
            ]) as u64) as i64;
            unsafe {
                core::ptr::write_unaligned(out_base as *mut i32, KIND_ADD_ORDER);
                core::ptr::write_unaligned(out_base.add(4) as *mut i32, side);
                core::ptr::write_unaligned(out_base.add(8) as *mut i64, order_ref);
                core::ptr::write_unaligned(out_base.add(16) as *mut i64, shares);
                core::ptr::write_unaligned(out_base.add(24) as *mut i64, price);
            }
            1
        }
        MSG_ORDER_EXECUTED => {
            if rx_len < (ORDER_EXECUTED_LEN as i32) {
                return 0;
            }
            let order_ref = u64::from_be_bytes([
                slice_get_or_trap(rx, 11),
                slice_get_or_trap(rx, 12),
                slice_get_or_trap(rx, 13),
                slice_get_or_trap(rx, 14),
                slice_get_or_trap(rx, 15),
                slice_get_or_trap(rx, 16),
                slice_get_or_trap(rx, 17),
                slice_get_or_trap(rx, 18),
            ]) as i64;
            let exec_shares = (u32::from_be_bytes([
                slice_get_or_trap(rx, 19),
                slice_get_or_trap(rx, 20),
                slice_get_or_trap(rx, 21),
                slice_get_or_trap(rx, 22),
            ]) as u64) as i64;
            let match_num = u64::from_be_bytes([
                slice_get_or_trap(rx, 23),
                slice_get_or_trap(rx, 24),
                slice_get_or_trap(rx, 25),
                slice_get_or_trap(rx, 26),
                slice_get_or_trap(rx, 27),
                slice_get_or_trap(rx, 28),
                slice_get_or_trap(rx, 29),
                slice_get_or_trap(rx, 30),
            ]) as i64;
            unsafe {
                core::ptr::write_unaligned(out_base as *mut i32, KIND_ORDER_EXECUTED);
                core::ptr::write_unaligned(out_base.add(4) as *mut i32, SIDE_NONE);
                core::ptr::write_unaligned(out_base.add(8) as *mut i64, order_ref);
                core::ptr::write_unaligned(out_base.add(16) as *mut i64, exec_shares);
                core::ptr::write_unaligned(out_base.add(24) as *mut i64, match_num);
            }
            1
        }
        _ => 0,
    }
}

/// Buggy Mutant 2 (`itch_decode_buggy_endian`):
/// Decodes `order_ref` in little-endian instead of big-endian -> trap-free and
/// satisfies `SliceFrame([out_ptr, out_ptr + 32))`, but equivalence against
/// `itch_decode_ref` / `itch_decode_opt` is FALSIFIED!
#[unsafe(no_mangle)]
pub extern "C" fn itch_decode_buggy_endian(
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
            // BUG: little-endian decode of big-endian ITCH `order_ref`!
            let order_ref =
                u64::from_le(core::ptr::read_unaligned(rx_base.add(11) as *const u64)) as i64;
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
            // BUG: little-endian decode of big-endian ITCH `order_ref`!
            let order_ref =
                u64::from_le(core::ptr::read_unaligned(rx_base.add(11) as *const u64)) as i64;
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

/// Buggy Mutant 3 (`itch_decode_buggy_clobber_rx`):
/// Decodes correctly into `out_ptr[0..32]`, but accidentally writes 1 byte
/// (`0u8`) to `rx_ptr[0]` (strictly outside `[out_ptr, out_ptr + 32)` and
/// `[out_ptr, out_ptr + out_len)` because `rx` and `out` are disjoint!).
/// Trap-free, but `SliceFrame([out_ptr, out_ptr + 32))` is FALSIFIED!
#[unsafe(no_mangle)]
pub extern "C" fn itch_decode_buggy_clobber_rx(
    rx_ptr: i32,
    rx_len: i32,
    out_ptr: i32,
    out_len: i32,
) -> i32 {
    if rx_len < 1 || out_len < (OUT_RECORD_LEN as i32) {
        return 0;
    }
    let rx_base = rx_ptr as usize as *mut u8;
    let out_base = out_ptr as usize as *mut u8;

    unsafe {
        let msg_type = core::ptr::read(rx_base as *const u8);
        if msg_type == MSG_ADD_ORDER {
            if rx_len < (ADD_ORDER_LEN as i32) {
                return 0;
            }
            let side = decode_side(core::ptr::read((rx_base as *const u8).add(19)));
            if side == SIDE_NONE {
                return 0;
            }
            let order_ref =
                u64::from_be(core::ptr::read_unaligned((rx_base as *const u8).add(11) as *const u64))
                    as i64;
            let shares = (u32::from_be(core::ptr::read_unaligned(
                (rx_base as *const u8).add(20) as *const u32,
            )) as u64) as i64;
            let price = (u32::from_be(core::ptr::read_unaligned(
                (rx_base as *const u8).add(32) as *const u32,
            )) as u64) as i64;

            core::ptr::write_unaligned(out_base as *mut i32, KIND_ADD_ORDER);
            core::ptr::write_unaligned(out_base.add(4) as *mut i32, side);
            core::ptr::write_unaligned(out_base.add(8) as *mut i64, order_ref);
            core::ptr::write_unaligned(out_base.add(16) as *mut i64, shares);
            core::ptr::write_unaligned(out_base.add(24) as *mut i64, price);
            // BUG: clobbers 1 byte in RX DMA buffer outside `[out_ptr, out_ptr + 32)`!
            core::ptr::write(rx_base, 0u8);
            1
        } else if msg_type == MSG_ORDER_EXECUTED {
            if rx_len < (ORDER_EXECUTED_LEN as i32) {
                return 0;
            }
            let order_ref =
                u64::from_be(core::ptr::read_unaligned((rx_base as *const u8).add(11) as *const u64))
                    as i64;
            let exec_shares = (u32::from_be(core::ptr::read_unaligned(
                (rx_base as *const u8).add(19) as *const u32,
            )) as u64) as i64;
            let match_num =
                u64::from_be(core::ptr::read_unaligned((rx_base as *const u8).add(23) as *const u64))
                    as i64;

            core::ptr::write_unaligned(out_base as *mut i32, KIND_ORDER_EXECUTED);
            core::ptr::write_unaligned(out_base.add(4) as *mut i32, SIDE_NONE);
            core::ptr::write_unaligned(out_base.add(8) as *mut i64, order_ref);
            core::ptr::write_unaligned(out_base.add(16) as *mut i64, exec_shares);
            core::ptr::write_unaligned(out_base.add(24) as *mut i64, match_num);
            // BUG: clobbers 1 byte in RX DMA buffer outside `[out_ptr, out_ptr + 32)`!
            core::ptr::write(rx_base, 0u8);
            1
        } else {
            0
        }
    }
}
