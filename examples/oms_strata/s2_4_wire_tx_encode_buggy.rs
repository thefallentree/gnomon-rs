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

const OUCH_ENTER_ORDER_TAG: u8 = b'O';
const OUCH_FRAME_LEN: usize = 48;
const OUCH_FIRM_ID: u64 = 0x474E_4F4D_4F4E_3031;

#[inline(always)]
fn valid_side(side: i32) -> bool {
    side == (b'B' as i32) || side == (b'S' as i32)
}

/// Precondition matching `s2_4_wire_tx_encode::req_ouch_encode`.
#[unsafe(no_mangle)]
pub extern "C" fn req_ouch_encode(
    tx_ptr: i32,
    tx_len: i32,
    _cl_ord_id: i64,
    _side: i32,
    _shares: i32,
    _symbol: i64,
    _price: i64,
    _tif: i32,
) -> i32 {
    if core::arch::wasm32::memory_size(0) < MIN_LIVE_PAGES {
        return 0;
    }
    let guard_lo = (WIRE_DMA_GUARD.as_ptr() as i32).wrapping_add(64);
    let live_lo = if guard_lo > LIVE_LO { guard_lo } else { LIVE_LO };
    if tx_ptr < live_lo || tx_ptr > LIVE_HI {
        return 0;
    }
    if tx_len < 0 || tx_len > LIVE_HI - tx_ptr {
        return 0;
    }
    1
}

/// Buggy Mutant 1 (`ouch_encode_buggy_overrun`):
/// Writes the 48-byte OUCH frame AND a 49th trailing byte (`0x0Au8`) at
/// `tx_ptr + 48`, clobbering the adjacent DMA ring slot!
/// Trap-free under `req_ouch_encode` (since `LIVE_HI + 48 < 17 * 65536`),
/// so `SliceFrame([tx_ptr, tx_ptr + 48))` is cleanly FALSIFIED!
#[unsafe(no_mangle)]
pub extern "C" fn ouch_encode_buggy_overrun(
    tx_ptr: i32,
    tx_len: i32,
    cl_ord_id: i64,
    side: i32,
    shares: i32,
    symbol: i64,
    price: i64,
    tif: i32,
) -> i32 {
    if tx_len < (OUCH_FRAME_LEN as i32) || !valid_side(side) || shares <= 0 {
        return 0;
    }
    let tx_base = tx_ptr as usize as *mut u8;
    unsafe {
        core::ptr::write(tx_base, OUCH_ENTER_ORDER_TAG);
        core::ptr::write_unaligned(tx_base.add(1) as *mut u64, (cl_ord_id as u64).to_be());
        core::ptr::write(tx_base.add(9), side as u8);
        core::ptr::write_unaligned(tx_base.add(10) as *mut u32, (shares as u32).to_be());
        core::ptr::write_unaligned(tx_base.add(14) as *mut u64, symbol as u64);
        core::ptr::write_unaligned(tx_base.add(22) as *mut u64, (price as u64).to_be());
        core::ptr::write_unaligned(tx_base.add(30) as *mut u32, (tif as u32).to_be());
        core::ptr::write_unaligned(tx_base.add(34) as *mut u64, OUCH_FIRM_ID.to_be());
        core::ptr::write_unaligned(tx_base.add(42) as *mut u32, 0u32);
        core::ptr::write_unaligned(tx_base.add(46) as *mut u16, 0u16);
        // BUG: 1-byte overrun at `tx_ptr + 48` clobbering adjacent DMA slot!
        core::ptr::write(tx_base.add(48), b'\n');
    }
    OUCH_FRAME_LEN as i32
}

/// Buggy Mutant 2 (`ouch_encode_buggy_endian`):
/// Writes `price` in little-endian instead of big-endian -> trap-free and
/// satisfies `SliceFrame([tx_ptr, tx_ptr + 48))`, but equivalence against
/// `ouch_encode_ref` / `ouch_encode_opt` is FALSIFIED!
#[unsafe(no_mangle)]
pub extern "C" fn ouch_encode_buggy_endian(
    tx_ptr: i32,
    tx_len: i32,
    cl_ord_id: i64,
    side: i32,
    shares: i32,
    symbol: i64,
    price: i64,
    tif: i32,
) -> i32 {
    if tx_len < (OUCH_FRAME_LEN as i32) || !valid_side(side) || shares <= 0 {
        return 0;
    }
    let tx_base = tx_ptr as usize as *mut u8;
    unsafe {
        core::ptr::write(tx_base, OUCH_ENTER_ORDER_TAG);
        core::ptr::write_unaligned(tx_base.add(1) as *mut u64, (cl_ord_id as u64).to_be());
        core::ptr::write(tx_base.add(9), side as u8);
        core::ptr::write_unaligned(tx_base.add(10) as *mut u32, (shares as u32).to_be());
        core::ptr::write_unaligned(tx_base.add(14) as *mut u64, symbol as u64);
        // BUG: little-endian store of big-endian OUCH `price`!
        core::ptr::write_unaligned(tx_base.add(22) as *mut u64, (price as u64).to_le());
        core::ptr::write_unaligned(tx_base.add(30) as *mut u32, (tif as u32).to_be());
        core::ptr::write_unaligned(tx_base.add(34) as *mut u64, OUCH_FIRM_ID.to_be());
        core::ptr::write_unaligned(tx_base.add(42) as *mut u32, 0u32);
        core::ptr::write_unaligned(tx_base.add(46) as *mut u16, 0u16);
    }
    OUCH_FRAME_LEN as i32
}

#[inline(always)]
fn slice_write_bytes_or_trap(s: &mut [u8], off: usize, src: &[u8]) {
    let end = off.wrapping_add(src.len());
    if end < off || end > s.len() {
        core::arch::wasm32::unreachable();
    }
    let mut i = 0usize;
    while i < src.len() {
        if let Some(slot) = s.get_mut(off + i) {
            *slot = src[i];
        } else {
            core::arch::wasm32::unreachable();
        }
        i += 1;
    }
}

/// Buggy Mutant 3 (`ouch_encode_buggy_short_buf`):
/// Forgets the `tx_len < 48` bounds check! When `tx_len < 48`, writing into
/// `tx[0..48]` traps (`unreachable`) -> trap-freedom contract and equivalence
/// BOTH FALSIFIED!
#[unsafe(no_mangle)]
pub extern "C" fn ouch_encode_buggy_short_buf(
    tx_ptr: i32,
    tx_len: i32,
    cl_ord_id: i64,
    side: i32,
    shares: i32,
    symbol: i64,
    price: i64,
    tif: i32,
) -> i32 {
    // BUG: missing `tx_len < 48` check!
    if !valid_side(side) || shares <= 0 {
        return 0;
    }
    let tx = unsafe { slice::from_raw_parts_mut(tx_ptr as *mut u8, tx_len as usize) };
    slice_write_bytes_or_trap(tx, 0, &[OUCH_ENTER_ORDER_TAG]);
    slice_write_bytes_or_trap(tx, 1, &(cl_ord_id as u64).to_be_bytes());
    slice_write_bytes_or_trap(tx, 9, &[side as u8]);
    slice_write_bytes_or_trap(tx, 10, &(shares as u32).to_be_bytes());
    slice_write_bytes_or_trap(tx, 14, &(symbol as u64).to_le_bytes());
    slice_write_bytes_or_trap(tx, 22, &(price as u64).to_be_bytes());
    slice_write_bytes_or_trap(tx, 30, &(tif as u32).to_be_bytes());
    slice_write_bytes_or_trap(tx, 34, &OUCH_FIRM_ID.to_be_bytes());
    slice_write_bytes_or_trap(tx, 42, &[0u8; 6]);
    OUCH_FRAME_LEN as i32
}
