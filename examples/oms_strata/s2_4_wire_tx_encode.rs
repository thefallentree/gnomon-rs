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

// Nasdaq OUCH 5.0 EnterOrder (48-byte outbound frame)
const OUCH_ENTER_ORDER_TAG: u8 = b'O';
const OUCH_FRAME_LEN: usize = 48;
/// Fixed 8-byte ASCII firm identifier (`"GNOMON01"`), encoded big-endian at `[34..42]`.
const OUCH_FIRM_ID: u64 = 0x474E_4F4D_4F4E_3031;

#[inline(always)]
fn valid_side(side: i32) -> bool {
    side == (b'B' as i32) || side == (b'S' as i32)
}

/// Shadow-stack frame builder: materializes the 48-byte big-endian OUCH 5.0
/// `EnterOrder` frame into a caller-allocated `[u8; 48]` buffer on `__stack_pointer`.
#[inline(never)]
fn build_ouch_frame_on_stack(
    frame: &mut [u8; OUCH_FRAME_LEN],
    cl_ord_id: u64,
    side: u8,
    shares: u32,
    symbol: u64,
    price: u64,
    tif: u32,
) {
    frame[0] = OUCH_ENTER_ORDER_TAG;
    frame[1..9].copy_from_slice(&cl_ord_id.to_be_bytes());
    frame[9] = side;
    frame[10..14].copy_from_slice(&shares.to_be_bytes());
    frame[14..22].copy_from_slice(&symbol.to_le_bytes());
    frame[22..30].copy_from_slice(&price.to_be_bytes());
    frame[30..34].copy_from_slice(&tif.to_be_bytes());
    frame[34..42].copy_from_slice(&OUCH_FIRM_ID.to_be_bytes());
    frame[42] = 0;
    frame[43] = 0;
    frame[44] = 0;
    frame[45] = 0;
    frame[46] = 0;
    frame[47] = 0;
}

/// Shadow-stack commit helper: copies the staged 48-byte frame into `dst`.
#[inline(never)]
fn commit_ouch_frame(src: &[u8; OUCH_FRAME_LEN], dst: &mut [u8; OUCH_FRAME_LEN]) {
    let mut i = 0usize;
    while i < OUCH_FRAME_LEN {
        dst[i] = src[i];
        i += 1;
    }
}

/// Precondition for `ouch_encode_ref` and `ouch_encode_opt`:
/// - Linear memory has at least 17 pages (`>= 1_114_112` bytes).
/// - `[tx_ptr, tx_ptr + tx_len)` lies within `[1_048_576 + 64, 1_048_576 + 32_768)`
///   with `tx_len >= 0` and no 32-bit wraparound.
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

/// S2.4 Reference OUCH 5.0 `EnterOrder` 48-byte Encoder (shadow-stack buffered):
/// Builds a local `[u8; 48]` frame on `__stack_pointer` (`Global(0)`) and copies
/// it into `tx_ptr[0..48]`.
/// Layout:
///   `[0]`      `b'O'`
///   `[1..9]`   `cl_ord_id` (`u64` BE)
///   `[9]`      `side` (`b'B'` / `b'S'`)
///   `[10..14]` `shares` (`u32` BE)
///   `[14..22]` `symbol` (`u64` raw 8-byte ASCII)
///   `[22..30]` `price` (`u64` BE)
///   `[30..34]` `tif` (`u32` BE)
///   `[34..42]` `firm_id` (`u64` BE, `"GNOMON01"`)
///   `[42..48]` reserved zeros
/// Returns `48` on success, or `0` if `tx_len < 48` or invalid `side`/`shares`.
#[unsafe(no_mangle)]
pub extern "C" fn ouch_encode_ref(
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
    // SAFETY: Caller satisfies `req_ouch_encode` and `tx_len >= 48`.
    let tx = unsafe { slice::from_raw_parts_mut(tx_ptr as *mut u8, tx_len as usize) };
    let Some(dst_slice) = tx.get_mut(..OUCH_FRAME_LEN) else {
        return 0;
    };
    let Ok(dst_fixed): Result<&mut [u8; OUCH_FRAME_LEN], _> = dst_slice.try_into() else {
        return 0;
    };

    let mut frame = [0u8; OUCH_FRAME_LEN];
    build_ouch_frame_on_stack(
        &mut frame,
        cl_ord_id as u64,
        side as u8,
        shares as u32,
        symbol as u64,
        price as u64,
        tif as u32,
    );
    commit_ouch_frame(&frame, dst_fixed);
    OUCH_FRAME_LEN as i32
}

/// S2.4 Zero-Copy Optimized OUCH 5.0 `EnterOrder` 48-byte Encoder:
/// Writes directly into `tx_ptr[0..48]` using unaligned wide big-endian stores
/// with ZERO shadow-stack frame (no `Global(0)` accesses).
#[unsafe(no_mangle)]
pub extern "C" fn ouch_encode_opt(
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
    // SAFETY: Caller satisfies `req_ouch_encode` and `tx_len >= 48`.
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
    }
    OUCH_FRAME_LEN as i32
}
