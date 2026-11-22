#![no_std]

use core::sync::atomic::{AtomicU8, Ordering};

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

const CAP: usize = 32;
static BUF: [AtomicU8; CAP] = [const { AtomicU8::new(0) }; CAP];

#[unsafe(no_mangle)]
pub extern "C" fn cursor_u32_be_bounds(buf_len: i32, pos: i32, seed: i32) -> i64 {
    let mut s = seed as u32;
    let mut i = 0usize;
    while i < CAP {
        s = s.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
        if let Some(slot) = BUF.get(i) {
            slot.store(((s >> 24) | 1) as u8, Ordering::Relaxed);
        }
        i += 1;
    }

    let len = ((buf_len as u32) & 31) as usize;
    let p = ((pos as u32) & 31) as usize;
    // BUG: off-by-one bounds check (`p + 3 > len` instead of `p + 4 > len`) reads past `len`
    if p + 3 > len {
        return -1;
    }

    let b0 = BUF.get(p).map_or(0, |x| x.load(Ordering::Relaxed)) as u32;
    let b1 = BUF.get(p + 1).map_or(0, |x| x.load(Ordering::Relaxed)) as u32;
    let b2 = BUF.get(p + 2).map_or(0, |x| x.load(Ordering::Relaxed)) as u32;
    let b3 = BUF.get(p + 3).map_or(0, |x| x.load(Ordering::Relaxed)) as u32;
    let val = (b0 << 24) | (b1 << 16) | (b2 << 8) | b3;
    (((p + 4) as i64) << 32) | (val as i64)
}
