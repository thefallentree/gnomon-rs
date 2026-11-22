#![no_std]

use core::sync::atomic::{AtomicU8, Ordering};

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

const CAP: usize = 32;
static BUF: [AtomicU8; CAP] = [const { AtomicU8::new(0) }; CAP];

#[unsafe(no_mangle)]
pub extern "C" fn cursor_u16_be_read(seed: i32, pos: i32) -> i32 {
    let mut s = seed as u32;
    let mut i = 0usize;
    while i < CAP {
        s = s.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
        if let Some(slot) = BUF.get(i) {
            slot.store((s >> 24) as u8, Ordering::Relaxed);
        }
        i += 1;
    }

    let p = ((pos as u32) & 30) as usize;
    let b0 = BUF.get(p).map_or(0, |x| x.load(Ordering::Relaxed)) as u32;
    let b1 = BUF.get(p + 1).map_or(0, |x| x.load(Ordering::Relaxed)) as u32;
    // BUG: decodes little-endian `(b1 << 8) | b0` instead of big-endian `(b0 << 8) | b1`
    ((b1 << 8) | b0) as i32
}
