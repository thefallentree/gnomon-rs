#![no_std]

use core::sync::atomic::{AtomicU8, Ordering};

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

const CAP: usize = 16;
const MASK: u32 = (CAP - 1) as u32;
static BUF: [AtomicU8; CAP] = [const { AtomicU8::new(0) }; CAP];

#[unsafe(no_mangle)]
pub extern "C" fn ring_peek_bounds(head: i32, len: i32, offset: i32, seed: i32) -> i32 {
    let mut i = 0usize;
    while i < CAP {
        let v = ((seed as u32).wrapping_add((i as u32).wrapping_mul(19)) & 0xFF) as u8;
        if let Some(slot) = BUF.get(i) {
            slot.store(v, Ordering::Relaxed);
        }
        i += 1;
    }

    let h = (head as u32) & MASK;
    let l = (len as u32) & MASK;
    let off = (offset as u32) & MASK;

    if off >= l {
        return -1;
    }
    let idx = (h.wrapping_add(off) & MASK) as usize;
    BUF.get(idx).map_or(-1, |s| s.load(Ordering::Relaxed) as i32)
}
