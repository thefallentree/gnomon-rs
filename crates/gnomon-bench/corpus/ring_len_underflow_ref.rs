#![no_std]

use core::sync::atomic::{AtomicU8, Ordering};

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

const CAP: usize = 32;
const MASK: u32 = (CAP - 1) as u32;
static BUF: [AtomicU8; CAP] = [const { AtomicU8::new(0) }; CAP];

#[unsafe(no_mangle)]
pub extern "C" fn ring_len_underflow(head: i32, tail: i32, push_byte: i32) -> i32 {
    let h = (head as u32) & MASK;
    let t = (tail as u32) & MASK;
    let used = t.wrapping_sub(h) & MASK;
    let avail = (CAP as u32).wrapping_sub(used);

    if let Some(slot) = BUF.get(t as usize) {
        slot.store((push_byte as u8) | 1, Ordering::Relaxed);
    }
    let read_back = BUF.get(t as usize).map_or(0, |s| s.load(Ordering::Relaxed)) as u32;
    (((avail & 0xFF) << 16) | ((used & 0xFF) << 8) | (read_back & 0xFF)) as i32
}
