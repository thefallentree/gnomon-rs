#![no_std]

use core::sync::atomic::{AtomicU8, Ordering};

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

const CAP: usize = 16;
static BUF: [AtomicU8; CAP] = [const { AtomicU8::new(0) }; CAP];

#[unsafe(no_mangle)]
pub extern "C" fn ring_wrap_write(tail: i32, count: i32, byte_seed: i32) -> i32 {
    let mut i = 0usize;
    while i < CAP {
        if let Some(slot) = BUF.get(i) {
            slot.store(0, Ordering::Relaxed);
        }
        i += 1;
    }

    let t = (tail as u32) & 15;
    let n = ((count as u32) & 7) + 1;
    let first = n.min((CAP as u32) - t);

    let mut k = 0u32;
    while k < first {
        let val = ((byte_seed as u32).wrapping_add(k.wrapping_mul(7)) | 1) as u8;
        if let Some(slot) = BUF.get((t + k) as usize) {
            slot.store(val, Ordering::Relaxed);
        }
        k += 1;
    }
    // BUG: wrapped second segment [0 .. n - first] is omitted, silently dropping tail bytes

    let mut acc: u32 = 0x1357_9BDF;
    let mut j = 0usize;
    while j < CAP {
        let b = BUF.get(j).map_or(0, |s| s.load(Ordering::Relaxed)) as u32;
        acc = acc.rotate_left(5) ^ b;
        j += 1;
    }
    acc as i32
}
