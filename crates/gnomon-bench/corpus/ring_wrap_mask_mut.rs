#![no_std]

use core::sync::atomic::{AtomicU8, Ordering};

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

const CAP: usize = 16;
const MASK: u32 = (CAP - 1) as u32;
// BUG: stale wrap mask from old 8-byte ring buffer aliases upper slots into 0..8
const BUGGY_MASK: u32 = 7;
static BUF: [AtomicU8; CAP] = [const { AtomicU8::new(0) }; CAP];

#[unsafe(no_mangle)]
pub extern "C" fn ring_wrap_mask(head: i32, push_count: i32, seed: i32) -> i32 {
    let mut i = 0usize;
    while i < CAP {
        if let Some(slot) = BUF.get(i) {
            slot.store(0, Ordering::Relaxed);
        }
        i += 1;
    }

    let h = (head as u32) & MASK;
    let n = ((push_count as u32) & MASK) + 1;
    let mut step = 0u32;
    while step < n {
        let idx = ((h.wrapping_add(step)) & BUGGY_MASK) as usize;
        let val = (((seed as u32).wrapping_add(step.wrapping_mul(13))) | 1) as u8;
        if let Some(slot) = BUF.get(idx) {
            slot.store(val, Ordering::Relaxed);
        }
        step += 1;
    }

    let mut hash: u32 = 0x811C_9DC5;
    let mut j = 0usize;
    while j < CAP {
        let b = BUF.get(j).map_or(0, |s| s.load(Ordering::Relaxed)) as u32;
        hash = (hash ^ b).wrapping_mul(0x0100_0193);
        j += 1;
    }
    hash as i32
}
