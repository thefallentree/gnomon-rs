#![no_std]

use core::sync::atomic::{AtomicU8, Ordering};

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

const CAP: usize = 64;
static BUF: [AtomicU8; CAP] = [const { AtomicU8::new(0) }; CAP];

#[unsafe(no_mangle)]
pub extern "C" fn bump_reset(used_before: i32, alloc_size: i32, seed: i32) -> i32 {
    let mut i = 0usize;
    while i < CAP {
        let dirty = (((seed as u32).wrapping_add((i as u32).wrapping_mul(11))) | 1) as u8;
        if let Some(slot) = BUF.get(i) {
            slot.store(dirty, Ordering::Relaxed);
        }
        i += 1;
    }

    let used = (((used_before as u32) & 63) + 1) as usize;
    let mut j = 0usize;
    while j < used {
        if let Some(slot) = BUF.get(j) {
            slot.store(0, Ordering::Relaxed);
        }
        j += 1;
    }

    let n = (((alloc_size as u32) & 15) + 1) as usize;
    let limit = n.min(used);
    let mut sum: u32 = 0;
    let mut k = 0usize;
    while k < limit {
        sum = sum.wrapping_add(BUF.get(k).map_or(0, |s| s.load(Ordering::Relaxed)) as u32);
        k += 1;
    }
    sum as i32
}
