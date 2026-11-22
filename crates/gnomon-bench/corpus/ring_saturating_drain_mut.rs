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
pub extern "C" fn ring_saturating_drain(head: i32, len: i32, drain_n: i32, seed: i32) -> i32 {
    let mut i = 0usize;
    while i < CAP {
        let v = (((seed as u32) ^ ((i as u32).wrapping_mul(37))) | 1) as u8;
        if let Some(slot) = BUF.get(i) {
            slot.store(v, Ordering::Relaxed);
        }
        i += 1;
    }

    let h = (head as u32) & MASK;
    let l = (len as u32) & MASK;
    let k = (drain_n as u32) & MASK;

    // BUG: fails to saturate drain count `k` to `l`, causing `new_len` underflow and stale reads
    let actual = k;
    let new_len = l.wrapping_sub(actual);
    let mut sum: u32 = 0;
    let mut step = 0u32;
    while step < actual {
        let idx = (h.wrapping_add(step) & MASK) as usize;
        let b = BUF.get(idx).map_or(0, |s| s.load(Ordering::Relaxed)) as u32;
        sum = sum.wrapping_add(b.wrapping_mul(step + 1));
        step += 1;
    }
    (((new_len & 0xFFFF) << 16) | (sum & 0xFFFF)) as i32
}
