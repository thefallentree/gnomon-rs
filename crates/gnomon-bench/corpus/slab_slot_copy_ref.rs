#![no_std]

use core::sync::atomic::{AtomicU8, Ordering};

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

const CAP: usize = 64;
static BUF: [AtomicU8; CAP] = [const { AtomicU8::new(0) }; CAP];

#[unsafe(no_mangle)]
pub extern "C" fn slab_slot_copy(src: i32, dst: i32, len: i32, seed: i32) -> i32 {
    let mut i = 0usize;
    while i < CAP {
        let v = (((seed as u32).wrapping_add((i as u32).wrapping_mul(7))) | 1) as u8;
        if let Some(slot) = BUF.get(i) {
            slot.store(v, Ordering::Relaxed);
        }
        i += 1;
    }

    let s = ((src as u32) & 31) as usize;
    let d = ((dst as u32) & 31) as usize;
    let n = (((len as u32) & 15) + 1) as usize;

    if d > s && d < s + n {
        let mut k = n;
        while k > 0 {
            k -= 1;
            let b = BUF.get(s + k).map_or(0, |x| x.load(Ordering::Relaxed));
            if let Some(slot) = BUF.get(d + k) {
                slot.store(b, Ordering::Relaxed);
            }
        }
    } else {
        let mut k = 0usize;
        while k < n {
            let b = BUF.get(s + k).map_or(0, |x| x.load(Ordering::Relaxed));
            if let Some(slot) = BUF.get(d + k) {
                slot.store(b, Ordering::Relaxed);
            }
            k += 1;
        }
    }

    let mut hash: u32 = 0x811C_9DC5;
    let mut j = 0usize;
    while j < CAP {
        let b = BUF.get(j).map_or(0, |x| x.load(Ordering::Relaxed)) as u32;
        hash = (hash ^ b).wrapping_mul(0x0100_0193);
        j += 1;
    }
    hash as i32
}
