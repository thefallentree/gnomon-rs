#![no_std]

use core::sync::atomic::{AtomicU8, Ordering};

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

const CAP: usize = 24;
static BUF: [AtomicU8; CAP] = [const { AtomicU8::new(0) }; CAP];

#[unsafe(no_mangle)]
pub extern "C" fn tlv_checksum(seed: i32, payload_len: i32) -> i32 {
    let len = ((payload_len as u32) & 15) as usize;
    let s = seed as u32;
    if let Some(slot) = BUF.get(0) {
        slot.store(((s >> 8) | 1) as u8, Ordering::Relaxed);
    }
    if let Some(slot) = BUF.get(1) {
        slot.store(len as u8, Ordering::Relaxed);
    }
    let mut k = 0usize;
    while k < len {
        let b = ((s.wrapping_add((k as u32).wrapping_mul(29))) | 1) as u8;
        if let Some(slot) = BUF.get(2 + k) {
            slot.store(b, Ordering::Relaxed);
        }
        k += 1;
    }

    let mut csum: u32 = 0x5A;
    let mut i = 0usize;
    // BUG: off-by-one loop bound `1 + len` drops the final payload byte (or length byte when len==0)
    while i < 1 + len {
        let b = BUF.get(i).map_or(0, |x| x.load(Ordering::Relaxed)) as u32;
        csum = (csum.rotate_left(3) ^ b).wrapping_add(17) & 0xFFFF;
        i += 1;
    }
    csum as i32
}
