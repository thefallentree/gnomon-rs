#![no_std]

use core::sync::atomic::{AtomicU8, Ordering};

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

const CAP: usize = 16;
static BUF: [AtomicU8; CAP] = [const { AtomicU8::new(0) }; CAP];

#[unsafe(no_mangle)]
pub extern "C" fn cursor_u64_le_write(pos: i32, val: i64) -> i64 {
    let mut i = 0usize;
    while i < CAP {
        if let Some(slot) = BUF.get(i) {
            slot.store(0, Ordering::Relaxed);
        }
        i += 1;
    }

    let p = ((pos as u32) & 7) as usize;
    let bytes = (val as u64).to_le_bytes();
    let mut k = 0usize;
    while k < 8 {
        if let Some(slot) = BUF.get(p + k)
            && let Some(&b) = bytes.get(k)
        {
            slot.store(b, Ordering::Relaxed);
        }
        k += 1;
    }

    let mut hash: u64 = 0xCBF2_9CE4_8422_2325;
    let mut j = 0usize;
    while j < CAP {
        let b = BUF.get(j).map_or(0, |x| x.load(Ordering::Relaxed)) as u64;
        hash = (hash ^ b).wrapping_mul(0x0100_0000_01B3);
        j += 1;
    }
    hash as i64
}
