#![no_std]

use core::sync::atomic::{AtomicU8, Ordering};

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

static BUF: [AtomicU8; 8] = [const { AtomicU8::new(0) }; 8];

#[unsafe(no_mangle)]
pub extern "C" fn varint_u32_encode(val: i32) -> i64 {
    let mut i = 0usize;
    while i < 8 {
        if let Some(slot) = BUF.get(i) {
            slot.store(0, Ordering::Relaxed);
        }
        i += 1;
    }

    // BUG: uses signed `i32` arithmetic right shift instead of unsigned `u32` logical shift
    let mut v = val;
    let mut len = 0usize;
    while len < 5 {
        let mut byte = (v & 0x7F) as u8;
        v >>= 7;
        if v != 0 {
            byte |= 0x80;
        }
        if let Some(slot) = BUF.get(len) {
            slot.store(byte, Ordering::Relaxed);
        }
        len += 1;
        if v == 0 {
            break;
        }
    }

    let mut packed: u64 = (len as u64) << 40;
    let mut j = 0usize;
    while j < 5 {
        let b = BUF.get(j).map_or(0, |s| s.load(Ordering::Relaxed)) as u64;
        packed |= b << (j * 8);
        j += 1;
    }
    packed as i64
}
