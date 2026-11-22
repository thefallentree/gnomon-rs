#![no_std]

use core::sync::atomic::{AtomicU8, Ordering};

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

const fn make_crc32c_table() -> [u32; 256] {
    let mut table = [0u32; 256];
    let mut i = 0usize;
    while i < 256 {
        let mut crc = i as u32;
        let mut bit = 0;
        while bit < 8 {
            if (crc & 1) != 0 {
                crc = (crc >> 1) ^ 0x82F6_3B78;
            } else {
                crc >>= 1;
            }
            bit += 1;
        }
        table[i] = crc;
        i += 1;
    }
    table
}

static CRC32C_TABLE: [u32; 256] = make_crc32c_table();
const CAP: usize = 64;
static BUF: [AtomicU8; CAP] = [const { AtomicU8::new(0) }; CAP];

#[unsafe(no_mangle)]
pub extern "C" fn crc32c_buf_fold(seed: i32, len: i32) -> i32 {
    let n = (((len as u32) & 63) + 1) as usize;
    let mut s = seed as u32;
    let mut i = 0usize;
    while i < n {
        s = s.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
        if let Some(slot) = BUF.get(i) {
            slot.store((s >> 24) as u8, Ordering::Relaxed);
        }
        i += 1;
    }

    let mut crc = !0u32;
    let mut j = 0usize;
    while j < n {
        let b = BUF.get(j).map_or(0, |x| x.load(Ordering::Relaxed)) as u32;
        let idx = ((crc ^ b) & 0xFF) as usize;
        let entry = CRC32C_TABLE.get(idx).copied().unwrap_or(0);
        crc = (crc >> 8) ^ entry;
        j += 1;
    }
    // BUG: forgets final bitwise inversion `!crc`
    crc as i32
}
