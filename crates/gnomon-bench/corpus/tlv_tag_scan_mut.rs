#![no_std]

use core::sync::atomic::{AtomicU8, Ordering};

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

const CAP: usize = 32;
static BUF: [AtomicU8; CAP] = [const { AtomicU8::new(0) }; CAP];

#[unsafe(no_mangle)]
pub extern "C" fn tlv_tag_scan(seed: i32, target_tag: i32) -> i32 {
    let mut i = 0usize;
    while i < CAP {
        if let Some(slot) = BUF.get(i) {
            slot.store(0, Ordering::Relaxed);
        }
        i += 1;
    }

    let mut pos = 0usize;
    let mut rec = 0u32;
    let mut s = seed as u32;
    while rec < 5 && pos + 2 < CAP {
        s = s.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
        let tag = ((s >> 24) & 7) as u8;
        let len = (((s >> 16) & 3) + 1) as usize;
        if pos + 2 + len > CAP {
            break;
        }
        if let Some(slot) = BUF.get(pos) {
            slot.store(tag, Ordering::Relaxed);
        }
        if let Some(slot) = BUF.get(pos + 1) {
            slot.store(len as u8, Ordering::Relaxed);
        }
        let mut k = 0usize;
        while k < len {
            let val = (((s >> (k * 4)) ^ (k as u32)) | 1) as u8;
            if let Some(slot) = BUF.get(pos + 2 + k) {
                slot.store(val, Ordering::Relaxed);
            }
            k += 1;
        }
        pos += 2 + len;
        rec += 1;
    }
    let total_len = pos;
    let want = ((target_tag as u32) & 7) as u8;

    let mut cur = 0usize;
    while cur + 2 <= total_len {
        let tag = BUF.get(cur).map_or(0, |x| x.load(Ordering::Relaxed));
        let len = BUF.get(cur + 1).map_or(0, |x| x.load(Ordering::Relaxed)) as usize;
        if cur + 2 + len > total_len {
            return -1;
        }
        if tag == want {
            let mut sum = 0u32;
            let mut k = 0usize;
            while k < len {
                sum = sum.wrapping_add(
                    BUF.get(cur + 2 + k).map_or(0, |x| x.load(Ordering::Relaxed)) as u32,
                );
                k += 1;
            }
            return (((cur as u32) << 8) | (sum & 0xFF)) as i32;
        }
        // BUG: advances cursor by `1 + len` instead of `2 + len`, misaligning subsequent TLVs
        cur += 1 + len;
    }
    -1
}
