#![no_std]

use core::sync::atomic::{AtomicU8, Ordering};

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

const CAP: usize = 64;
static BUF: [AtomicU8; CAP] = [const { AtomicU8::new(0) }; CAP];

#[unsafe(no_mangle)]
pub extern "C" fn bump_alloc_overflow(cursor: i32, size: i32, align_pow: i32) -> i64 {
    let c = (cursor as u32) & 63;
    let sz = (size as u32) & 63;
    let align = 1u32 << ((align_pow as u32) & 3);
    let aligned = (c + (align - 1)) & !(align - 1);
    let end = aligned + sz;
    if end > CAP as u32 {
        return -1;
    }
    let mut i = aligned as usize;
    while i < end as usize {
        if let Some(slot) = BUF.get(i) {
            slot.store(0, Ordering::Relaxed);
        }
        i += 1;
    }
    ((aligned as i64) << 32) | (end as i64)
}
