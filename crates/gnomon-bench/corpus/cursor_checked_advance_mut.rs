#![no_std]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

#[unsafe(no_mangle)]
pub extern "C" fn cursor_checked_advance(pos: i32, step: i32, limit: i32) -> i64 {
    let p = pos as u32;
    let s = step as u32;
    let lim = (limit as u32).max(1);
    // BUG: unchecked `wrapping_add` wraps `p + s` past `u32::MAX` below `lim`
    let next = p.wrapping_add(s);
    if next <= lim { next as i64 } else { -1 }
}
