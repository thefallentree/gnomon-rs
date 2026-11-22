#![no_std]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

#[unsafe(no_mangle)]
pub extern "C" fn bucket_refill_overflow(tokens: i32, elapsed: i32, rate: i32, burst: i32) -> i32 {
    let cur = (tokens as u32) & 0xFFFF;
    let dt = elapsed as u32;
    let r = rate as u32;
    let cap = (burst as u32).max(1);
    // BUG: computes `elapsed * rate` in 32-bit wrapping arithmetic, losing tokens on overflow
    let add = dt.wrapping_mul(r);
    cur.saturating_add(add).min(cap) as i32
}
