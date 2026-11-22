#![no_std]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

#[unsafe(no_mangle)]
pub extern "C" fn bucket_burst_clamp(tokens: i32, add: i32, burst: i32) -> i32 {
    let tok = (tokens as u32) & 31;
    let a = (add as u32) & 31;
    let cap = ((burst as u32) & 31).max(1);
    let sum = tok + a;
    // BUG: off-by-one clamp (`sum >= cap` clamps to `cap - 1` instead of `cap`)
    if sum >= cap { (cap - 1) as i32 } else { sum as i32 }
}
