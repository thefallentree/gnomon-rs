#![no_std]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

#[unsafe(no_mangle)]
pub extern "C" fn bucket_wait_time_div0(tokens: i32, cost: i32, rate: i32) -> i64 {
    let tok = (tokens as u32) & 0xFFFF;
    let c = (cost as u32) & 0xFFFF;
    let r = (rate as u32) & 63;
    if tok >= c {
        return 0;
    }
    let need = c - tok;
    // BUG: omits `r == 0` infinite-wait error (`-1`) and uses floor division instead of ceiling
    need.checked_div(r).unwrap_or(0) as i64
}
