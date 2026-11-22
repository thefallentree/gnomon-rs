#![no_std]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

#[unsafe(no_mangle)]
pub extern "C" fn bucket_consume_underflow(tokens: i32, cost: i32) -> i64 {
    let tok = tokens as u32;
    let c = cost as u32;
    if tok >= c {
        (1i64 << 32) | ((tok - c) as i64)
    } else {
        tok as i64
    }
}
