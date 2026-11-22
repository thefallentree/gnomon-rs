#![no_std]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

#[unsafe(no_mangle)]
pub extern "C" fn chacha20_quarter_round(a: i32, b: i32, c: i32, d: i32) -> i64 {
    let mut x0 = a as u32;
    let mut x1 = b as u32;
    let mut x2 = c as u32;
    let mut x3 = d as u32;

    x0 = x0.wrapping_add(x1);
    x3 ^= x0;
    x3 = x3.rotate_left(16);

    x2 = x2.wrapping_add(x3);
    x1 ^= x2;
    x1 = x1.rotate_left(12);

    x0 = x0.wrapping_add(x1);
    x3 ^= x0;
    x3 = x3.rotate_left(8);

    x2 = x2.wrapping_add(x3);
    x1 ^= x2;
    x1 = x1.rotate_left(7);

    ((((x0 ^ x2) as u64) << 32) | ((x1 ^ x3) as u64)) as i64
}
