#![no_std]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

#[unsafe(no_mangle)]
pub extern "C" fn siphash_round(v0: i64, v1: i64, v2: i64, v3: i64) -> i64 {
    let mut x0 = v0 as u64;
    let mut x1 = v1 as u64;
    let mut x2 = v2 as u64;
    let mut x3 = v3 as u64;

    x0 = x0.wrapping_add(x1);
    x1 = x1.rotate_left(13);
    x1 ^= x0;
    x0 = x0.rotate_left(32);

    x2 = x2.wrapping_add(x3);
    x3 = x3.rotate_left(16);
    x3 ^= x2;

    x0 = x0.wrapping_add(x3);
    x3 = x3.rotate_left(21);
    x3 ^= x0;

    x2 = x2.wrapping_add(x1);
    x1 = x1.rotate_left(17);
    x1 ^= x2;
    x2 = x2.rotate_left(32);

    (x0 ^ x1 ^ x2 ^ x3) as i64
}
