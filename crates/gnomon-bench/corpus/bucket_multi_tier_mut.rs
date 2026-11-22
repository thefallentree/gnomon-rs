#![no_std]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

#[unsafe(no_mangle)]
pub extern "C" fn bucket_multi_tier(b1: i32, b2: i32, cost: i32, cap1: i32, cap2: i32) -> i64 {
    let c1 = ((cap1 as u32) & 255).max(1);
    let c2 = ((cap2 as u32) & 255).max(1);
    let mut t1 = ((b1 as u32) & 255).min(c1);
    let mut t2 = ((b2 as u32) & 255).min(c2);
    let c = (cost as u32) & 255;

    // BUG: non-atomic tier deduction drains `t1` before checking whether `t2 >= c`
    let mut allowed = 0u64;
    if t1 >= c {
        t1 -= c;
        if t2 >= c {
            t2 -= c;
            allowed = 1;
        }
    }
    ((allowed << 32) | ((t1 as u64) << 16) | (t2 as u64)) as i64
}
