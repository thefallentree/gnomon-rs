#![no_std]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

#[unsafe(no_mangle)]
pub extern "C" fn slab_bitmask_alloc(bitmap: i32, want_count: i32) -> i64 {
    let mut mask = bitmap as u32;
    let k = ((want_count as u32) & 3) + 1;
    let mut last_idx = 0u32;
    let mut step = 0u32;
    while step < k {
        if mask == 0 {
            return -1;
        }
        let idx = mask.trailing_zeros();
        mask &= !(1u32 << idx);
        last_idx = idx;
        step += 1;
    }
    (((mask as u64) << 32) | (last_idx as u64)) as i64
}
