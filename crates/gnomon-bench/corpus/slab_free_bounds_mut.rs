#![no_std]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

#[unsafe(no_mangle)]
pub extern "C" fn slab_free_bounds(bitmap: i32, ptr_offset: i32) -> i32 {
    let occ = (bitmap as u32) & 0xFFFF;
    let off = ptr_offset & 255;
    // BUG: omits `(off & 7) != 0` alignment validation, freeing slot on interior pointer
    if !(0..128).contains(&off) {
        return -1;
    }
    let slot = (off >> 3) as u32;
    if (occ & (1u32 << slot)) == 0 {
        return -2;
    }
    (occ & !(1u32 << slot)) as i32
}
