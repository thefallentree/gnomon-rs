#![no_std]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

#[unsafe(no_mangle)]
pub extern "C" fn varint_u32_decode(w0: i32, w1: i32) -> i64 {
    let a = (w0 as u32).to_le_bytes();
    let b = (w1 as u32).to_le_bytes();
    let bytes = [a[0], a[1], a[2], a[3], b[0], b[1], b[2], b[3]];

    let mut result: u32 = 0;
    let mut shift: u32 = 0;
    let mut i = 0usize;
    while i < 5 {
        let byte = match bytes.get(i) {
            Some(&v) => v,
            None => return -1,
        };
        // BUG: omits `i == 4 && byte >= 0x10` overflow & continuation bit validation on 5th byte
        result |= ((byte & 0x7F) as u32).wrapping_shl(shift);
        if (byte & 0x80) == 0 || i == 4 {
            return result as i64;
        }
        shift += 7;
        i += 1;
    }
    -1
}
