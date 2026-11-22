#![no_std]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

#[unsafe(no_mangle)]
pub extern "C" fn tlv_header_bounds(pkt_len: i32, offset: i32, tlv_len: i32) -> i32 {
    let pkt = ((pkt_len as u32) & 255) as i32;
    // BUG: signed 32-bit bounds comparison wraps/accepts negative or overflowing offset/len
    if offset.wrapping_add(4).wrapping_add(tlv_len) <= pkt { 1 } else { 0 }
}
