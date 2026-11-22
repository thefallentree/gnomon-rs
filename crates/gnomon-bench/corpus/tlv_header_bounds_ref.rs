#![no_std]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

#[unsafe(no_mangle)]
pub extern "C" fn tlv_header_bounds(pkt_len: i32, offset: i32, tlv_len: i32) -> i32 {
    let pkt = ((pkt_len as u32) & 255) as u64;
    let off = (offset as u32) as u64;
    let len = (tlv_len as u32) as u64;
    if off + 4 + len <= pkt { 1 } else { 0 }
}
