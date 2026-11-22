#![no_std]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

#[unsafe(no_mangle)]
pub extern "C" fn bitfield_pack_unpack(flags: i32, kind: i32, seq: i32, len: i32) -> i64 {
    let f = (flags as u64) & 0xF;
    // BUG: omits `& 0xFF` mask on `kind`, bleeding upper bits into `seq` and `len`
    let k = (kind as u64) << 4;
    let s = ((seq as u64) & 0xF_FFFF) << 12;
    let l = ((len as u32) as u64) << 32;
    let word = f | k | s | l;

    let uf = word & 0xF;
    let uk = (word >> 4) & 0xFF;
    let us = (word >> 12) & 0xF_FFFF;
    let ul = word >> 32;
    ((uf << 56) ^ (uk << 40) ^ (us << 16) ^ ul ^ word) as i64
}
