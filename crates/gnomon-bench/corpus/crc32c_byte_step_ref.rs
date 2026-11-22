#![no_std]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

const fn make_crc32c_table() -> [u32; 256] {
    let mut table = [0u32; 256];
    let mut i = 0usize;
    while i < 256 {
        let mut crc = i as u32;
        let mut bit = 0;
        while bit < 8 {
            if (crc & 1) != 0 {
                crc = (crc >> 1) ^ 0x82F6_3B78;
            } else {
                crc >>= 1;
            }
            bit += 1;
        }
        table[i] = crc;
        i += 1;
    }
    table
}

static CRC32C_TABLE: [u32; 256] = make_crc32c_table();

#[unsafe(no_mangle)]
pub extern "C" fn crc32c_byte_step(crc: i32, byte: i32) -> i32 {
    let c = crc as u32;
    let idx = ((c ^ (byte as u32)) & 0xFF) as usize;
    let entry = CRC32C_TABLE.get(idx).copied().unwrap_or(0);
    ((c >> 8) ^ entry) as i32
}
