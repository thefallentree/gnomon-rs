#![no_std]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

#[inline(always)]
fn sipround(v0: &mut u64, v1: &mut u64, v2: &mut u64, v3: &mut u64) {
    *v0 = v0.wrapping_add(*v1);
    *v1 = v1.rotate_left(13);
    *v1 ^= *v0;
    *v0 = v0.rotate_left(32);
    *v2 = v2.wrapping_add(*v3);
    *v3 = v3.rotate_left(16);
    *v3 ^= *v2;
    *v0 = v0.wrapping_add(*v3);
    *v3 = v3.rotate_left(21);
    *v3 ^= *v0;
    *v2 = v2.wrapping_add(*v1);
    *v1 = v1.rotate_left(17);
    *v1 ^= *v2;
    *v2 = v2.rotate_left(32);
}

#[unsafe(no_mangle)]
pub extern "C" fn siphash_2_4_u64(k0: i64, k1: i64, msg: i64) -> i64 {
    let key0 = k0 as u64;
    let key1 = k1 as u64;
    let m = msg as u64;

    let mut v0 = 0x736f_6d65_7073_6575u64 ^ key0;
    let mut v1 = 0x646f_7261_6e64_6f6du64 ^ key1;
    let mut v2 = 0x6c79_6765_6e65_7261u64 ^ key0;
    let mut v3 = 0x7465_6462_7974_6573u64 ^ key1;

    v3 ^= m;
    sipround(&mut v0, &mut v1, &mut v2, &mut v3);
    sipround(&mut v0, &mut v1, &mut v2, &mut v3);
    v0 ^= m;

    let b = 8u64 << 56;
    v3 ^= b;
    sipround(&mut v0, &mut v1, &mut v2, &mut v3);
    sipround(&mut v0, &mut v1, &mut v2, &mut v3);
    v0 ^= b;

    // BUG: omits `v2 ^= 0xff` domain-separation flag before finalization rounds
    sipround(&mut v0, &mut v1, &mut v2, &mut v3);
    sipround(&mut v0, &mut v1, &mut v2, &mut v3);
    sipround(&mut v0, &mut v1, &mut v2, &mut v3);
    sipround(&mut v0, &mut v1, &mut v2, &mut v3);

    (v0 ^ v1 ^ v2 ^ v3) as i64
}
