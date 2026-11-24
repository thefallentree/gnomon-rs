#![no_std]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

const FMIX64_C1: u64 = 0xff51_afd7_ed55_8ccd;
const FMIX64_C2: u64 = 0xc4ce_b9fe_1a85_ec53;
// Exact modular inverses modulo 2^64:
//   FMIX64_C1.wrapping_mul(FMIX64_INV1) == 1
//   FMIX64_C2.wrapping_mul(FMIX64_INV2) == 1
const FMIX64_INV1: u64 = 0x4f74_430c_22a5_4005;
const FMIX64_INV2: u64 = 0x9cb4_b2f8_1293_37db;

/// S1.3 Bijective 64-bit MurmurHash3 `fmix64` order-ID mixer (pure, total, zero memory).
/// Exported as function 0 so `gnomon define-op --name order_id_mix` registers it directly
/// as a Layer-1 Stratum for `S2.2` (`s2_2_order_slab_table`) and UF CEGAR composition.
#[unsafe(no_mangle)]
pub extern "C" fn order_id_mix(x: i64) -> i64 {
    let mut z = x as u64;
    z ^= z >> 33;
    z = z.wrapping_mul(FMIX64_C1);
    z ^= z >> 33;
    z = z.wrapping_mul(FMIX64_C2);
    z ^= z >> 33;
    z as i64
}

/// Exact inverse of `order_id_mix` over all 2^64 values (pure, total, zero memory).
/// Since `z ^= z >> 33` is self-inverse (`2 * 33 >= 64`) and both odd multipliers are
/// invertible modulo `2^64`, `order_id_unmix(order_id_mix(x)) == x` and
/// `order_id_mix(order_id_unmix(y)) == y` hold for every `i64`.
#[unsafe(no_mangle)]
pub extern "C" fn order_id_unmix(y: i64) -> i64 {
    let mut z = y as u64;
    z ^= z >> 33;
    z = z.wrapping_mul(FMIX64_INV2);
    z ^= z >> 33;
    z = z.wrapping_mul(FMIX64_INV1);
    z ^= z >> 33;
    z as i64
}

/// Bijection round-trip helper: `order_id_unmix(order_id_mix(x))` (equals `x` for all `i64`).
#[unsafe(no_mangle)]
pub extern "C" fn order_id_roundtrip(x: i64) -> i64 {
    order_id_unmix(order_id_mix(x))
}

/// Identity postcondition (`ret == x`) for verifying bijective round-trip.
#[unsafe(no_mangle)]
pub extern "C" fn post_identity_i64(x: i64, ret: i64) -> i32 {
    if ret == x { 1 } else { 0 }
}
