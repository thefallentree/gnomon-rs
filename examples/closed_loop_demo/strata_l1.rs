#![no_std]

/// Layer-1 Stratum primitive for Kernel 2 (SOR fee division):
/// Exact unsigned integer division by `10_000` over the 24-bit masked domain (`0..=16_777_215`),
/// which covers all `price * fee_bps` for `1 <= price <= 32_000` and `0 <= fee_bps <= 500`.
#[unsafe(no_mangle)]
pub extern "C" fn sor_div_10k(x: u32) -> u32 {
    (x & 0x00FF_FFFF) / 10_000
}

/// Layer-1 Stratum primitive for Kernel 3 (notional cap gate):
/// Returns `1` iff `aligned * qty <= max_notional` (overflow-free under `req_tick_risk`
/// where `1 <= aligned <= 1_000_000_000` and `1 <= qty <= 1_000_000_000`).
#[unsafe(no_mangle)]
pub extern "C" fn notional_le(aligned: i64, qty: i64, max_notional: i64) -> i32 {
    if aligned.wrapping_mul(qty) <= max_notional {
        1
    } else {
        0
    }
}

/// Layer-1 Stratum primitive for Kernel 3 (BPS price collar gate):
/// Returns `1` iff `|aligned - ref_price| * 10_000 <= ref_price * collar_bps`
/// (overflow-free under `req_tick_risk` where `1 <= price, ref_price <= 1_000_000_000`
/// and `0 <= collar_bps <= 10_000`).
#[unsafe(no_mangle)]
pub extern "C" fn collar_le(aligned: i64, ref_price: i64, collar_bps: i64) -> i32 {
    let diff = if aligned >= ref_price {
        aligned.wrapping_sub(ref_price)
    } else {
        ref_price.wrapping_sub(aligned)
    };
    if diff.wrapping_mul(10_000) <= ref_price.wrapping_mul(collar_bps) {
        1
    } else {
        0
    }
}

#[cfg(target_arch = "wasm32")]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}
