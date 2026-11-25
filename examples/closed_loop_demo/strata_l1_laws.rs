#![no_std]

#[cfg(target_arch = "wasm32")]
#[link(wasm_import_module = "stratum")]
unsafe extern "C" {
    fn sor_div_10k(x: u32) -> u32;
}

#[cfg(not(target_arch = "wasm32"))]
#[inline(always)]
unsafe fn sor_div_10k(x: u32) -> u32 {
    (x & 0x00FF_FFFF) / 10_000
}

/// LHS of the unconditional Layer-1 folding law `sor-div-10k-fold`:
/// Exact multiply-shift reciprocal `(((x & 0x00FF_FFFF) >> 4) * 54_975_582) >> 35`
/// (0 hardware `div` instructions).
#[unsafe(no_mangle)]
pub extern "C" fn sor_div_10k_reciprocal(x: u32) -> u32 {
    ((((x & 0x00FF_FFFF) >> 4) as u64).wrapping_mul(54_975_582) >> 35) as u32
}

/// RHS of the unconditional Layer-1 folding law `sor-div-10k-fold`:
/// Canonical Layer-1 Stratum call `stratum::sor_div_10k(x)`.
#[unsafe(no_mangle)]
pub extern "C" fn sor_div_10k_stratum(x: u32) -> u32 {
    // SAFETY: Pure total Layer-1 Stratum call.
    unsafe { sor_div_10k(x) }
}

#[cfg(target_arch = "wasm32")]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}
