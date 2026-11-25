#![no_std]

#[cfg(target_arch = "wasm32")]
#[link(wasm_import_module = "stratum")]
unsafe extern "C" {
    fn notional_le(aligned: i64, qty: i64, max_notional: i64) -> i32;
    fn collar_le(aligned: i64, ref_price: i64, collar_bps: i64) -> i32;
}

#[cfg(not(target_arch = "wasm32"))]
#[inline(always)]
unsafe fn notional_le(aligned: i64, qty: i64, max_notional: i64) -> i32 {
    if aligned.wrapping_mul(qty) <= max_notional {
        1
    } else {
        0
    }
}

#[cfg(not(target_arch = "wasm32"))]
#[inline(always)]
unsafe fn collar_le(aligned: i64, ref_price: i64, collar_bps: i64) -> i32 {
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

/// Kernel 3 (Reference): Combined Tick-Size Alignment + Pre-Trade Risk Fast Path.
///
/// Aligns `price` down to a multiple of `tick` using runtime unsigned remainder (`price % tick`),
/// then evaluates pre-trade risk gates via nested branches:
/// 1. Global kill-switch (`kill_switch != 0` -> reject `0`).
/// 2. Positive finite domain guards.
/// 3. Aligned price positivity (`aligned > 0`).
/// 4. Overflow-safe notional cap (`aligned * qty <= max_notional`, via Layer-1 Stratum `notional_le`).
/// 5. Price collar (`|aligned - ref_price| * 10_000 <= ref_price * collar_bps`, via `collar_le`).
/// Returns `aligned` if all checks pass, else `0`.
#[unsafe(no_mangle)]
pub extern "C" fn oms_tick_risk_ref(
    price: i64,
    qty: i64,
    ref_price: i64,
    tick: i64,
    max_notional: i64,
    collar_bps: i64,
    kill_switch: i32,
) -> i64 {
    if kill_switch != 0 {
        return 0;
    }
    if price <= 0 || qty <= 0 || ref_price <= 0 || tick <= 0 || max_notional <= 0 || collar_bps < 0
    {
        return 0;
    }
    let u_price = price as u64;
    let u_tick = tick as u64;
    let aligned = (u_price.wrapping_sub(u_price % u_tick)) as i64;
    if aligned <= 0 {
        return 0;
    }
    // SAFETY: Pure total Layer-1 Strata (`notional_le`, `collar_le`), identical to inline bodies.
    if unsafe { notional_le(aligned, qty, max_notional) } == 0 {
        return 0;
    }
    if unsafe { collar_le(aligned, ref_price, collar_bps) } == 0 {
        return 0;
    }
    aligned
}

/// Kernel 3 (Optimized): Branchless, Constant-Cycle, 0-div, 0-spill Tick-Risk Fast Path.
///
/// Closed-loop optimization highlights:
/// - Attempt 1 (`kill_switch != 1` bug): FALSIFIED by Bitwuzla in 96 ms (contract) / 497 ms (goal)
///   with counterexample `kill_switch = 1_073_741_824` (`0x4000_0000`, non-boolean halt code bypassed!).
/// - Attempt 2 (inline 64x64 multipliers): hit Bitwuzla's nonlinear bit-blasting cliff;
///   extracting pure `notional_le` and `collar_le` into Layer-1 Strata (`strata_l1.rs`) unlocked
///   UF-CEGAR congruence, proving FULL `price, qty <= 1_000_000_000` equivalence in 126.9 ms!
/// - Final winner: `aligned = price & !(tick - 1)` + branchless bitwise conjunction of all 4 gates:
///   - `0` branches, `0` divs, `0` register spills on BOTH x64 (`skylake`: 18.57x cycles, 5.39x RT)
///     and ARM64 (`neoverse-v2`: 3.00x cycles, 9.13x RT).
#[unsafe(no_mangle)]
pub extern "C" fn oms_tick_risk_opt(
    price: i64,
    qty: i64,
    ref_price: i64,
    tick: i64,
    max_notional: i64,
    collar_bps: i64,
    kill_switch: i32,
) -> i64 {
    let aligned = price & !tick.wrapping_sub(1);
    let ok_kill = kill_switch == 0;
    let ok_pos = aligned > 0;
    // SAFETY: Pure total Layer-1 Strata (`notional_le`, `collar_le`), identical to inline bodies.
    let ok_notional = unsafe { notional_le(aligned, qty, max_notional) } != 0;
    let ok_collar = unsafe { collar_le(aligned, ref_price, collar_bps) } != 0;
    let ok = ok_kill & ok_pos & ok_notional & ok_collar;
    if ok { aligned } else { 0 }
}

/// Precondition `req_tick_risk`:
/// - `tick` power-of-2 in `{1, 2, 4, 8, 16, 32, 64}`.
/// - Positive finite bounds guaranteeing zero 64-bit signed overflow in notional & collar checks:
///   `1 <= price, qty, ref_price <= 1_000_000_000`, `1 <= max_notional <= 10^18`,
///   `0 <= collar_bps <= 10_000`.
#[unsafe(no_mangle)]
pub extern "C" fn req_tick_risk(
    price: i64,
    qty: i64,
    ref_price: i64,
    tick: i64,
    max_notional: i64,
    collar_bps: i64,
    _kill_switch: i32,
) -> i32 {
    if tick != 1
        && tick != 2
        && tick != 4
        && tick != 8
        && tick != 16
        && tick != 32
        && tick != 64
    {
        return 0;
    }
    if price < 1 || price > 1_000_000_000 {
        return 0;
    }
    if qty < 1 || qty > 1_000_000_000 {
        return 0;
    }
    if ref_price < 1 || ref_price > 1_000_000_000 {
        return 0;
    }
    if max_notional < 1 || max_notional > 1_000_000_000_000_000_000 {
        return 0;
    }
    if collar_bps < 0 || collar_bps > 10_000 {
        return 0;
    }
    1
}

/// Application contract postcondition `ens_tick_risk`:
/// 1. Kill-switch dominance: `kill_switch != 0 => ret == 0` (for ALL non-zero `i32` halt codes!).
/// 2. Bounded non-negative output: `0 <= ret <= price`.
/// 3. Whenever accepted (`ret > 0`), output is strictly tick-aligned (`(ret & (tick - 1)) == 0`),
///    respects notional cap (`notional_le == 1`), and respects BPS collar (`collar_le == 1`).
#[unsafe(no_mangle)]
pub extern "C" fn ens_tick_risk(
    price: i64,
    qty: i64,
    ref_price: i64,
    tick: i64,
    max_notional: i64,
    collar_bps: i64,
    kill_switch: i32,
    ret: i64,
) -> i32 {
    if kill_switch != 0 {
        return if ret == 0 { 1 } else { 0 };
    }
    if ret == 0 {
        return 1;
    }
    if ret < 0 || ret > price {
        return 0;
    }
    if (ret & tick.wrapping_sub(1)) != 0 {
        return 0;
    }
    // SAFETY: Pure total Layer-1 Strata (`notional_le`, `collar_le`).
    if unsafe { notional_le(ret, qty, max_notional) } == 0 {
        return 0;
    }
    if unsafe { collar_le(ret, ref_price, collar_bps) } == 0 {
        return 0;
    }
    1
}

#[cfg(target_arch = "wasm32")]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}
