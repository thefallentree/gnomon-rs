#![no_std]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

/// S1.2 Tick-Size Round-Down (pure, total, trap-free):
/// Rounds `price` down to the nearest non-negative multiple of `tick_size`.
/// Returns `0` defensively if `price < 0 || tick_size <= 0`.
#[unsafe(no_mangle)]
pub extern "C" fn tick_round_down(price: i64, tick_size: i64) -> i64 {
    if price < 0 || tick_size <= 0 {
        return 0;
    }
    let u_price = price as u64;
    let u_tick = tick_size as u64;
    let q = match u_price.checked_div(u_tick) {
        Some(q) => q,
        None => return 0,
    };
    q.wrapping_mul(u_tick) as i64
}

/// Precondition for `tick_round_down`: `price >= 0 && tick_size > 0` (full 64-bit domain).
#[unsafe(no_mangle)]
pub extern "C" fn req_tick(price: i64, tick_size: i64) -> i32 {
    if price >= 0 && tick_size > 0 { 1 } else { 0 }
}

/// Postcondition for `tick_round_down`:
/// Proves `price >= 0 && tick_size > 0 => 0 <= ret <= price && price - ret < tick_size
/// && ret == (price / tick_size) * tick_size` (which implies `ret % tick_size == 0`
/// and uniquely identifies the greatest multiple of `tick_size` <= `price`).
#[unsafe(no_mangle)]
pub extern "C" fn ens_tick(price: i64, tick_size: i64, ret: i64) -> i32 {
    if price < 0 || tick_size <= 0 {
        return if ret == 0 { 1 } else { 0 };
    }
    if ret < 0 || ret > price {
        return 0;
    }
    let u_price = price as u64;
    let u_tick = tick_size as u64;
    let u_ret = ret as u64;
    if u_price.wrapping_sub(u_ret) >= u_tick {
        return 0;
    }
    let q = match u_price.checked_div(u_tick) {
        Some(q) => q,
        None => return 0,
    };
    if u_ret == q.wrapping_mul(u_tick) {
        1
    } else {
        0
    }
}

/// Buggy mutant for `tick_round_down`:
/// Off-by-one-tick error that subtracts an extra `tick_size` whenever `price >= tick_size`
/// and `price` is already tick-aligned -> violates `price - ret < tick_size`.
#[unsafe(no_mangle)]
pub extern "C" fn tick_round_down_buggy_offbytick(price: i64, tick_size: i64) -> i64 {
    if price < 0 || tick_size <= 0 {
        return 0;
    }
    let u_price = price as u64;
    let u_tick = tick_size as u64;
    let q = match u_price.checked_div(u_tick) {
        Some(q) => q,
        None => return 0,
    };
    let rounded = q.wrapping_mul(u_tick);
    if rounded == u_price && rounded >= u_tick {
        rounded.wrapping_sub(u_tick) as i64
    } else {
        rounded as i64
    }
}

/// S1.2 Basis-Point Fee Calculation (pure, total, overflow-safe):
/// Computes exact `floor(notional * fee_bps / 10_000)` for all `0 <= notional <= i64::MAX`
/// and `0 <= fee_bps <= 10_000` with zero 64-bit overflow and zero `i128` spills.
/// Decomposition: `notional = q * 10_000 + r` (`0 <= r < 10_000`), so
/// `floor((q * 10_000 + r) * fee_bps / 10_000) == q * fee_bps + (r * fee_bps) / 10_000`.
#[unsafe(no_mangle)]
pub extern "C" fn fee_bps_calc(notional: i64, fee_bps: i64) -> i64 {
    if notional <= 0 || fee_bps <= 0 || fee_bps > 10_000 {
        return 0;
    }
    if fee_bps == 10_000 {
        return notional;
    }
    let u_notional = notional as u64;
    let u_bps = fee_bps as u64;
    let q = u_notional / 10_000;
    let r = u_notional % 10_000;
    q.wrapping_mul(u_bps)
        .wrapping_add(r.wrapping_mul(u_bps) / 10_000) as i64
}

/// Precondition for `fee_bps_calc`: full 64-bit `notional >= 0` and `0 <= fee_bps <= 10_000`.
#[unsafe(no_mangle)]
pub extern "C" fn req_fee(notional: i64, fee_bps: i64) -> i32 {
    if notional >= 0 && fee_bps >= 0 && fee_bps <= 10_000 {
        1
    } else {
        0
    }
}

/// Relational postcondition for `fee_bps_calc`:
/// Proves zero signed 64-bit overflow (`ret >= 0`), boundary identities
/// (`notional == 0 || fee_bps == 0 => ret == 0`, `fee_bps == 10_000 => ret == notional`),
/// and exact overflow-free basis-point floor division across the entire 64-bit `notional` domain.
#[unsafe(no_mangle)]
pub extern "C" fn ens_fee(notional: i64, fee_bps: i64, ret: i64) -> i32 {
    if notional < 0 || fee_bps < 0 || fee_bps > 10_000 {
        return if ret == 0 { 1 } else { 0 };
    }
    if ret < 0 {
        return 0;
    }
    if notional == 0 || fee_bps == 0 {
        return if ret == 0 { 1 } else { 0 };
    }
    if fee_bps == 10_000 {
        return if ret == notional { 1 } else { 0 };
    }
    let u_notional = notional as u64;
    let u_bps = fee_bps as u64;
    let q = u_notional / 10_000;
    let r = u_notional % 10_000;
    let expected = q
        .wrapping_mul(u_bps)
        .wrapping_add(r.wrapping_mul(u_bps) / 10_000);
    if (ret as u64) == expected { 1 } else { 0 }
}

/// Buggy mutant for `fee_bps_calc`:
/// Naive `(notional * fee_bps) / 10_000` wraps negative on large notionals
/// (`notional > i64::MAX / fee_bps`), violating both `ret >= 0` and exact fee semantics.
#[unsafe(no_mangle)]
pub extern "C" fn fee_bps_calc_buggy_overflow(notional: i64, fee_bps: i64) -> i64 {
    if notional <= 0 || fee_bps <= 0 || fee_bps > 10_000 {
        return 0;
    }
    notional.wrapping_mul(fee_bps) / 10_000
}

/// S1.2 Barrett Multiply-Shift Fastmod for `u32` bucket indexing (pure, division-free):
/// Given precomputed reciprocal `magic = floor(2^32 / denom)` (for `denom != 0`),
/// computes exact `(key as u32) % (denom as u32)` with zero hardware division:
///   `q_est = ((key as u64) * (magic as u64)) >> 32`   (satisfies `q_true - 1 <= q_est <= q_true`)
///   `rem_est = key - q_est * denom`                   (satisfies `0 <= rem_est < 2 * denom`)
///   `rem = if rem_est >= denom { rem_est - denom } else { rem_est }`
#[unsafe(no_mangle)]
pub extern "C" fn bucket_index_barrett_u32(key: i32, denom: i32, magic: i64) -> i32 {
    let u_key = key as u32 as u64;
    let u_denom = denom as u32 as u64;
    if u_denom == 0 {
        return 0;
    }
    let u_magic = magic as u64;
    let q_est = u_key.wrapping_mul(u_magic) >> 32;
    let rem_est = u_key.wrapping_sub(q_est.wrapping_mul(u_denom));
    let rem = if rem_est >= u_denom {
        rem_est.wrapping_sub(u_denom)
    } else {
        rem_est
    };
    (rem as u32) as i32
}

/// Exact Barrett `magic` precondition over non-power-of-2 prime OMS shard counts
/// `denom in {3, 7, 13, 31}` with `magic == floor(2^32 / denom)` and `key in 0..=4095`,
/// enabling sub-4s Bitwuzla QF_BV equivalence proof against hardware `(key as u32) % (denom as u32)`.
#[unsafe(no_mangle)]
pub extern "C" fn req_barrett(key: i32, denom: i32, magic: i64) -> i32 {
    if (key as u32) > 0x0FFF {
        return 0;
    }
    let d = denom as u32 as u64;
    let m = magic as u64;
    if (d == 3 && m == ((1u64 << 32) / 3))
        || (d == 7 && m == ((1u64 << 32) / 7))
        || (d == 13 && m == ((1u64 << 32) / 13))
        || (d == 31 && m == ((1u64 << 32) / 31))
    {
        1
    } else {
        0
    }
}

/// Exact Barrett `magic` precondition over power-of-2 bucket counts `denom in {8, 16, 64, 256}`
/// across the FULL unconstrained 32-bit `key` domain (proves in < 1s).
#[unsafe(no_mangle)]
pub extern "C" fn req_barrett_pow2(_key: i32, denom: i32, magic: i64) -> i32 {
    let d = denom as u32 as u64;
    let m = magic as u64;
    if (d == 8 && m == ((1u64 << 32) / 8))
        || (d == 16 && m == ((1u64 << 32) / 16))
        || (d == 64 && m == ((1u64 << 32) / 64))
        || (d == 256 && m == ((1u64 << 32) / 256))
    {
        1
    } else {
        0
    }
}

/// Relational postcondition for `bucket_index_barrett_u32`:
/// Proves exact equivalence `(ret as u32) == (key as u32) % (denom as u32)` and `(ret as u32) < (denom as u32)`.
#[unsafe(no_mangle)]
pub extern "C" fn ens_barrett(key: i32, denom: i32, _magic: i64, ret: i32) -> i32 {
    let u_denom = denom as u32;
    if u_denom == 0 {
        return if ret == 0 { 1 } else { 0 };
    }
    let u_key = key as u32;
    let u_ret = ret as u32;
    let expected = match u_key.checked_rem(u_denom) {
        Some(r) => r,
        None => return 0,
    };
    if u_ret < u_denom && u_ret == expected {
        1
    } else {
        0
    }
}

/// Buggy mutant for `bucket_index_barrett_u32`:
/// Omits the conditional Barrett remainder correction (`if rem_est >= denom`),
/// producing an off-by-one quotient underestimate (`rem_est == denom + true_rem >= denom`).
#[unsafe(no_mangle)]
pub extern "C" fn bucket_index_barrett_buggy_offbyone(key: i32, denom: i32, magic: i64) -> i32 {
    let u_key = key as u32 as u64;
    let u_denom = denom as u32 as u64;
    if u_denom == 0 {
        return 0;
    }
    let u_magic = magic as u64;
    let q_est = u_key.wrapping_mul(u_magic) >> 32;
    let rem_est = u_key.wrapping_sub(q_est.wrapping_mul(u_denom));
    (rem_est as u32) as i32
}
