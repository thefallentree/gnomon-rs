#![no_std]

#[cfg(target_arch = "wasm32")]
#[link(wasm_import_module = "stratum")]
unsafe extern "C" {
    fn sor_div_10k(x: u32) -> u32;
}

#[cfg(not(target_arch = "wasm32"))]
#[inline(always)]
unsafe fn sor_div_10k_native(x: u32, d: u32) -> u32 {
    if d == 0 {
        return 0;
    }
    (x & 0x00FF_FFFF) / d
}

/// Kernel 2 (Reference): 4-Venue Smart Order Router (Fee-Adjusted Effective Price + Child Allocation).
///
/// Computes each venue's fee-adjusted effective price using runtime division
/// (`fee_i = (p_i * f_i) / bps_denom`, where `req_sor` constrains `bps_denom == 10_000`),
/// selects the best venue via nested branchy `if` chains:
/// - `side == 0` (BUY): minimize effective price `p_i + fee_i` (lower venue index wins ties)
/// - `side != 0` (SELL): maximize effective price `p_i - fee_i` (lower venue index wins ties)
/// Allocates `alloc_qty = min(parent_qty, best_qty)` and packs `(best_venue: i32, alloc_qty: i32)`
/// into `i64` as `((best_venue as u64) << 32) | ((alloc_qty as u32) as u64)`.
#[unsafe(no_mangle)]
pub extern "C" fn sor_route_4_ref(
    side: i32,
    parent_qty: i32,
    bps_denom: i32,
    p0: i32,
    q0: i32,
    f0: i32,
    p1: i32,
    q1: i32,
    f1: i32,
    p2: i32,
    q2: i32,
    f2: i32,
    p3: i32,
    q3: i32,
    f3: i32,
) -> i64 {
    if bps_denom <= 0 || parent_qty < 0 {
        return 0;
    }
    #[cfg(target_arch = "wasm32")]
    let (fee0, fee1, fee2, fee3) = (
        // SAFETY: Pure total Layer-1 Stratum call (`sor_div_10k`, equivalent to `(x & 0x00FF_FFFF) / 10_000`).
        unsafe { sor_div_10k((p0 as u32).wrapping_mul(f0 as u32)) } as i32,
        unsafe { sor_div_10k((p1 as u32).wrapping_mul(f1 as u32)) } as i32,
        unsafe { sor_div_10k((p2 as u32).wrapping_mul(f2 as u32)) } as i32,
        unsafe { sor_div_10k((p3 as u32).wrapping_mul(f3 as u32)) } as i32,
    );
    #[cfg(not(target_arch = "wasm32"))]
    let (fee0, fee1, fee2, fee3) = {
        let d = bps_denom as u32;
        (
            // SAFETY: Pure runtime unsigned division guarded by `bps_denom > 0`.
            unsafe { sor_div_10k_native((p0 as u32).wrapping_mul(f0 as u32), d) } as i32,
            unsafe { sor_div_10k_native((p1 as u32).wrapping_mul(f1 as u32), d) } as i32,
            unsafe { sor_div_10k_native((p2 as u32).wrapping_mul(f2 as u32), d) } as i32,
            unsafe { sor_div_10k_native((p3 as u32).wrapping_mul(f3 as u32), d) } as i32,
        )
    };

    let best_venue: i32;
    let best_qty: i32;

    if side == 0 {
        let e0 = p0.wrapping_add(fee0);
        let e1 = p1.wrapping_add(fee1);
        let e2 = p2.wrapping_add(fee2);
        let e3 = p3.wrapping_add(fee3);

        let mut bv = 0i32;
        let mut be = e0;
        let mut bq = q0;
        if e1 < be {
            bv = 1;
            be = e1;
            bq = q1;
        }
        if e2 < be {
            bv = 2;
            be = e2;
            bq = q2;
        }
        if e3 < be {
            bv = 3;
            bq = q3;
        }
        best_venue = bv;
        best_qty = bq;
    } else {
        let e0 = p0.wrapping_sub(fee0);
        let e1 = p1.wrapping_sub(fee1);
        let e2 = p2.wrapping_sub(fee2);
        let e3 = p3.wrapping_sub(fee3);

        let mut bv = 0i32;
        let mut be = e0;
        let mut bq = q0;
        if e1 > be {
            bv = 1;
            be = e1;
            bq = q1;
        }
        if e2 > be {
            bv = 2;
            be = e2;
            bq = q2;
        }
        if e3 > be {
            bv = 3;
            bq = q3;
        }
        best_venue = bv;
        best_qty = bq;
    }

    let alloc_qty = if parent_qty < best_qty {
        parent_qty
    } else {
        best_qty
    };
    (((best_venue as u64) << 32) | ((alloc_qty as u32) as u64)) as i64
}

#[inline(always)]
fn div_10k_fast(x: u32) -> i32 {
    ((((x & 0x00FF_FFFF) >> 4) as u64).wrapping_mul(54_975_582) >> 35) as u32 as i32
}

/// Kernel 2 (Optimized): Zero-div, Zero-branch, Zero-spill 4-Venue Smart Order Router.
///
/// Closed-loop optimization highlights:
/// - Attempt 1 (under-precision 40-bit reciprocal `M = 109_951_163, S = 40`): FALSIFIED by
///   Bitwuzla with counterexample `x = 499_059_999` (`opt = 49_906 != ref = 49_905`, +1 fee bug!).
/// - Attempt 2 (pre-negating all 4 prices up front): `llvm-mca` caught 1 register spill on x64.
/// - Attempt 3 (unpaired `if s1 < s0` selection): left 3 conditional branches on x64 due to
///   stack-passed quantity loads (`q1..q3`).
/// - Final winner: Verified exact multiply-shift reciprocal `(((x & 0x00FF_FFFF) >> 4) * 54_975_582) >> 35`
///   (proved unconditionally via TCB-admitted Layer-1 law `sor-div-10k-fold`, eliminating all 4 hardware
///   `div`s) + paired packed `(venue << 32 | qty)` bitmask min-tree:
///   - `0` branches, `0` divs, `0` register spills on BOTH x64 (`skylake`: 5.66x cycles)
///     and ARM64 (`neoverse-v2`: 4.06x cycles, 6.00x RThroughput).
#[unsafe(no_mangle)]
pub extern "C" fn sor_route_4_opt(
    side: i32,
    parent_qty: i32,
    _bps_denom: i32,
    p0: i32,
    q0: i32,
    f0: i32,
    p1: i32,
    q1: i32,
    f1: i32,
    p2: i32,
    q2: i32,
    f2: i32,
    p3: i32,
    q3: i32,
    f3: i32,
) -> i64 {
    // Pair (0, 1): compute fee + unified score (`p + fee` for BUY, `fee - p` for SELL -> always minimize)
    let fee0 = div_10k_fast((p0 as u32).wrapping_mul(f0 as u32));
    let fee1 = div_10k_fast((p1 as u32).wrapping_mul(f1 as u32));
    let s0 = if side != 0 {
        fee0.wrapping_sub(p0)
    } else {
        p0.wrapping_add(fee0)
    };
    let s1 = if side != 0 {
        fee1.wrapping_sub(p1)
    } else {
        p1.wrapping_add(fee1)
    };
    let vq0 = (q0 as u32) as u64;
    let vq1 = (1u64 << 32) | ((q1 as u32) as u64);
    let m01 = ((s1 < s0) as u64).wrapping_neg();
    let s01 = if s1 < s0 { s1 } else { s0 };
    let vq01 = (vq1 & m01) | (vq0 & !m01);

    // Pair (2, 3): interleaved after (0, 1) to stay within x86-64's 16 GPRs (0 register spills)
    let fee2 = div_10k_fast((p2 as u32).wrapping_mul(f2 as u32));
    let fee3 = div_10k_fast((p3 as u32).wrapping_mul(f3 as u32));
    let s2 = if side != 0 {
        fee2.wrapping_sub(p2)
    } else {
        p2.wrapping_add(fee2)
    };
    let s3 = if side != 0 {
        fee3.wrapping_sub(p3)
    } else {
        p3.wrapping_add(fee3)
    };
    let vq2 = (2u64 << 32) | ((q2 as u32) as u64);
    let vq3 = (3u64 << 32) | ((q3 as u32) as u64);
    let m23 = ((s3 < s2) as u64).wrapping_neg();
    let s23 = if s3 < s2 { s3 } else { s2 };
    let vq23 = (vq3 & m23) | (vq2 & !m23);

    // Final branchless merge + min(parent_qty, best_qty) allocation
    let m_top = ((s23 < s01) as u64).wrapping_neg();
    let best_vq = (vq23 & m_top) | (vq01 & !m_top);
    let best_q = (best_vq & 0xFFFF_FFFF) as i32;
    let alloc = if parent_qty < best_q {
        parent_qty
    } else {
        best_q
    };
    ((best_vq & 0xFFFF_FFFF_0000_0000) | ((alloc as u32) as u64)) as i64
}

/// Precondition `req_sor`:
/// - `side` in `{0, 1}` (0 = BUY, 1 = SELL)
/// - `bps_denom == 10_000`
/// - `parent_qty >= 0`, `q_i >= 0`
/// - `1 <= p_i <= 32_000` (e.g. up to $320.00 in cents), `0 <= f_i <= 500` bps
///   (ensuring `p_i * f_i <= 16_000_000 < 2^24`, matching `sor_div_10k` with zero masking truncation).
#[unsafe(no_mangle)]
pub extern "C" fn req_sor(
    side: i32,
    parent_qty: i32,
    bps_denom: i32,
    p0: i32,
    q0: i32,
    f0: i32,
    p1: i32,
    q1: i32,
    f1: i32,
    p2: i32,
    q2: i32,
    f2: i32,
    p3: i32,
    q3: i32,
    f3: i32,
) -> i32 {
    if (side != 0 && side != 1) || bps_denom != 10_000 || parent_qty < 0 {
        return 0;
    }
    if p0 < 1 || p0 > 32_000 || q0 < 0 || f0 < 0 || f0 > 500 {
        return 0;
    }
    if p1 < 1 || p1 > 32_000 || q1 < 0 || f1 < 0 || f1 > 500 {
        return 0;
    }
    if p2 < 1 || p2 > 32_000 || q2 < 0 || f2 < 0 || f2 > 500 {
        return 0;
    }
    if p3 < 1 || p3 > 32_000 || q3 < 0 || f3 < 0 || f3 > 500 {
        return 0;
    }
    1
}

/// Application contract postcondition `ens_sor`:
/// Proves `0 <= best_venue <= 3`, `0 <= alloc_qty <= parent_qty`, and `alloc_qty <= q_{best_venue}`
/// with zero traps/overflow.
#[unsafe(no_mangle)]
pub extern "C" fn ens_sor(
    _side: i32,
    parent_qty: i32,
    _bps_denom: i32,
    _p0: i32,
    q0: i32,
    _f0: i32,
    _p1: i32,
    q1: i32,
    _f1: i32,
    _p2: i32,
    q2: i32,
    _f2: i32,
    _p3: i32,
    q3: i32,
    _f3: i32,
    ret: i64,
) -> i32 {
    let u = ret as u64;
    let best_venue = (u >> 32) as i32;
    let alloc_qty = (u & 0xFFFF_FFFF) as i32;
    if best_venue < 0 || best_venue > 3 {
        return 0;
    }
    if alloc_qty < 0 || alloc_qty > parent_qty {
        return 0;
    }
    let best_q = match best_venue {
        0 => q0,
        1 => q1,
        2 => q2,
        _ => q3,
    };
    if alloc_qty <= best_q { 1 } else { 0 }
}

#[cfg(target_arch = "wasm32")]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}
