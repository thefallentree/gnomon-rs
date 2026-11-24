#![no_std]

//! Vertical Pack 1 — AI Inference (`llama.cpp` / GGML `Q8_0` 4-Lane Block Quantization)
//!
//! Quantizes a 4-lane `f32` activation/weight block into GGML `Q8_0` format:
//! - `scale: f32 = amax / 127.0`
//! - `q: [i8; 4]` where `q_i = clamp(round_ties_even(x_i * (127.0 / amax)), -127, 127)`
//! - Guards `amax == 0.0` (and subnormal/infinite `inv_scale`) so `0.0 * Inf = NaN` NEVER occurs
//!   and an all-zero block deterministically returns `(scale = +0.0, q = [0, 0, 0, 0])`.
//!
//! Packed `i64` Wasm ABI return layout:
//! - low 32 bits  (`ret as u32`): `scale.to_bits()`
//! - high 32 bits (`(ret >> 32) as u32`): `[q0, q1, q2, q3]` packed as 4 `i8` lanes in `i32`
//!
//! Also includes a portable native pair (`q8_0_scale_scalar` vs `q8_0_scale_vec`)
//! for `gnomon profile --compare --targets x64,arm64`.

#[cfg(target_arch = "wasm32")]
use core::arch::wasm32::*;

#[cfg(target_arch = "wasm32")]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

#[cfg(target_arch = "wasm32")]
#[link(wasm_import_module = "gnomon")]
unsafe extern "C" {
    fn gnomon_assume(cond: i32);
    fn gnomon_assert(cond: i32);
}

#[cfg(target_arch = "wasm32")]
#[inline(always)]
fn assume(cond: bool) {
    unsafe {
        gnomon_assume(if cond { 1 } else { 0 });
    }
}

#[cfg(target_arch = "wasm32")]
#[inline(always)]
fn assert_prop(cond: bool) {
    unsafe {
        gnomon_assert(if cond { 1 } else { 0 });
    }
}

#[cfg(target_arch = "wasm32")]
#[inline(always)]
fn pack_i32_pair(lo: i32, hi: i32) -> i64 {
    ((((hi as u32) as u64) << 32) | ((lo as u32) as u64)) as i64
}

#[cfg(target_arch = "wasm32")]
#[inline(always)]
fn wasm_f32_max_nonneg(a: f32, b: f32) -> f32 {
    // Lowers directly to scalar Wasm `f32.max`, matching `f32x4.max` lane-for-lane.
    f32x4_extract_lane::<0>(f32x4_max(f32x4_splat(a), f32x4_splat(b)))
}

#[cfg(target_arch = "wasm32")]
#[inline(always)]
fn wasm_f32_nearest(x: f32) -> f32 {
    f32x4_extract_lane::<0>(f32x4_nearest(f32x4_splat(x)))
}

#[cfg(target_arch = "wasm32")]
#[inline(always)]
fn clamp_q8_i32(v: i32) -> i32 {
    if v > 127 {
        127
    } else if v < -127 {
        -127
    } else {
        v
    }
}

#[cfg(target_arch = "wasm32")]
#[inline(always)]
fn pack_4_i8(q0: i32, q1: i32, q2: i32, q3: i32) -> i32 {
    (q0 & 0xFF) | ((q1 & 0xFF) << 8) | ((q2 & 0xFF) << 16) | ((q3 & 0xFF) << 24)
}

// ============================================================================
// Verified Wasm Kernels (`QF_ABVFP`): Scalar Reference vs `f32x4` SIMD128
// ============================================================================

/// Scalar reference `llama.cpp` / GGML `Q8_0` 4-lane block quantization.
/// Uses explicit `max(max(a0, a1), max(a2, a3))` tree and `f32.nearest` + `i32.trunc_sat_f32_s`
/// + `[-127, 127]` clamp so it is bit-identical to `q8_0_quant_4_v128`.
#[cfg(target_arch = "wasm32")]
#[unsafe(no_mangle)]
pub extern "C" fn q8_0_quant_4_ref(x0: f32, x1: f32, x2: f32, x3: f32) -> i64 {
    let a0 = x0.abs();
    let a1 = x1.abs();
    let a2 = x2.abs();
    let a3 = x3.abs();

    let m01 = wasm_f32_max_nonneg(a0, a1);
    let m23 = wasm_f32_max_nonneg(a2, a3);
    let amax = wasm_f32_max_nonneg(m01, m23);

    // Guard amax == 0.0, NaN, +Inf, and extreme subnormals where 127.0 / amax overflows to +Inf.
    if !(amax > 0.0) {
        return 0;
    }
    let scale = amax / 127.0;
    let inv_scale = 127.0 / amax;
    if !(scale < f32::INFINITY) || !(inv_scale < f32::INFINITY) {
        return 0;
    }

    let q0 = clamp_q8_i32(wasm_f32_nearest(x0 * inv_scale) as i32);
    let q1 = clamp_q8_i32(wasm_f32_nearest(x1 * inv_scale) as i32);
    let q2 = clamp_q8_i32(wasm_f32_nearest(x2 * inv_scale) as i32);
    let q3 = clamp_q8_i32(wasm_f32_nearest(x3 * inv_scale) as i32);

    let packed_q = pack_4_i8(q0, q1, q2, q3);
    pack_i32_pair(scale.to_bits() as i32, packed_q)
}

/// Vectorized `f32x4` SIMD128 `Q8_0` 4-lane block quantization using
/// `f32x4_abs`, `f32x4_max`, `f32x4_mul`, `f32x4_nearest`, `i32x4_trunc_sat_f32x4`,
/// and `i32x4_min`/`i32x4_max` clamp to `[-127, 127]`.
/// Proved bit-for-bit equivalent to `q8_0_quant_4_ref` in Gnomon `QF_ABVFP`.
#[cfg(target_arch = "wasm32")]
#[unsafe(no_mangle)]
pub extern "C" fn q8_0_quant_4_v128(x0: f32, x1: f32, x2: f32, x3: f32) -> i64 {
    let xv = f32x4(x0, x1, x2, x3);
    let av = f32x4_abs(xv);

    let even = f32x4(
        f32x4_extract_lane::<0>(av),
        f32x4_extract_lane::<2>(av),
        0.0,
        0.0,
    );
    let odd = f32x4(
        f32x4_extract_lane::<1>(av),
        f32x4_extract_lane::<3>(av),
        0.0,
        0.0,
    );
    let pair_max = f32x4_max(even, odd);
    let m01 = f32x4_extract_lane::<0>(pair_max);
    let m23 = f32x4_extract_lane::<1>(pair_max);
    let amax = f32x4_extract_lane::<0>(f32x4_max(f32x4_splat(m01), f32x4_splat(m23)));

    if !(amax > 0.0) {
        return 0;
    }
    let scale = amax / 127.0;
    let inv_scale = 127.0 / amax;
    if !(scale < f32::INFINITY) || !(inv_scale < f32::INFINITY) {
        return 0;
    }

    let scaled = f32x4_mul(xv, f32x4_splat(inv_scale));
    let rounded = f32x4_nearest(scaled);
    let trunc = i32x4_trunc_sat_f32x4(rounded);
    let clamped = i32x4_max(i32x4_min(trunc, i32x4_splat(127)), i32x4_splat(-127));

    let q0 = i32x4_extract_lane::<0>(clamped);
    let q1 = i32x4_extract_lane::<1>(clamped);
    let q2 = i32x4_extract_lane::<2>(clamped);
    let q3 = i32x4_extract_lane::<3>(clamped);

    let packed_q = pack_4_i8(q0, q1, q2, q3);
    pack_i32_pair(scale.to_bits() as i32, packed_q)
}

/// Precondition: all 4 input activations are finite IEEE-754 `f32` values (no NaN, no ±Inf).
#[cfg(target_arch = "wasm32")]
#[unsafe(no_mangle)]
pub extern "C" fn req_finite_block(x0: f32, x1: f32, x2: f32, x3: f32) -> i32 {
    let xv = f32x4(x0, x1, x2, x3);
    let lim = f32x4_splat(f32::MAX);
    let ok = f32x4_le(f32x4_abs(xv), lim);
    if i32x4_bitmask(ok) == 0xF { 1 } else { 0 }
}

/// Postcondition proving `Q8_0` quantization safety:
/// - `scale` is finite, non-negative, not `NaN`, and not `-0.0`
/// - all 4 quantized bytes lie strictly in `[-127, 127]` (never `-128`)
/// - all-zero input block returns exact `(scale = +0.0, q = [0, 0, 0, 0])` (`ret == 0`)
#[cfg(target_arch = "wasm32")]
#[unsafe(no_mangle)]
pub extern "C" fn ens_q8_0_safe(x0: f32, x1: f32, x2: f32, x3: f32, ret: i64) -> i32 {
    let scale = f32::from_bits(ret as u32);
    let packed_q = (ret >> 32) as u32;

    if scale.is_nan() || !(scale >= 0.0) || !(scale < f32::INFINITY) || scale.to_bits() == 0x8000_0000
    {
        return 0;
    }

    let q0 = (packed_q & 0xFF) as u8 as i8;
    let q1 = ((packed_q >> 8) & 0xFF) as u8 as i8;
    let q2 = ((packed_q >> 16) & 0xFF) as u8 as i8;
    let q3 = ((packed_q >> 24) & 0xFF) as u8 as i8;

    if q0 < -127 || q1 < -127 || q2 < -127 || q3 < -127 {
        return 0;
    }

    if x0 == 0.0 && x1 == 0.0 && x2 == 0.0 && x3 == 0.0 && ret != 0 {
        return 0;
    }

    1
}

/// Inline contract verifying `req_finite_block => ens_q8_0_safe` and bit-exact equivalence
/// between `q8_0_quant_4_v128` and `q8_0_quant_4_ref`.
#[cfg(target_arch = "wasm32")]
#[unsafe(no_mangle)]
pub extern "C" fn contract_q8_0_quant_4(x0: f32, x1: f32, x2: f32, x3: f32) -> i32 {
    assume(req_finite_block(x0, x1, x2, x3) == 1);
    let r = q8_0_quant_4_ref(x0, x1, x2, x3);
    let v = q8_0_quant_4_v128(x0, x1, x2, x3);
    assert_prop(v == r);
    assert_prop(ens_q8_0_safe(x0, x1, x2, x3, v) == 1);
    1
}

// ============================================================================
// Portable Native Profile Pair (`gnomon profile --compare --targets x64,arm64`)
// ============================================================================

/// Scalar reference 4-lane `Q8_0` block quantizer with per-element branches
/// (NaN/abs/max/clamp checks in a scalar loop).
#[unsafe(no_mangle)]
pub extern "C" fn q8_0_scale_scalar(src: *const f32, dst: *mut i8) -> f32 {
    // SAFETY: Caller supplies valid 4-element `src` and `dst` buffers.
    unsafe {
        let mut amax = 0.0f32;
        let mut i = 0usize;
        while i < 4 {
            let x = *src.add(i);
            let ax = if x < 0.0 { -x } else { x };
            if ax > amax {
                amax = ax;
            }
            i += 1;
        }

        if !(amax > 0.0) {
            let mut j = 0usize;
            while j < 4 {
                *dst.add(j) = 0;
                j += 1;
            }
            return 0.0;
        }

        let scale = amax / 127.0;
        let inv_scale = 127.0 / amax;
        if scale.to_bits() >= 0x7F80_0000 || inv_scale.to_bits() >= 0x7F80_0000 {
            let mut j = 0usize;
            while j < 4 {
                *dst.add(j) = 0;
                j += 1;
            }
            return 0.0;
        }

        let mut k = 0usize;
        while k < 4 {
            let s = (*src.add(k)) * inv_scale;
            let biased = if s >= 0.0 { s + 0.5 } else { s - 0.5 };
            let mut qi = biased as i32;
            if qi > 127 {
                qi = 127;
            } else if qi < -127 {
                qi = -127;
            }
            *dst.add(k) = qi as i8;
            k += 1;
        }
        scale
    }
}

/// Vectorized branchless 4-lane `Q8_0` block quantizer (portable SIMD):
/// - Compiles on x86-64 (`skylake`) to packed SSE/AVX `vandps` + `vmaxps` + `vmulps` + `vcvttps2dq`
/// - Compiles on ARM64 (`neoverse-v2`) to NEON `fabs.4s` + `fmax.4s` + `fmul.4s` + `fcvtzs.4s`
#[unsafe(no_mangle)]
pub extern "C" fn q8_0_scale_vec(src: *const f32, dst: *mut i8) -> f32 {
    // SAFETY: Caller supplies valid 4-element `src` and `dst` buffers.
    unsafe {
        let x = [*src.add(0), *src.add(1), *src.add(2), *src.add(3)];
        let a = [x[0].abs(), x[1].abs(), x[2].abs(), x[3].abs()];
        let m01 = if a[0] >= a[1] { a[0] } else { a[1] };
        let m23 = if a[2] >= a[3] { a[2] } else { a[3] };
        let amax = if m01 >= m23 { m01 } else { m23 };

        let scale = amax / 127.0;
        let inv_scale = 127.0 / amax;
        let valid =
            (amax > 0.0) & (scale.to_bits() < 0x7F80_0000) & (inv_scale.to_bits() < 0x7F80_0000);
        let eff_scale = if valid { scale } else { 0.0 };
        let eff_inv = if valid { inv_scale } else { 0.0 };

        let mut q = [0i8; 4];
        let mut i = 0usize;
        while i < 4 {
            let s = x[i] * eff_inv;
            let half = f32::from_bits(0x3F00_0000 | (s.to_bits() & 0x8000_0000));
            let qi = ((s + half) as i32).clamp(-127, 127);
            q[i] = qi as i8;
            i += 1;
        }
        core::ptr::write_unaligned(dst as *mut [i8; 4], q);
        eff_scale
    }
}
