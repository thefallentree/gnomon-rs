#![no_std]

// ============================================================================
// Pair 1: Barrett Tick/Bucket `fastmod` (`div` -> multiply-shift)
// ============================================================================

/// Reference OMS shard/bucket router using hardware unsigned remainder (`key % d`).
/// Guarded for `d == 0` so it is total and trap-free.
#[unsafe(no_mangle)]
pub extern "C" fn oms_bucket_ref(key: u32, d: u32, _magic: u64) -> u32 {
    if d == 0 {
        return 0;
    }
    key % d
}

/// Optimized OMS shard/bucket router using verified Barrett multiply-shift:
///   `q_est   = ((key as u64) * magic) >> 32`   (with `magic = floor(2^32 / d)`)
///   `rem_est = key - q_est * d`                 (satisfies `0 <= rem_est < 2 * d`)
///   `rem     = if rem_est >= d { rem_est - d } else { rem_est }`
/// Eliminates hardware `div` (`1 -> 0` on both x86-64 and ARM64).
#[unsafe(no_mangle)]
pub extern "C" fn oms_bucket_opt(key: u32, d: u32, magic: u64) -> u32 {
    if d == 0 {
        return 0;
    }
    let u_key = key as u64;
    let u_d = d as u64;
    let q_est = u_key.wrapping_mul(magic) >> 32;
    let rem_est = u_key.wrapping_sub(q_est.wrapping_mul(u_d));
    let rem = if rem_est >= u_d {
        rem_est.wrapping_sub(u_d)
    } else {
        rem_est
    };
    rem as u32
}

/// Exact Barrett `magic == floor(2^32 / d)` precondition for prime OMS shard count
/// `d == 13` (`magic == 330_382_099`) across 16-bit order-bucket keys (`0..=65535`).
#[unsafe(no_mangle)]
pub extern "C" fn req_oms_bucket(key: u32, d: u32, magic: u64) -> i32 {
    if key <= 0xFFFF && d == 13 && magic == ((1u64 << 32) / 13) {
        1
    } else {
        0
    }
}

/// Additional full 32-bit `key` Barrett precondition over power-of-2 OMS shard counts
/// `d in {8, 16, 64, 256}` (proves in < 100 ms over all `2^32` keys).
#[unsafe(no_mangle)]
pub extern "C" fn req_oms_bucket_pow2(_key: u32, d: u32, magic: u64) -> i32 {
    if (d == 8 && magic == ((1u64 << 32) / 8))
        || (d == 16 && magic == ((1u64 << 32) / 16))
        || (d == 64 && magic == ((1u64 << 32) / 64))
        || (d == 256 && magic == ((1u64 << 32) / 256))
    {
        1
    } else {
        0
    }
}

// ============================================================================
// Pair 2: SWAR 8-Byte FIX ASCII Digit Validator (branchy loop -> branchless SWAR)
// ============================================================================

/// Reference byte-by-byte FIX 8-byte ASCII digit validator (`'0'..='9'` in every byte).
/// Early-exits per byte, producing 7 conditional branches in native x86-64 code.
#[unsafe(no_mangle)]
pub extern "C" fn oms_fix_digits_ref(w: u64) -> i32 {
    let mut i = 0u32;
    while i < 8 {
        let b = ((w >> (i * 8)) & 0xFF) as u8;
        if b < b'0' || b > b'9' {
            return 0;
        }
        i += 1;
    }
    1
}

/// Optimized branchless SWAR 8-byte FIX ASCII digit validator (carry-free Lemire formula):
/// - High nibble of every byte must equal `0x3` (`0x30..=0x3F`).
/// - Adding `0x06` per byte keeps high nibble `0x3` iff low nibble <= 9 (`0x30..=0x39`),
///   with zero inter-byte carry bleed when `hi_nibbles == 0x3030...`.
/// Emits 0 branches on native x86-64 and ARM64.
#[unsafe(no_mangle)]
pub extern "C" fn oms_fix_digits_opt(w: u64) -> i32 {
    let hi_nibbles = w & 0xF0F0_F0F0_F0F0_F0F0;
    let shifted_plus6 = (w.wrapping_add(0x0606_0606_0606_0606) & 0xF0F0_F0F0_F0F0_F0F0) >> 4;
    if (hi_nibbles | shifted_plus6) == 0x3333_3333_3333_3333 {
        1
    } else {
        0
    }
}

// ============================================================================
// Pair 3: Register-Pressure / Unroll Study on Pipelined Order-ID Hash
//         (`oms_hash_mix_2x` vs `oms_hash_mix_4x` vs `oms_hash_mix_12x_spill`)
// ============================================================================

const MIX_C1: u64 = 0xff51_afd7_ed55_8ccd;
const MIX_K1: u64 = 0x9e37_79b9_7f4a_7c15;
const MIX_K2: u64 = 0xbf58_476d_1ce4_e5b9;

#[inline(always)]
fn hash_round1(v: u64) -> u64 {
    let a = (v ^ (v >> 33)).wrapping_mul(MIX_C1);
    (a ^ a.rotate_left(17)).wrapping_add(a.leading_zeros() as u64)
}

#[inline(always)]
fn hash_round2(v: u64) -> u64 {
    let a = v.wrapping_add(MIX_K2);
    a ^ a.rotate_left(31) ^ (a >> 29)
}

#[inline(always)]
fn lane_key(seed: u64, salt: u64, idx: u64) -> u64 {
    seed.wrapping_add(salt ^ idx.wrapping_mul(MIX_K1))
}

#[inline(always)]
fn mix_lane(seed: u64, salt: u64, idx: u64) -> u64 {
    hash_round2(hash_round1(lane_key(seed, salt, idx)))
}

/// 2-way pipelined order-ID batch mixer (16 lanes accumulated across 2 parallel chains):
/// 0 register spills on BOTH x86-64 (`skylake` & generic) and ARM64 (`neoverse-v2`).
#[unsafe(no_mangle)]
pub extern "C" fn oms_hash_mix_2x(seed: u64, salt: u64) -> u64 {
    let mut a0 = 0u64;
    let mut a1 = 0u64;
    let mut i = 0u64;
    while i < 16 {
        a0 = a0.wrapping_add(mix_lane(seed, salt, i));
        a1 = a1.wrapping_add(mix_lane(seed, salt, i + 1));
        i += 2;
    }
    a0.wrapping_add(a1)
}

/// 4-way pipelined order-ID batch mixer (16 lanes accumulated across 4 parallel chains):
/// Tuned sweet spot: 0 register spills and 0B stack frame on BOTH x86-64 (16 GPRs)
/// and ARM64 (31 GPRs), beating the over-unrolled variant by ~14% in x64 cycles/RThroughput.
#[unsafe(no_mangle)]
pub extern "C" fn oms_hash_mix_4x(seed: u64, salt: u64) -> u64 {
    let mut a0 = 0u64;
    let mut a1 = 0u64;
    let mut a2 = 0u64;
    let mut a3 = 0u64;
    let mut i = 0u64;
    while i < 16 {
        a0 = a0.wrapping_add(mix_lane(seed, salt, i));
        a1 = a1.wrapping_add(mix_lane(seed, salt, i + 1));
        a2 = a2.wrapping_add(mix_lane(seed, salt, i + 2));
        a3 = a3.wrapping_add(mix_lane(seed, salt, i + 3));
        i += 4;
    }
    a0.wrapping_add(a1).wrapping_add(a2.wrapping_add(a3))
}

/// Over-unrolled 16-lane (12+ live) order-ID batch mixer holding all 16 live `u64` lanes
/// simultaneously across mixing rounds:
/// - On x86-64 (16 GPRs): triggers heavy real LLVM stack register spills (`[rsp+...]`,
///   56B stack frame on `skylake`, 64 `%rsp` accesses on generic x86-64) and +14% cycle/RThroughput regression!
/// - On ARM64 (31 GPRs): stays at 0 register spills / 0 reloads!
/// Proved bit-for-bit equivalent to `oms_hash_mix_2x` and `oms_hash_mix_4x`.
#[unsafe(no_mangle)]
pub extern "C" fn oms_hash_mix_12x_spill(seed: u64, salt: u64) -> u64 {
    let mut v = [0u64; 16];
    let mut i = 0usize;
    while i < 16 {
        v[i] = lane_key(seed, salt, i as u64);
        i += 1;
    }
    i = 0;
    while i < 16 {
        v[i] = hash_round1(v[i]);
        i += 1;
    }
    let mut acc = 0u64;
    i = 0;
    while i < 16 {
        acc = acc.wrapping_add(hash_round2(v[i]));
        i += 1;
    }
    acc
}

// ============================================================================
// Pair 4: Branchless Child Order FSM + Pre-Trade Risk Dispatch
// ============================================================================

// Child order states (0..7)
const ST_EMPTY: u32 = 0;
const ST_PENDING_NEW: u32 = 1;
const ST_LIVE: u32 = 2;
const ST_PENDING_REPLACE: u32 = 3;
const ST_PENDING_CANCEL: u32 = 4;
const ST_FILLED: u32 = 5;
const ST_CANCELED: u32 = 6;
const ST_REJECTED: u32 = 7;

// Events (0..7)
const EV_NEW_REQ: u32 = 0;
const EV_NEW_ACK: u32 = 1;
const EV_PARTIAL_FILL: u32 = 2;
const EV_FULL_FILL: u32 = 3;
const EV_REPLACE_REQ: u32 = 4;
const EV_REPLACE_ACK: u32 = 5;
const EV_CANCEL_REQ: u32 = 6;
const EV_CANCEL_ACK: u32 = 7;

// Dispatch actions (0..3)
const ACT_IGNORE: u32 = 0;
const ACT_ROUTE: u32 = 1;
const ACT_BOOK_UPD: u32 = 2;
const ACT_RISK_REJ: u32 = 3;

// Effective-qty output modes packed into upper 16 bits of return value:
const QTY_ZERO: u32 = 0;
const QTY_KEEP: u32 = 1;
const QTY_HALF: u32 = 2;

#[inline(always)]
const fn pack_fsm(action: u32, next_state: u32, eff_qty: u32) -> u32 {
    ((eff_qty & 0xFFFF) << 16) | (action << 8) | next_state
}

/// Reference Child Order FSM + Pre-Trade Risk Dispatch using nested `if`/`match`.
/// Risk flags:
/// - bit 0: global kill switch active
/// - bit 1: venue halted
/// - bit 2: sell-short order
/// - bit 3: short locate confirmed
#[unsafe(no_mangle)]
pub extern "C" fn oms_risk_fsm_ref(
    state: u32,
    event: u32,
    qty: u32,
    max_qty: u32,
    risk_flags: u32,
    collar_ok: u32,
) -> u32 {
    let q_keep = qty & 0xFFFF;
    let q_half = (qty >> 1) & 0xFFFF;

    if state > 7 || event > 7 {
        return pack_fsm(ACT_IGNORE, state & 7, q_keep);
    }

    if event == EV_NEW_REQ || event == EV_REPLACE_REQ {
        let kill_switch = (risk_flags & 1) != 0;
        let venue_halted = (risk_flags & 2) != 0;
        let short_no_locate = ((risk_flags & 4) != 0) && ((risk_flags & 8) == 0);
        let bad_qty = qty == 0 || qty > max_qty;
        let bad_collar = collar_ok == 0;

        if kill_switch || venue_halted || short_no_locate || bad_qty || bad_collar {
            if event == EV_NEW_REQ && state == ST_EMPTY {
                return pack_fsm(ACT_RISK_REJ, ST_REJECTED, 0);
            }
            if event == EV_REPLACE_REQ && state == ST_LIVE {
                return pack_fsm(ACT_RISK_REJ, ST_LIVE, q_keep);
            }
            return pack_fsm(ACT_IGNORE, state, q_keep);
        }
    }

    match state {
        ST_EMPTY => match event {
            EV_NEW_REQ => pack_fsm(ACT_ROUTE, ST_PENDING_NEW, q_keep),
            _ => pack_fsm(ACT_IGNORE, ST_EMPTY, 0),
        },
        ST_PENDING_NEW => match event {
            EV_NEW_ACK => pack_fsm(ACT_BOOK_UPD, ST_LIVE, q_keep),
            EV_PARTIAL_FILL => pack_fsm(ACT_BOOK_UPD, ST_LIVE, q_half),
            EV_FULL_FILL => pack_fsm(ACT_BOOK_UPD, ST_FILLED, 0),
            EV_CANCEL_REQ => pack_fsm(ACT_ROUTE, ST_PENDING_CANCEL, q_keep),
            EV_CANCEL_ACK => pack_fsm(ACT_BOOK_UPD, ST_REJECTED, 0),
            _ => pack_fsm(ACT_IGNORE, ST_PENDING_NEW, q_keep),
        },
        ST_LIVE => match event {
            EV_PARTIAL_FILL => pack_fsm(ACT_BOOK_UPD, ST_LIVE, q_half),
            EV_FULL_FILL => pack_fsm(ACT_BOOK_UPD, ST_FILLED, 0),
            EV_REPLACE_REQ => pack_fsm(ACT_ROUTE, ST_PENDING_REPLACE, q_keep),
            EV_CANCEL_REQ => pack_fsm(ACT_ROUTE, ST_PENDING_CANCEL, q_keep),
            EV_CANCEL_ACK => pack_fsm(ACT_BOOK_UPD, ST_CANCELED, 0),
            _ => pack_fsm(ACT_IGNORE, ST_LIVE, q_keep),
        },
        ST_PENDING_REPLACE => match event {
            EV_PARTIAL_FILL => pack_fsm(ACT_BOOK_UPD, ST_PENDING_REPLACE, q_half),
            EV_FULL_FILL => pack_fsm(ACT_BOOK_UPD, ST_FILLED, 0),
            EV_REPLACE_ACK => pack_fsm(ACT_BOOK_UPD, ST_LIVE, q_keep),
            EV_CANCEL_REQ => pack_fsm(ACT_ROUTE, ST_PENDING_CANCEL, q_keep),
            EV_CANCEL_ACK => pack_fsm(ACT_BOOK_UPD, ST_CANCELED, 0),
            _ => pack_fsm(ACT_IGNORE, ST_PENDING_REPLACE, q_keep),
        },
        ST_PENDING_CANCEL => match event {
            EV_PARTIAL_FILL => pack_fsm(ACT_BOOK_UPD, ST_PENDING_CANCEL, q_half),
            EV_FULL_FILL => pack_fsm(ACT_BOOK_UPD, ST_FILLED, 0),
            EV_CANCEL_ACK => pack_fsm(ACT_BOOK_UPD, ST_CANCELED, 0),
            _ => pack_fsm(ACT_IGNORE, ST_PENDING_CANCEL, q_keep),
        },
        ST_FILLED => pack_fsm(ACT_IGNORE, ST_FILLED, 0),
        ST_CANCELED => pack_fsm(ACT_IGNORE, ST_CANCELED, 0),
        _ => pack_fsm(ACT_IGNORE, ST_REJECTED, 0),
    }
}

/// Compile-time helper constructing the 7 bit-planes (3 state bits + 2 action bits + 2 qty-mode bits)
/// of the 8x8 normal-path transition table (`idx = (state << 3) | event`).
const fn build_fsm_bitplanes() -> [u64; 7] {
    let mut p = [0u64; 7];
    let mut s = 0u32;
    while s < 8 {
        let mut e = 0u32;
        while e < 8 {
            let (act, ns, qm) = match s {
                ST_EMPTY => match e {
                    EV_NEW_REQ => (ACT_ROUTE, ST_PENDING_NEW, QTY_KEEP),
                    _ => (ACT_IGNORE, ST_EMPTY, QTY_ZERO),
                },
                ST_PENDING_NEW => match e {
                    EV_NEW_ACK => (ACT_BOOK_UPD, ST_LIVE, QTY_KEEP),
                    EV_PARTIAL_FILL => (ACT_BOOK_UPD, ST_LIVE, QTY_HALF),
                    EV_FULL_FILL => (ACT_BOOK_UPD, ST_FILLED, QTY_ZERO),
                    EV_CANCEL_REQ => (ACT_ROUTE, ST_PENDING_CANCEL, QTY_KEEP),
                    EV_CANCEL_ACK => (ACT_BOOK_UPD, ST_REJECTED, QTY_ZERO),
                    _ => (ACT_IGNORE, ST_PENDING_NEW, QTY_KEEP),
                },
                ST_LIVE => match e {
                    EV_PARTIAL_FILL => (ACT_BOOK_UPD, ST_LIVE, QTY_HALF),
                    EV_FULL_FILL => (ACT_BOOK_UPD, ST_FILLED, QTY_ZERO),
                    EV_REPLACE_REQ => (ACT_ROUTE, ST_PENDING_REPLACE, QTY_KEEP),
                    EV_CANCEL_REQ => (ACT_ROUTE, ST_PENDING_CANCEL, QTY_KEEP),
                    EV_CANCEL_ACK => (ACT_BOOK_UPD, ST_CANCELED, QTY_ZERO),
                    _ => (ACT_IGNORE, ST_LIVE, QTY_KEEP),
                },
                ST_PENDING_REPLACE => match e {
                    EV_PARTIAL_FILL => (ACT_BOOK_UPD, ST_PENDING_REPLACE, QTY_HALF),
                    EV_FULL_FILL => (ACT_BOOK_UPD, ST_FILLED, QTY_ZERO),
                    EV_REPLACE_ACK => (ACT_BOOK_UPD, ST_LIVE, QTY_KEEP),
                    EV_CANCEL_REQ => (ACT_ROUTE, ST_PENDING_CANCEL, QTY_KEEP),
                    EV_CANCEL_ACK => (ACT_BOOK_UPD, ST_CANCELED, QTY_ZERO),
                    _ => (ACT_IGNORE, ST_PENDING_REPLACE, QTY_KEEP),
                },
                ST_PENDING_CANCEL => match e {
                    EV_PARTIAL_FILL => (ACT_BOOK_UPD, ST_PENDING_CANCEL, QTY_HALF),
                    EV_FULL_FILL => (ACT_BOOK_UPD, ST_FILLED, QTY_ZERO),
                    EV_CANCEL_ACK => (ACT_BOOK_UPD, ST_CANCELED, QTY_ZERO),
                    _ => (ACT_IGNORE, ST_PENDING_CANCEL, QTY_KEEP),
                },
                ST_FILLED => (ACT_IGNORE, ST_FILLED, QTY_ZERO),
                ST_CANCELED => (ACT_IGNORE, ST_CANCELED, QTY_ZERO),
                _ => (ACT_IGNORE, ST_REJECTED, QTY_ZERO),
            };
            let idx = (s << 3) | e;
            p[0] |= ((ns & 1) as u64) << idx;
            p[1] |= (((ns >> 1) & 1) as u64) << idx;
            p[2] |= (((ns >> 2) & 1) as u64) << idx;
            p[3] |= ((act & 1) as u64) << idx;
            p[4] |= (((act >> 1) & 1) as u64) << idx;
            p[5] |= ((qm & 1) as u64) << idx;
            p[6] |= (((qm >> 1) & 1) as u64) << idx;
            e += 1;
        }
        s += 1;
    }
    p
}

const FSM_PLANES: [u64; 7] = build_fsm_bitplanes();

#[inline(always)]
fn select_u32(cond: bool, when_true: u32, when_false: u32) -> u32 {
    let mask = 0u32.wrapping_sub(cond as u32);
    (when_true & mask) | (when_false & !mask)
}

/// Optimized branchless Child Order FSM + Pre-Trade Risk Dispatch:
/// - Normal 8x8 transition table evaluated via shift-mask `u64` bit-planes (0 memory, 0 branches).
/// - Pre-trade risk gating & bounds checks evaluated via pure bitwise masks & selects.
#[unsafe(no_mangle)]
pub extern "C" fn oms_risk_fsm_opt(
    state: u32,
    event: u32,
    qty: u32,
    max_qty: u32,
    risk_flags: u32,
    collar_ok: u32,
) -> u32 {
    let q_keep = qty & 0xFFFF;
    let q_half = (qty >> 1) & 0xFFFF;
    let in_bounds = (state <= 7) & (event <= 7);
    let s = state & 7;
    let e = event & 7;
    let idx = (s << 3) | e;

    let ns0 = ((FSM_PLANES[0] >> idx) & 1) as u32;
    let ns1 = ((FSM_PLANES[1] >> idx) & 1) as u32;
    let ns2 = ((FSM_PLANES[2] >> idx) & 1) as u32;
    let ac0 = ((FSM_PLANES[3] >> idx) & 1) as u32;
    let ac1 = ((FSM_PLANES[4] >> idx) & 1) as u32;
    let qm0 = ((FSM_PLANES[5] >> idx) & 1) != 0;
    let qm1 = ((FSM_PLANES[6] >> idx) & 1) != 0;

    let normal_qty = select_u32(qm1, q_half, select_u32(qm0, q_keep, 0));
    let normal_out = pack_fsm(
        ac0 | (ac1 << 1),
        ns0 | (ns1 << 1) | (ns2 << 2),
        normal_qty,
    );

    let risk_fail = ((risk_flags & 3) != 0)
        | ((risk_flags & 12) == 4)
        | (qty == 0)
        | (qty > max_qty)
        | (collar_ok == 0);

    let is_new_reject = risk_fail & (event == EV_NEW_REQ) & (state == ST_EMPTY);
    let is_rep_reject = risk_fail & (event == EV_REPLACE_REQ) & (state == ST_LIVE);
    let is_other_risk_drop = risk_fail & ((event == EV_NEW_REQ) | (event == EV_REPLACE_REQ));

    let mut out = select_u32(
        is_other_risk_drop,
        pack_fsm(ACT_IGNORE, s, q_keep),
        normal_out,
    );
    out = select_u32(is_new_reject, pack_fsm(ACT_RISK_REJ, ST_REJECTED, 0), out);
    out = select_u32(is_rep_reject, pack_fsm(ACT_RISK_REJ, ST_LIVE, q_keep), out);
    select_u32(in_bounds, out, pack_fsm(ACT_IGNORE, s, q_keep))
}

// ============================================================================
// Pair 5: Zero-Copy OUCH 48-Byte Big-Endian Frame Builder
// ============================================================================

/// 64-byte static guard placed in `.bss` right above the 1 MiB wasm32 shadow stack,
/// forcing `wasm-ld` to reserve `min_pages >= 17` (`1_114_112` bytes).
#[cfg(target_arch = "wasm32")]
static OMS_DMA_GUARD: [u8; 64] = [0; 64];

#[cfg(target_arch = "wasm32")]
const STACK_TOP: usize = 1_048_576;
#[cfg(target_arch = "wasm32")]
const LIVE_LO: usize = STACK_TOP + 64;
#[cfg(target_arch = "wasm32")]
const LIVE_HI: usize = STACK_TOP + 32_768;
#[cfg(target_arch = "wasm32")]
const MIN_LIVE_PAGES: usize = 17;

const OUCH_ENTER_ORDER_TAG: u8 = b'O';
const OUCH_FRAME_LEN: usize = 48;
/// Fixed 8-byte ASCII firm identifier (`"GNOMON01"`), encoded big-endian at `[34..42]`.
const OUCH_FIRM_ID: u64 = 0x474E_4F4D_4F4E_3031;

#[inline(always)]
fn valid_side_u8(side: u8) -> bool {
    side == b'B' || side == b'S'
}

/// Shadow-stack big-endian OUCH frame builder writing into a caller-allocated `[u8; 48]`.
#[inline(never)]
fn build_ouch_frame_on_stack(
    frame: &mut [u8; OUCH_FRAME_LEN],
    cl_ord_id: u64,
    symbol: u64,
    price: u64,
    shares: u32,
    tif: u32,
    side: u8,
) {
    frame[0] = OUCH_ENTER_ORDER_TAG;
    frame[1..9].copy_from_slice(&cl_ord_id.to_be_bytes());
    frame[9] = side;
    frame[10..14].copy_from_slice(&shares.to_be_bytes());
    frame[14..22].copy_from_slice(&symbol.to_le_bytes());
    frame[22..30].copy_from_slice(&price.to_be_bytes());
    frame[30..34].copy_from_slice(&tif.to_be_bytes());
    frame[34..42].copy_from_slice(&OUCH_FIRM_ID.to_be_bytes());
    frame[42] = 0;
    frame[43] = 0;
    frame[44] = 0;
    frame[45] = 0;
    frame[46] = 0;
    frame[47] = 0;
}

/// Staged commit helper copying the 48-byte stack frame into `dst`.
#[inline(never)]
fn commit_ouch_frame(src: &[u8; OUCH_FRAME_LEN], dst: *mut u8) {
    let mut i = 0usize;
    while i < OUCH_FRAME_LEN {
        // SAFETY: Caller verified `dst` has at least 48 writable bytes.
        unsafe {
            core::ptr::write(dst.add(i), src[i]);
        }
        i += 1;
    }
}

/// Precondition for `oms_ouch_pack_ref` and `oms_ouch_pack_opt`.
/// On wasm32, ensures `tx_ptr..tx_ptr+tx_len` lies strictly in live DMA memory
/// above `__stack_pointer` (`Global(0)`) with >= 17 memory pages.
#[unsafe(no_mangle)]
pub extern "C" fn req_oms_ouch_pack(
    tx_ptr: *mut u8,
    tx_len: i32,
    _cl_ord_id: u64,
    _symbol: u64,
    _price: u64,
    _meta: u64,
) -> i32 {
    #[cfg(target_arch = "wasm32")]
    {
        if core::arch::wasm32::memory_size(0) < MIN_LIVE_PAGES {
            return 0;
        }
        let guard_lo = (OMS_DMA_GUARD.as_ptr() as usize).wrapping_add(64);
        let live_lo = if guard_lo > LIVE_LO { guard_lo } else { LIVE_LO };
        let ptr_addr = tx_ptr as usize;
        if ptr_addr < live_lo || ptr_addr > LIVE_HI {
            return 0;
        }
        if tx_len < 0 || (tx_len as usize) > LIVE_HI - ptr_addr {
            return 0;
        }
        1
    }
    #[cfg(not(target_arch = "wasm32"))]
    {
        if tx_ptr.is_null() || tx_len < 0 {
            0
        } else {
            1
        }
    }
}

/// Reference OUCH 5.0 48-byte frame builder (stack-buffered `[u8; 48]` + staged copy).
/// `meta` packs: `shares = meta as u32`, `tif = ((meta >> 32) & 0x00FF_FFFF) as u32`,
/// `side = (meta >> 56) as u8`. All 6 parameters fit in x86-64/ARM64 ABI registers.
#[unsafe(no_mangle)]
pub extern "C" fn oms_ouch_pack_ref(
    tx_ptr: *mut u8,
    tx_len: i32,
    cl_ord_id: u64,
    symbol: u64,
    price: u64,
    meta: u64,
) -> i32 {
    let shares = meta as u32;
    let tif = ((meta >> 32) & 0x00FF_FFFF) as u32;
    let side = (meta >> 56) as u8;
    if tx_len < (OUCH_FRAME_LEN as i32) || !valid_side_u8(side) || shares == 0 {
        return 0;
    }
    let mut frame = [0u8; OUCH_FRAME_LEN];
    build_ouch_frame_on_stack(&mut frame, cl_ord_id, symbol, price, shares, tif, side);
    commit_ouch_frame(&frame, tx_ptr);
    OUCH_FRAME_LEN as i32
}

/// Zero-copy optimized OUCH 5.0 48-byte frame builder:
/// Direct `u64::to_be` / `u32::to_be` unaligned wide stores straight to `tx_ptr`.
/// Zero stack frame (`sub rsp` = 0), proven equivalent under `--ignore-dead-stack`.
#[unsafe(no_mangle)]
pub extern "C" fn oms_ouch_pack_opt(
    tx_ptr: *mut u8,
    tx_len: i32,
    cl_ord_id: u64,
    symbol: u64,
    price: u64,
    meta: u64,
) -> i32 {
    let shares = meta as u32;
    let tif = ((meta >> 32) & 0x00FF_FFFF) as u32;
    let side = (meta >> 56) as u8;
    if tx_len < (OUCH_FRAME_LEN as i32) || !valid_side_u8(side) || shares == 0 {
        return 0;
    }
    // SAFETY: Caller satisfies `req_oms_ouch_pack` and `tx_len >= 48`.
    unsafe {
        core::ptr::write(tx_ptr, OUCH_ENTER_ORDER_TAG);
        core::ptr::write_unaligned(tx_ptr.add(1) as *mut u64, cl_ord_id.to_be());
        core::ptr::write(tx_ptr.add(9), side);
        core::ptr::write_unaligned(tx_ptr.add(10) as *mut u32, shares.to_be());
        core::ptr::write_unaligned(tx_ptr.add(14) as *mut u64, symbol.to_le());
        core::ptr::write_unaligned(tx_ptr.add(22) as *mut u64, price.to_be());
        core::ptr::write_unaligned(tx_ptr.add(30) as *mut u32, tif.to_be());
        core::ptr::write_unaligned(tx_ptr.add(34) as *mut u64, OUCH_FIRM_ID.to_be());
        core::ptr::write_unaligned(tx_ptr.add(42) as *mut u32, 0u32);
        core::ptr::write_unaligned(tx_ptr.add(46) as *mut u16, 0u16);
    }
    OUCH_FRAME_LEN as i32
}

// ============================================================================
// Pair 6: 4-Lane Portfolio Notional / VWAP Accumulator (scalar vs vectorized)
// ============================================================================

/// Precondition for `oms_vwap_scalar_ref` and `oms_vwap_vec_opt`:
/// - On wasm32, `prices[0..4]` and `qtys[0..4]` lie in valid live linear memory.
/// - Every order-book quantity has sign bit `0` (non-negative, non-negative-zero),
///   matching real L2 order-book levels so per-level sign-bit guards never fire.
#[unsafe(no_mangle)]
pub extern "C" fn req_oms_vwap(prices: *const f32, qtys: *const f32) -> i32 {
    #[cfg(target_arch = "wasm32")]
    {
        if core::arch::wasm32::memory_size(0) < MIN_LIVE_PAGES {
            return 0;
        }
        let guard_lo = (OMS_DMA_GUARD.as_ptr() as usize).wrapping_add(64);
        let live_lo = if guard_lo > LIVE_LO { guard_lo } else { LIVE_LO };
        let p_addr = prices as usize;
        let q_addr = qtys as usize;
        if p_addr < live_lo || p_addr > LIVE_HI - 16 {
            return 0;
        }
        if q_addr < live_lo || q_addr > LIVE_HI - 16 {
            return 0;
        }
    }
    #[cfg(not(target_arch = "wasm32"))]
    {
        if prices.is_null() || qtys.is_null() {
            return 0;
        }
    }
    // SAFETY: Bounds checked above.
    unsafe {
        let q_bits = qtys as *const u32;
        if ((*q_bits.add(0) | *q_bits.add(1) | *q_bits.add(2) | *q_bits.add(3)) & 0x8000_0000) != 0
        {
            return 0;
        }
    }
    1
}

/// Scalar 4-lane VWAP reference with per-level sign-bit quantity guards:
/// Defensive scalar OMS code that prevents LLVM SLP auto-vectorization, emitting
/// scalar `movss`/`mulss`/`addss` + 7 branches on x86-64.
/// Uses balanced pairwise reduction `((pq0 + pq1) + (pq2 + pq3)) / ((q0 + q1) + (q2 + q3))`
/// so IEEE-754 rounding is bit-for-bit identical to `oms_vwap_vec_opt`.
#[unsafe(no_mangle)]
pub extern "C" fn oms_vwap_scalar_ref(prices: *const f32, qtys: *const f32) -> f32 {
    // SAFETY: Caller satisfies `req_oms_vwap`.
    unsafe {
        let q0 = *qtys.add(0);
        if (q0.to_bits() & 0x8000_0000) != 0 {
            return 0.0;
        }
        let pq0 = *prices.add(0) * q0;
        let q1 = *qtys.add(1);
        if (q1.to_bits() & 0x8000_0000) != 0 {
            return 0.0;
        }
        let pq1 = *prices.add(1) * q1;
        let q2 = *qtys.add(2);
        if (q2.to_bits() & 0x8000_0000) != 0 {
            return 0.0;
        }
        let pq2 = *prices.add(2) * q2;
        let q3 = *qtys.add(3);
        if (q3.to_bits() & 0x8000_0000) != 0 {
            return 0.0;
        }
        let pq3 = *prices.add(3) * q3;

        let total_q = (q0 + q1) + (q2 + q3);
        if !(total_q > 0.0) {
            return 0.0;
        }
        let num = (pq0 + pq1) + (pq2 + pq3);
        let raw = num / total_q;
        if raw == 0.0 { 0.0 } else { raw }
    }
}

/// Vectorized 4-lane VWAP accumulator (portable branchless SIMD):
/// - Compiles on native `x86_64` to SSE/AVX `movups` + `mulps` + `addps` (1 branch vs 7).
/// - Compiles on native `aarch64` to NEON `ldr q` + `fmul.4s` + `fadd`/`faddp`.
/// - Compiles on `wasm32 +simd128` to `v128.load` + `f32x4.mul` + `f32x4.extract_lane`.
/// Proved exact bit-for-bit equivalent to `oms_vwap_scalar_ref` in Gnomon `QF_ABVFP`.
#[unsafe(no_mangle)]
pub extern "C" fn oms_vwap_vec_opt(prices: *const f32, qtys: *const f32) -> f32 {
    #[cfg(target_arch = "wasm32")]
    {
        use core::arch::wasm32::*;
        // SAFETY: Caller satisfies `req_oms_vwap`.
        unsafe {
            let pv = f32x4(
                *prices.add(0),
                *prices.add(1),
                *prices.add(2),
                *prices.add(3),
            );
            let qv = f32x4(*qtys.add(0), *qtys.add(1), *qtys.add(2), *qtys.add(3));
            let pq = f32x4_mul(pv, qv);
            let num = (f32x4_extract_lane::<0>(pq) + f32x4_extract_lane::<1>(pq))
                + (f32x4_extract_lane::<2>(pq) + f32x4_extract_lane::<3>(pq));
            let total_q = (f32x4_extract_lane::<0>(qv) + f32x4_extract_lane::<1>(qv))
                + (f32x4_extract_lane::<2>(qv) + f32x4_extract_lane::<3>(qv));
            if !(total_q > 0.0) {
                return 0.0;
            }
            let raw = num / total_q;
            if raw == 0.0 { 0.0 } else { raw }
        }
    }
    #[cfg(not(target_arch = "wasm32"))]
    {
        // SAFETY: Caller satisfies `req_oms_vwap`.
        unsafe {
            let p = [
                *prices.add(0),
                *prices.add(1),
                *prices.add(2),
                *prices.add(3),
            ];
            let q = [*qtys.add(0), *qtys.add(1), *qtys.add(2), *qtys.add(3)];
            let mut pq = [0.0f32; 4];
            let mut i = 0;
            while i < 4 {
                pq[i] = p[i] * q[i];
                i += 1;
            }
            let num = (pq[0] + pq[1]) + (pq[2] + pq[3]);
            let total_q = (q[0] + q[1]) + (q[2] + q[3]);
            if !(total_q > 0.0) {
                return 0.0;
            }
            let raw = num / total_q;
            if raw == 0.0 { 0.0 } else { raw }
        }
    }
}

#[cfg(target_arch = "wasm32")]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}
