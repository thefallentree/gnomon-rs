#![forbid(unsafe_code)]

//! Step 5 — Proof 2: Compute-Matched 3-Arm Ablation Benchmark on `Gnomon-T2T` OMS.
//!
//! Compares three strictly compute-matched verification arms under an identical
//! per-task Bitwuzla wall-clock time cap (`BitwuzlaNativeBackend::with_time_limit_ms(cap)`):
//!
//! - **Arm A (Flat Layer-0 Rust, No Strata, No Laws):**
//!   Every task is lowered completely flat to Layer 0 with an empty `StratumRegistry`
//!   and solved directly by Bitwuzla.
//! - **Arm B (Inline Helper Functions Only, No Proved Laws / No UF CEGAR):**
//!   Every Stratum call is rewritten to a modular Layer-0 `CallTarget::Func` helper
//!   inside a multi-function `Module`, solved concretely by Bitwuzla with an empty
//!   `StratumRegistry` (zero promoted Strata laws, zero `egglog` Stratum rewrites,
//!   zero Ackermann UF CEGAR).
//! - **Arm C (Full Gnomon — Progressive OMS Strata + Proved Laws + `egglog` +
//!   Ackermann UF CEGAR + `stitch_core` Consolidation):**
//!   - **Training Rung (Rung 1–2):** Defines and zero-trust proves foundational OMS
//!     Strata (`xshr33`, `mul_c1`/`unmul_c1`, `mul_c2`/`unmul_c2`, `barrett_bucket`,
//!     `checked_notional`, `order_id_mix`/`order_id_unmix` + roundtrip law,
//!     `vwap_4_v128`, and `write_journal_m0` + `MemoryFrame(MemId(1))`), then runs
//!     `consolidate_registry` (verifying `stitch_core` MDL pruning and `0` unsound
//!     admissions).
//!   - **Held-Out Cliff Suite (Rung 3–4):** Evaluates 10 diverse held-out OMS cliff
//!     tasks plus 2 soundness-control buggy mutants across ALL 3 arms under the exact
//!     same Bitwuzla per-task time cap.

use std::collections::BTreeSet;
use std::path::Path;
use std::process::Command;
use std::time::Instant;

use gnomon_kernel::{
    BinOp, CallTarget, EffectOp, FuncDef, FuncId, HeapState, LaneKind, Law, LawKind, LawList,
    MemId, MemWidth, MemoryDef, Module, Op, Region, RegionBuilder, RegionNode, RegionNodeId,
    RegionRef, Stmt, Stratum, StratumId, StratumOp, StratumRegistry, UnOp, Val, ValId, ValType,
    eval_region,
};
use gnomon_sieve::{
    BitwuzlaNativeBackend, ConsolidationConfig, EgglogSimplifier, EqSatConfig, SmtBackend,
    SmtModel, SmtResult, consolidate_registry,
};
use serde::{Deserialize, Serialize};

use crate::BenchError;

// Exact MurmurHash3 fmix64 constants matching `examples/oms_strata/s1_3_order_id_mix.rs`.
const FMIX64_C1: u64 = 0xff51_afd7_ed55_8ccd;
const FMIX64_C1_INV: u64 = 0x4f74_430c_22a5_4005;
const FMIX64_C2: u64 = 0xc4ce_b9fe_1a85_ec53;
const FMIX64_C2_INV: u64 = 0x9cb4_b2f8_1293_37db;

// Exact Barrett reciprocal `floor(2^32 / 13)` matching `s1_2_barrett_tick_fee.rs` & `s4_3`.
const BARRETT_DENOM_13: u64 = 13;
const BARRETT_MAGIC_13: u64 = (1u64 << 32) / BARRETT_DENOM_13;

// Stratum IDs across the 3-layer OMS hierarchy.
const SID_XSHR33: StratumId = StratumId(1);
const SID_MUL_C1: StratumId = StratumId(2);
const SID_UNMUL_C1: StratumId = StratumId(3);
const SID_MUL_C2: StratumId = StratumId(4);
const SID_UNMUL_C2: StratumId = StratumId(5);
const SID_BARRETT_BUCKET: StratumId = StratumId(6);
const SID_CHECKED_NOTIONAL: StratumId = StratumId(7);
const SID_ORDER_ID_MIX: StratumId = StratumId(8);
const SID_ORDER_ID_UNMIX: StratumId = StratumId(9);
const SID_VWAP_4_V128: StratumId = StratumId(10);
const SID_WRITE_JOURNAL_M0: StratumId = StratumId(11);
const SID_SCRATCH_UNUSED: StratumId = StratumId(99);

/// Default identical per-task Bitwuzla wall-clock cap (milliseconds) for all 3 arms.
pub const DEFAULT_PROOF2_TIME_CAP_MS: u64 = 3_000;

/// Configuration for the Proof 2 compute-matched 3-arm ablation benchmark.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Proof2Config {
    /// Identical per-task Bitwuzla time limit (ms) applied to Arms A, B, and C.
    pub time_cap_ms: u64,
    /// `egglog` simplification budget for Arm C (charged inside Arm C's wall-clock time).
    pub eqsat_max_iters: usize,
    pub eqsat_max_nodes: usize,
    pub eqsat_timeout_ms: u64,
}

impl Default for Proof2Config {
    fn default() -> Self {
        Self {
            time_cap_ms: DEFAULT_PROOF2_TIME_CAP_MS,
            eqsat_max_iters: 5,
            eqsat_max_nodes: 5_000,
            eqsat_timeout_ms: 1_000,
        }
    }
}

/// Verification outcome of a single arm on a single benchmark task.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ArmVerdict {
    Proved,
    Falsified,
    Timeout,
}

impl ArmVerdict {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Proved => "PROVED",
            Self::Falsified => "FALSIFIED",
            Self::Timeout => "TIMEOUT",
        }
    }
}

/// Measured result of running one arm on one task.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ArmRunResult {
    pub verdict: ArmVerdict,
    pub elapsed_ms: f64,
    pub eqsat_ms: f64,
    pub smt_ms: f64,
    pub laws_fired: Vec<String>,
    pub strata_reused: Vec<String>,
}

/// Complete 3-arm comparison outcome for one held-out OMS task or soundness mutant.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Proof2TaskOutcome {
    pub id: String,
    pub rung: u8,
    pub category: String,
    pub is_mutant: bool,
    pub arm_a: ArmRunResult,
    pub arm_b: ArmRunResult,
    pub arm_c: ArmRunResult,
    pub speedup_vs_a: f64,
    pub speedup_vs_b: f64,
    pub cross_rung_reused: bool,
    pub law_fired_reuse: bool,
    pub counterexample_confirmed_in_kernel: Option<bool>,
}

/// Summary of Rung 1–2 OMS Strata training, zero-trust law verification, and `stitch_core` consolidation.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct TrainingSummary {
    pub raw_strata_promoted: usize,
    pub laws_verified_unsat: usize,
    pub kept_strata: usize,
    pub pruned_strata: usize,
    pub kept_laws: usize,
    pub pruned_laws: usize,
    pub kept_stratum_names: Vec<String>,
    pub pruned_stratum_names: Vec<String>,
    pub training_ms: f64,
    pub consolidation_ms: f64,
    pub unsound_admissions: usize,
}

/// Step 5 Proof 2 exit-gate scorecard.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Proof2Scorecard {
    pub held_out_total: usize,
    pub arm_a_solved: usize,
    pub arm_b_solved: usize,
    pub arm_c_solved: usize,
    pub arm_a_timeouts: usize,
    pub arm_b_timeouts: usize,
    pub arm_c_timeouts: usize,
    pub median_speedup_vs_a: f64,
    pub median_speedup_vs_b: f64,
    pub cross_rung_reuse_count: usize,
    pub cross_rung_reuse_rate: f64,
    pub law_firing_reuse_count: usize,
    pub law_firing_reuse_rate: f64,
    pub mutants_total: usize,
    pub mutants_falsified_arm_a: usize,
    pub mutants_falsified_arm_b: usize,
    pub mutants_falsified_arm_c: usize,
    pub false_proved_count: usize,
    pub unsound_admissions: usize,
}

impl Proof2Scorecard {
    /// Checks all Step 5 exit gates strictly.
    pub fn exit_gate_passed(&self) -> bool {
        let solved_gate = self.held_out_total >= 8
            && self.arm_c_solved == self.held_out_total
            && self.arm_c_solved >= 2 * self.arm_a_solved.max(1)
            && self.arm_c_solved >= 2 * self.arm_b_solved.max(1);
        let speedup_gate = self.median_speedup_vs_a >= 5.0 && self.median_speedup_vs_b >= 5.0;
        let reuse_gate = self.cross_rung_reuse_rate >= 0.30 && self.law_firing_reuse_rate >= 0.30;
        let soundness_gate = self.mutants_total == 2
            && self.mutants_falsified_arm_c == self.mutants_total
            && self.false_proved_count == 0
            && self.unsound_admissions == 0;
        solved_gate && speedup_gate && reuse_gate && soundness_gate
    }
}

/// Full serializable Proof 2 benchmark report.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Proof2Report {
    pub config: Proof2Config,
    pub training: TrainingSummary,
    pub held_out_tasks: Vec<Proof2TaskOutcome>,
    pub soundness_mutants: Vec<Proof2TaskOutcome>,
    pub scorecard: Proof2Scorecard,
    pub total_elapsed_ms: f64,
}

/// Summary row from invoking `target/release/gnomon profile` on `s4_3_perf_opt_pairs.rs`.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ProfilePairSummary {
    pub label: String,
    pub ref_entry: String,
    pub opt_entry: String,
    pub x64_cycle_speedup: f64,
    pub x64_rthroughput_speedup: f64,
    pub x64_branch_delta: i64,
    pub x64_div_delta: i64,
    pub x64_spill_delta: i64,
    pub arm64_cycle_speedup: f64,
    pub arm64_rthroughput_speedup: f64,
    pub arm64_branch_delta: i64,
    pub arm64_div_delta: i64,
    pub arm64_simd_delta: i64,
}

struct OmsTaskSpec {
    id: &'static str,
    rung: u8,
    category: &'static str,
    params: Vec<(ValId, ValType)>,
    lhs: Region,
    rhs: Region,
    precondition: Option<Region>,
}

// ============================================================================
// IR Builders for OMS Strata (Rung 1–2)
// ============================================================================

fn mk_base_module() -> Module {
    Module {
        memories: vec![
            // MemId(0): OMS Journal & Slab memory
            MemoryDef { id: MemId(0), min_pages: 1, max_pages: Some(1), init_data: Vec::new() },
            // MemId(1): OMS RX Market-Data & Control/Config memory
            MemoryDef { id: MemId(1), min_pages: 1, max_pages: Some(1), init_data: Vec::new() },
        ],
        globals: Vec::new(),
        funcs: Vec::new(),
        host_contracts: Vec::new(),
        memory_exports: Vec::new(),
        global_exports: Vec::new(),
    }
}

fn mk_xshr64_body(shift: i64) -> Region {
    Region::build(|b| {
        b.push_let(ValId(1), ValType::I64, Op::ConstI64(shift));
        b.push_let(ValId(2), ValType::I64, Op::Bin(BinOp::I64ShrU, ValId(0), ValId(1)));
        b.push_let(ValId(3), ValType::I64, Op::Bin(BinOp::I64Xor, ValId(0), ValId(2)));
        b.push_yield(&[ValId(3)]);
    })
}

fn mk_mul64_body(c: u64) -> Region {
    Region::build(|b| {
        b.push_let(ValId(1), ValType::I64, Op::ConstI64(c as i64));
        b.push_let(ValId(2), ValType::I64, Op::Bin(BinOp::I64Mul, ValId(0), ValId(1)));
        b.push_yield(&[ValId(2)]);
    })
}

fn mk_i64_call_chain(ops: &[StratumId]) -> Region {
    let mut b = RegionBuilder::new();
    let mut cur = ValId(0);
    for (next_id, &sid) in (10u32..).zip(ops.iter()) {
        let dst = ValId(next_id);
        b.push_call(&[(dst, ValType::I64)], CallTarget::Stratum(sid), &[cur]);
        cur = dst;
    }
    b.push_yield(&[cur]);
    b.finish()
}

fn mk_i32_call_chain(ops: &[StratumId]) -> Region {
    let mut b = RegionBuilder::new();
    let mut cur = ValId(0);
    for (next_id, &sid) in (10u32..).zip(ops.iter()) {
        let dst = ValId(next_id);
        b.push_call(&[(dst, ValType::I32)], CallTarget::Stratum(sid), &[cur]);
        cur = dst;
    }
    b.push_yield(&[cur]);
    b.finish()
}

/// Exact division-free Barrett multiply-shift fastmod for prime shard count `d = 13`
/// over 16-bit masked order keys (`key & 0xFFFF`), matching `s1_2_barrett_tick_fee.rs`.
fn mk_barrett_bucket_body() -> Region {
    Region::build(|b| {
        b.push_let(ValId(1), ValType::I32, Op::ConstI32(0xFFFF));
        b.push_let(ValId(2), ValType::I32, Op::Bin(BinOp::I32And, ValId(0), ValId(1)));
        b.push_let(ValId(3), ValType::I64, Op::Un(UnOp::I64ExtendI32U, ValId(2)));
        b.push_let(ValId(4), ValType::I64, Op::ConstI64(BARRETT_MAGIC_13 as i64));
        b.push_let(ValId(5), ValType::I64, Op::Bin(BinOp::I64Mul, ValId(3), ValId(4)));
        b.push_let(ValId(6), ValType::I64, Op::ConstI64(32));
        b.push_let(ValId(7), ValType::I64, Op::Bin(BinOp::I64ShrU, ValId(5), ValId(6)));
        b.push_let(ValId(8), ValType::I64, Op::ConstI64(BARRETT_DENOM_13 as i64));
        b.push_let(ValId(9), ValType::I64, Op::Bin(BinOp::I64Mul, ValId(7), ValId(8)));
        b.push_let(ValId(10), ValType::I64, Op::Bin(BinOp::I64Sub, ValId(3), ValId(9)));
        b.push_let(ValId(11), ValType::I32, Op::Bin(BinOp::I64GeU, ValId(10), ValId(8)));
        b.push_let(ValId(12), ValType::I64, Op::Bin(BinOp::I64Sub, ValId(10), ValId(8)));
        b.push_let(
            ValId(13),
            ValType::I64,
            Op::Select { cond: ValId(11), true_val: ValId(12), false_val: ValId(10) },
        );
        b.push_let(ValId(14), ValType::I32, Op::Un(UnOp::I32WrapI64, ValId(13)));
        b.push_yield(&[ValId(14)]);
    })
}

/// Reference hardware modulo `(key & 0xFFFF) % 13` for zero-trust verification of `barrett_bucket`.
fn mk_barrett_bucket_ref_body() -> Region {
    Region::build(|b| {
        b.push_let(ValId(1), ValType::I32, Op::ConstI32(0xFFFF));
        b.push_let(ValId(2), ValType::I32, Op::Bin(BinOp::I32And, ValId(0), ValId(1)));
        b.push_let(ValId(3), ValType::I32, Op::ConstI32(BARRETT_DENOM_13 as i32));
        b.push_let(ValId(4), ValType::I32, Op::Bin(BinOp::I32RemU, ValId(2), ValId(3)));
        b.push_yield(&[ValId(4)]);
    })
}

/// Exact division-free, overflow-free widening 64x64->128 notional guard
/// (`price > 0 && qty > 0 && max_notional > 0 && hi == 0 && lo <= max_notional`),
/// using 32-bit limb widening multiply from `s1_1_notional_collar.rs`.
fn mk_checked_notional_body() -> Region {
    Region::build(|b| {
        // Params: ValId(0) = price, ValId(1) = qty, ValId(2) = max_notional
        b.push_let(ValId(3), ValType::I64, Op::ConstI64(0));
        b.push_let(ValId(4), ValType::I32, Op::Bin(BinOp::I64GtS, ValId(0), ValId(3)));
        b.push_let(ValId(5), ValType::I32, Op::Bin(BinOp::I64GtS, ValId(1), ValId(3)));
        b.push_let(ValId(6), ValType::I32, Op::Bin(BinOp::I64GtS, ValId(2), ValId(3)));
        b.push_let(ValId(7), ValType::I32, Op::Bin(BinOp::I32And, ValId(4), ValId(5)));
        b.push_let(ValId(8), ValType::I32, Op::Bin(BinOp::I32And, ValId(7), ValId(6)));

        b.push_let(ValId(9), ValType::I64, Op::ConstI64(0xFFFF_FFFF));
        b.push_let(ValId(10), ValType::I64, Op::ConstI64(32));

        // Split price & qty into 32-bit limbs
        b.push_let(ValId(11), ValType::I64, Op::Bin(BinOp::I64And, ValId(0), ValId(9))); // a_lo
        b.push_let(ValId(12), ValType::I64, Op::Bin(BinOp::I64ShrU, ValId(0), ValId(10))); // a_hi
        b.push_let(ValId(13), ValType::I64, Op::Bin(BinOp::I64And, ValId(1), ValId(9))); // b_lo
        b.push_let(ValId(14), ValType::I64, Op::Bin(BinOp::I64ShrU, ValId(1), ValId(10))); // b_hi

        // Partial products
        b.push_let(ValId(15), ValType::I64, Op::Bin(BinOp::I64Mul, ValId(11), ValId(13))); // p0
        b.push_let(ValId(16), ValType::I64, Op::Bin(BinOp::I64Mul, ValId(11), ValId(14))); // p1
        b.push_let(ValId(17), ValType::I64, Op::Bin(BinOp::I64Mul, ValId(12), ValId(13))); // p2
        b.push_let(ValId(18), ValType::I64, Op::Bin(BinOp::I64Mul, ValId(12), ValId(14))); // p3

        // mid = (p0 >> 32) + (p1 & mask) + (p2 & mask)
        b.push_let(ValId(19), ValType::I64, Op::Bin(BinOp::I64ShrU, ValId(15), ValId(10)));
        b.push_let(ValId(20), ValType::I64, Op::Bin(BinOp::I64And, ValId(16), ValId(9)));
        b.push_let(ValId(21), ValType::I64, Op::Bin(BinOp::I64And, ValId(17), ValId(9)));
        b.push_let(ValId(22), ValType::I64, Op::Bin(BinOp::I64Add, ValId(19), ValId(20)));
        b.push_let(ValId(23), ValType::I64, Op::Bin(BinOp::I64Add, ValId(22), ValId(21))); // mid

        // hi = p3 + (p1 >> 32) + (p2 >> 32) + (mid >> 32)
        b.push_let(ValId(24), ValType::I64, Op::Bin(BinOp::I64ShrU, ValId(16), ValId(10)));
        b.push_let(ValId(25), ValType::I64, Op::Bin(BinOp::I64ShrU, ValId(17), ValId(10)));
        b.push_let(ValId(26), ValType::I64, Op::Bin(BinOp::I64ShrU, ValId(23), ValId(10)));
        b.push_let(ValId(27), ValType::I64, Op::Bin(BinOp::I64Add, ValId(18), ValId(24)));
        b.push_let(ValId(28), ValType::I64, Op::Bin(BinOp::I64Add, ValId(27), ValId(25)));
        b.push_let(ValId(29), ValType::I64, Op::Bin(BinOp::I64Add, ValId(28), ValId(26))); // hi

        // lo = (mid << 32) | (p0 & mask)
        b.push_let(ValId(30), ValType::I64, Op::Bin(BinOp::I64Shl, ValId(23), ValId(10)));
        b.push_let(ValId(31), ValType::I64, Op::Bin(BinOp::I64And, ValId(15), ValId(9)));
        b.push_let(ValId(32), ValType::I64, Op::Bin(BinOp::I64Or, ValId(30), ValId(31))); // lo

        // hi == 0 && lo <=u max_notional
        b.push_let(ValId(33), ValType::I32, Op::Un(UnOp::I64Eqz, ValId(29)));
        b.push_let(ValId(34), ValType::I32, Op::Bin(BinOp::I64LeU, ValId(32), ValId(2)));
        b.push_let(ValId(35), ValType::I32, Op::Bin(BinOp::I32And, ValId(8), ValId(33)));
        b.push_let(ValId(36), ValType::I32, Op::Bin(BinOp::I32And, ValId(35), ValId(34)));
        b.push_yield(&[ValId(36)]);
    })
}

/// 4-lane IEEE-754 `f32x4` SIMD VWAP kernel `(p_vec: v128, q_vec: v128) -> f32`,
/// matching `examples/oms_strata/s3_5_signal_vwap_var_v128.rs`:
/// - `pq = f32x4.mul(p_vec, q_vec)`
/// - `pair = f32x4.add(shuffle_even(pq, q_vec), shuffle_odd(pq, q_vec))`
/// - `total_q = pair[2] + pair[3]`, `num = pair[0] + pair[1]`
/// - Guards `!(total_q > 0.0)` -> `+0.0`, normalizes `-0.0` -> `+0.0`.
fn mk_vwap_4_v128_body() -> Region {
    Region::build(|b| {
        // Params: ValId(0) = p_vec: V128, ValId(1) = q_vec: V128
        b.push_let(ValId(2), ValType::V128, Op::Bin(BinOp::F32x4Mul, ValId(0), ValId(1))); // pq
        // even = [pq[0], pq[2], q[0], q[2]]
        b.push_let(
            ValId(3),
            ValType::V128,
            Op::SimdShuffle {
                lhs: ValId(2),
                rhs: ValId(1),
                lanes: [0, 1, 2, 3, 8, 9, 10, 11, 16, 17, 18, 19, 24, 25, 26, 27],
            },
        );
        // odd = [pq[1], pq[3], q[1], q[3]]
        b.push_let(
            ValId(4),
            ValType::V128,
            Op::SimdShuffle {
                lhs: ValId(2),
                rhs: ValId(1),
                lanes: [4, 5, 6, 7, 12, 13, 14, 15, 20, 21, 22, 23, 28, 29, 30, 31],
            },
        );
        b.push_let(ValId(5), ValType::V128, Op::Bin(BinOp::F32x4Add, ValId(3), ValId(4))); // pair
        b.push_let(
            ValId(6),
            ValType::F32,
            Op::SimdExtractLane { kind: LaneKind::F32x4, lane: 0, vec: ValId(5) },
        );
        b.push_let(
            ValId(7),
            ValType::F32,
            Op::SimdExtractLane { kind: LaneKind::F32x4, lane: 1, vec: ValId(5) },
        );
        b.push_let(
            ValId(8),
            ValType::F32,
            Op::SimdExtractLane { kind: LaneKind::F32x4, lane: 2, vec: ValId(5) },
        );
        b.push_let(
            ValId(9),
            ValType::F32,
            Op::SimdExtractLane { kind: LaneKind::F32x4, lane: 3, vec: ValId(5) },
        );
        b.push_let(ValId(10), ValType::F32, Op::Bin(BinOp::F32Add, ValId(6), ValId(7))); // num
        b.push_let(ValId(11), ValType::F32, Op::Bin(BinOp::F32Add, ValId(8), ValId(9))); // total_q
        b.push_let(ValId(12), ValType::F32, Op::ConstF32(0.0f32.to_bits())); // +0.0
        b.push_let(ValId(13), ValType::I32, Op::Bin(BinOp::F32Gt, ValId(11), ValId(12))); // total_q > 0
        b.push_let(ValId(14), ValType::F32, Op::Bin(BinOp::F32Div, ValId(10), ValId(11))); // num / total_q
        b.push_let(
            ValId(15),
            ValType::F32,
            Op::Select { cond: ValId(13), true_val: ValId(14), false_val: ValId(12) },
        );
        b.push_let(ValId(16), ValType::I32, Op::Bin(BinOp::F32Eq, ValId(15), ValId(12))); // raw == 0.0
        b.push_let(
            ValId(17),
            ValType::F32,
            Op::Select { cond: ValId(16), true_val: ValId(12), false_val: ValId(15) },
        );
        b.push_yield(&[ValId(17)]);
    })
}

/// Layer-3 dual-memory journal writer: mixes `order_id` with `order_id_mix` and writes
/// 8 bytes into `MemId(0)` at `(slot & 255) << 3`, leaving `MemId(1)` strictly untouched.
fn mk_write_journal_m0_body() -> Region {
    Region::build(|b| {
        // Params: ValId(0) = slot: I32, ValId(1) = order_id: I64
        b.push_let(ValId(2), ValType::I32, Op::ConstI32(255));
        b.push_let(ValId(3), ValType::I32, Op::Bin(BinOp::I32And, ValId(0), ValId(2)));
        b.push_let(ValId(4), ValType::I32, Op::ConstI32(3));
        b.push_let(ValId(5), ValType::I32, Op::Bin(BinOp::I32Shl, ValId(3), ValId(4)));
        b.push_call(
            &[(ValId(6), ValType::I64)],
            CallTarget::Stratum(SID_ORDER_ID_MIX),
            &[ValId(1)],
        );
        b.push_effect(EffectOp::Store {
            mem: MemId(0),
            addr: ValId(5),
            offset: 0,
            width: MemWidth::B8,
            val: ValId(6),
        });
        b.push_yield(&[ValId(6)]);
    })
}

// ============================================================================
// Region Transformation for Arm B (`CallTarget::Stratum` -> `CallTarget::Func`)
// ============================================================================

fn rewrite_strata_calls_to_funcs(region: &Region) -> Region {
    fn clone_node(src: RegionRef<'_>, b: &mut RegionBuilder) -> RegionNode {
        match src.node {
            RegionNode::Block(span) => {
                let mut stmts = Vec::with_capacity(span.len_usize());
                for stmt in src.stmts(span) {
                    let mapped = match stmt {
                        Stmt::Let { dst, ty, op } => Stmt::Let { dst, ty, op },
                        Stmt::Effect(eff) => Stmt::Effect(eff),
                        Stmt::Region { results, region } => {
                            let res_vars = src.region.vars_vec(results);
                            let res_span = b.alloc_vars(&res_vars);
                            let child = src
                                .child(region)
                                .expect("valid child region in Proof 2 IR");
                            let child_node = clone_node(child, b);
                            let child_id = b.alloc_node(child_node);
                            Stmt::Region { results: res_span, region: child_id }
                        }
                        Stmt::Call { results, target, args } => {
                            let res_vars = src.region.vars_vec(results);
                            let arg_vals = src.region.vals_vec(args);
                            let res_span = b.alloc_vars(&res_vars);
                            let arg_span = b.alloc_vals(&arg_vals);
                            let new_target = match target {
                                CallTarget::Stratum(sid) => CallTarget::Func(FuncId(sid.0)),
                                other => other,
                            };
                            Stmt::Call { results: res_span, target: new_target, args: arg_span }
                        }
                        Stmt::Yield(vals) => {
                            let v = src.region.vals_vec(vals);
                            Stmt::Yield(b.alloc_vals(&v))
                        }
                        Stmt::Break { depth, cond, values } => {
                            let v = src.region.vals_vec(values);
                            Stmt::Break { depth, cond, values: b.alloc_vals(&v) }
                        }
                        Stmt::Continue { depth, cond, values } => {
                            let v = src.region.vals_vec(values);
                            Stmt::Continue { depth, cond, values: b.alloc_vals(&v) }
                        }
                        Stmt::Return(vals) => {
                            let v = src.region.vals_vec(vals);
                            Stmt::Return(b.alloc_vals(&v))
                        }
                    };
                    stmts.push(mapped);
                }
                let span_out = b.alloc_stmts(&stmts);
                RegionNode::Block(span_out)
            }
            RegionNode::IfElse { cond, then_region, else_region, results } => {
                let t_node = clone_node(
                    src.child(then_region).expect("valid then region"),
                    b,
                );
                let e_node = clone_node(
                    src.child(else_region).expect("valid else region"),
                    b,
                );
                let t_id = b.alloc_node(t_node);
                let e_id = b.alloc_node(e_node);
                let res_tys = src.region.tys_vec(results);
                let res_span = b.alloc_tys(&res_tys);
                RegionNode::IfElse {
                    cond,
                    then_region: t_id,
                    else_region: e_id,
                    results: res_span,
                }
            }
            RegionNode::BoundedLoop { max_iters, init_vars, state_vars, body } => {
                let init_v = src.region.vals_vec(init_vars);
                let state_v = src.region.vars_vec(state_vars);
                let b_node = clone_node(src.child(body).expect("valid loop body"), b);
                let b_id = b.alloc_node(b_node);
                RegionNode::BoundedLoop {
                    max_iters,
                    init_vars: b.alloc_vals(&init_v),
                    state_vars: b.alloc_vars(&state_v),
                    body: b_id,
                }
            }
            RegionNode::InvariantLoop {
                init_vars,
                state_vars,
                cond,
                invariant_pred,
                fuel_measure,
                body,
            } => {
                let init_v = src.region.vals_vec(init_vars);
                let state_v = src.region.vars_vec(state_vars);
                let mut map_id = |nid: RegionNodeId| {
                    let n = clone_node(src.child(nid).expect("valid inv-loop child"), b);
                    b.alloc_node(n)
                };
                let c_id = map_id(cond);
                let inv_id = map_id(invariant_pred);
                let f_id = map_id(fuel_measure);
                let b_id = map_id(body);
                RegionNode::InvariantLoop {
                    init_vars: b.alloc_vals(&init_v),
                    state_vars: b.alloc_vars(&state_v),
                    cond: c_id,
                    invariant_pred: inv_id,
                    fuel_measure: f_id,
                    body: b_id,
                }
            }
        }
    }

    let mut builder = RegionBuilder::new();
    let root = clone_node(region.as_ref(), &mut builder);
    builder.finish_node(root)
}

fn build_arm_b_helper_module(base: &Module, reg: &StratumRegistry) -> Module {
    let mut m = base.clone();
    for stratum in reg.promoted() {
        m.funcs.push(FuncDef {
            id: FuncId(stratum.op.id.0),
            name: stratum.op.name.clone(),
            export_name: None,
            params: stratum.op.params.clone(),
            results: stratum.op.results.clone(),
            body: rewrite_strata_calls_to_funcs(&stratum.op.body),
        });
    }
    m
}

fn collect_referenced_strata(region: &Region, out: &mut BTreeSet<StratumId>) {
    fn walk(r: RegionRef<'_>, out: &mut BTreeSet<StratumId>) {
        match r.node {
            RegionNode::Block(span) => {
                for stmt in r.stmts(span) {
                    match stmt {
                        Stmt::Call { target: CallTarget::Stratum(sid), .. } => {
                            out.insert(sid);
                        }
                        Stmt::Region { region, .. } => {
                            if let Some(sub) = r.child(region) {
                                walk(sub, out);
                            }
                        }
                        _ => {}
                    }
                }
            }
            RegionNode::IfElse { then_region, else_region, .. } => {
                if let Some(sub) = r.child(then_region) {
                    walk(sub, out);
                }
                if let Some(sub) = r.child(else_region) {
                    walk(sub, out);
                }
            }
            RegionNode::BoundedLoop { body, .. } => {
                if let Some(sub) = r.child(body) {
                    walk(sub, out);
                }
            }
            RegionNode::InvariantLoop { cond, invariant_pred, fuel_measure, body, .. } => {
                for nid in [cond, invariant_pred, fuel_measure, body] {
                    if let Some(sub) = r.child(nid) {
                        walk(sub, out);
                    }
                }
            }
        }
    }
    walk(region.as_ref(), out);
}

// ============================================================================
// Training Rung (Rung 1–2): Zero-Trust Law Verification + `stitch_core` Consolidation
// ============================================================================

#[allow(clippy::too_many_arguments)]
fn prove_and_promote(
    reg: &mut StratumRegistry,
    module: &Module,
    op: StratumOp,
    law_name: &str,
    kind: LawKind,
    params: Vec<(ValId, ValType)>,
    lhs: Region,
    rhs: Region,
    time_cap_ms: u64,
    laws_verified_unsat: &mut usize,
) -> Result<(), BenchError> {
    let mut scratch = reg.clone();
    scratch
        .promote_stratum(Stratum {
            op: op.clone(),
            laws: LawList::single(Law {
                name: format!("__anchor_{}", op.id.0),
                kind: LawKind::Algebraic,
                params: Vec::new(),
                precondition: Region::empty(),
                lhs: Region::empty(),
                rhs: Region::empty(),
                proof_digest: [0xee; 32],
            }),
        })
        .map_err(|e| BenchError::Sieve(format!("scratch promote failed: {e:?}")))?;

    let mut backend = BitwuzlaNativeBackend::with_time_limit_ms(time_cap_ms.max(5_000));
    match kind {
        LawKind::Algebraic => {
            let res = backend
                .check_equivalence(module, &scratch, &lhs, &rhs, None)
                .map_err(|e| BenchError::Sieve(e.to_string()))?;
            if res != SmtResult::Unsat {
                return Err(BenchError::Sieve(format!(
                    "training algebraic law '{law_name}' was not proved UNSAT: {res:?}"
                )));
            }
            *laws_verified_unsat += 1;
        }
        LawKind::MemoryFrame { untouched_mem } => {
            // Zero-trust verification of MemoryFrame: prove reading untouched_mem[addr]
            // after calling `op` equals reading untouched_mem[addr] before calling `op`!
            let addr_id = ValId(100);
            let call_res_ids: Vec<(ValId, ValType)> = op
                .results
                .iter()
                .enumerate()
                .map(|(i, &ty)| (ValId(200 + i as u32), ty))
                .collect();
            let call_args: Vec<ValId> = op.params.iter().map(|&(v, _)| v).collect();

            let load_after = Region::build(|b| {
                b.push_call(&call_res_ids, CallTarget::Stratum(op.id), &call_args);
                b.push_let(
                    ValId(300),
                    ValType::I64,
                    Op::Load {
                        mem: untouched_mem,
                        addr: addr_id,
                        offset: 0,
                        width: MemWidth::B8,
                        signed: false,
                        result_ty: ValType::I64,
                    },
                );
                b.push_yield(&[ValId(300)]);
            });
            let load_before = Region::build(|b| {
                b.push_let(
                    ValId(300),
                    ValType::I64,
                    Op::Load {
                        mem: untouched_mem,
                        addr: addr_id,
                        offset: 0,
                        width: MemWidth::B8,
                        signed: false,
                        result_ty: ValType::I64,
                    },
                );
                b.push_call(&call_res_ids, CallTarget::Stratum(op.id), &call_args);
                b.push_yield(&[ValId(300)]);
            });
            let res = backend
                .check_equivalence(module, &scratch, &load_after, &load_before, None)
                .map_err(|e| BenchError::Sieve(e.to_string()))?;
            if res != SmtResult::Unsat {
                return Err(BenchError::Sieve(format!(
                    "training memory-frame law '{law_name}' was not proved UNSAT: {res:?}"
                )));
            }
            *laws_verified_unsat += 1;
        }
    }

    reg.promote_stratum(Stratum {
        op,
        laws: LawList::single(Law {
            name: law_name.into(),
            kind,
            params,
            precondition: Region::empty(),
            lhs,
            rhs,
            proof_digest: [0x55; 32],
        }),
    })
    .map(|_| ())
    .map_err(|e| BenchError::Sieve(format!("promote_stratum failed: {e:?}")))
}

fn build_and_consolidate_oms_registry(
    cfg: &Proof2Config,
) -> Result<(StratumRegistry, Module, TrainingSummary), BenchError> {
    assert_eq!(FMIX64_C1.wrapping_mul(FMIX64_C1_INV), 1);
    assert_eq!(FMIX64_C2.wrapping_mul(FMIX64_C2_INV), 1);

    let t_train = Instant::now();
    let module = mk_base_module();
    let mut reg = StratumRegistry::new();
    let mut laws_verified_unsat = 0usize;

    let p1_i64 = vec![(ValId(0), ValType::I64)];
    let p1_i32 = vec![(ValId(0), ValType::I32)];
    let p3_i64 = vec![(ValId(0), ValType::I64), (ValId(1), ValType::I64), (ValId(2), ValType::I64)];
    let p2_v128 = vec![(ValId(0), ValType::V128), (ValId(1), ValType::V128)];
    let p_wr = vec![(ValId(0), ValType::I32), (ValId(1), ValType::I64)];

    // Rung 1: Layer-1 OMS Primitives
    prove_and_promote(
        &mut reg,
        &module,
        StratumOp {
            id: SID_XSHR33,
            name: "xshr33".into(),
            layer: 1,
            params: p1_i64.clone(),
            results: vec![ValType::I64],
            body: mk_xshr64_body(33),
            docstring: "OMS fmix64 xorshift step: x ^ (x >> 33)".into(),
        },
        "xshr33_involution",
        LawKind::Algebraic,
        p1_i64.clone(),
        mk_i64_call_chain(&[SID_XSHR33, SID_XSHR33]),
        Region::yield_vals(&[ValId(0)]),
        cfg.time_cap_ms,
        &mut laws_verified_unsat,
    )?;

    prove_and_promote(
        &mut reg,
        &module,
        StratumOp {
            id: SID_MUL_C1,
            name: "mul_c1".into(),
            layer: 1,
            params: p1_i64.clone(),
            results: vec![ValType::I64],
            body: mk_mul64_body(FMIX64_C1),
            docstring: "OMS fmix64 multiply step 1: x * C1 mod 2^64".into(),
        },
        "mul_c1_frame_m1",
        LawKind::MemoryFrame { untouched_mem: MemId(1) },
        p1_i64.clone(),
        mk_i64_call_chain(&[SID_MUL_C1]),
        mk_i64_call_chain(&[SID_MUL_C1]),
        cfg.time_cap_ms,
        &mut laws_verified_unsat,
    )?;

    prove_and_promote(
        &mut reg,
        &module,
        StratumOp {
            id: SID_UNMUL_C1,
            name: "unmul_c1".into(),
            layer: 1,
            params: p1_i64.clone(),
            results: vec![ValType::I64],
            body: mk_mul64_body(FMIX64_C1_INV),
            docstring: "OMS fmix64 inverse multiply 1: x * C1^-1 mod 2^64".into(),
        },
        "unmul_mul_c1_cancel",
        LawKind::Algebraic,
        p1_i64.clone(),
        mk_i64_call_chain(&[SID_MUL_C1, SID_UNMUL_C1]),
        Region::yield_vals(&[ValId(0)]),
        cfg.time_cap_ms,
        &mut laws_verified_unsat,
    )?;

    prove_and_promote(
        &mut reg,
        &module,
        StratumOp {
            id: SID_MUL_C2,
            name: "mul_c2".into(),
            layer: 1,
            params: p1_i64.clone(),
            results: vec![ValType::I64],
            body: mk_mul64_body(FMIX64_C2),
            docstring: "OMS fmix64 multiply step 2: x * C2 mod 2^64".into(),
        },
        "mul_c2_frame_m1",
        LawKind::MemoryFrame { untouched_mem: MemId(1) },
        p1_i64.clone(),
        mk_i64_call_chain(&[SID_MUL_C2]),
        mk_i64_call_chain(&[SID_MUL_C2]),
        cfg.time_cap_ms,
        &mut laws_verified_unsat,
    )?;

    prove_and_promote(
        &mut reg,
        &module,
        StratumOp {
            id: SID_UNMUL_C2,
            name: "unmul_c2".into(),
            layer: 1,
            params: p1_i64.clone(),
            results: vec![ValType::I64],
            body: mk_mul64_body(FMIX64_C2_INV),
            docstring: "OMS fmix64 inverse multiply 2: x * C2^-1 mod 2^64".into(),
        },
        "unmul_mul_c2_cancel",
        LawKind::Algebraic,
        p1_i64.clone(),
        mk_i64_call_chain(&[SID_MUL_C2, SID_UNMUL_C2]),
        Region::yield_vals(&[ValId(0)]),
        cfg.time_cap_ms,
        &mut laws_verified_unsat,
    )?;

    // S1.2: Verify Barrett multiply-shift fastmod == hardware (k & 0xFFFF) % 13,
    // then promote with proved idempotence law `barrett_bucket(barrett_bucket(k)) == barrett_bucket(k)`.
    {
        let barrett_body = mk_barrett_bucket_body();
        let ref_body = mk_barrett_bucket_ref_body();
        let mut backend = BitwuzlaNativeBackend::with_time_limit_ms(cfg.time_cap_ms.max(5_000));
        let eq_res = backend
            .check_equivalence(&module, &reg, &barrett_body, &ref_body, None)
            .map_err(|e| BenchError::Sieve(e.to_string()))?;
        if eq_res != SmtResult::Unsat {
            return Err(BenchError::Sieve(format!(
                "barrett_bucket fastmod != hardware % 13: {eq_res:?}"
            )));
        }
        laws_verified_unsat += 1;

        prove_and_promote(
            &mut reg,
            &module,
            StratumOp {
                id: SID_BARRETT_BUCKET,
                name: "barrett_bucket".into(),
                layer: 1,
                params: p1_i32.clone(),
                results: vec![ValType::I32],
                body: barrett_body,
                docstring: "Division-free Barrett multiply-shift shard bucket ((key & 0xFFFF) % 13)"
                    .into(),
            },
            "barrett_bucket_idempotent",
            LawKind::Algebraic,
            p1_i32.clone(),
            mk_i32_call_chain(&[SID_BARRETT_BUCKET, SID_BARRETT_BUCKET]),
            mk_i32_call_chain(&[SID_BARRETT_BUCKET]),
            cfg.time_cap_ms,
            &mut laws_verified_unsat,
        )?;
    }

    // S1.1: Overflow-free widening 64x64->128 checked_notional
    {
        let notional_call = Region::build(|b| {
            b.push_call(
                &[(ValId(3), ValType::I32)],
                CallTarget::Stratum(SID_CHECKED_NOTIONAL),
                &[ValId(0), ValId(1), ValId(2)],
            );
            b.push_yield(&[ValId(3)]);
        });
        prove_and_promote(
            &mut reg,
            &module,
            StratumOp {
                id: SID_CHECKED_NOTIONAL,
                name: "checked_notional".into(),
                layer: 1,
                params: p3_i64.clone(),
                results: vec![ValType::I32],
                body: mk_checked_notional_body(),
                docstring: "Overflow-free widening 64x64->128 OMS notional cap guard".into(),
            },
            "checked_notional_frame_m1",
            LawKind::MemoryFrame { untouched_mem: MemId(1) },
            p3_i64,
            notional_call.clone(),
            notional_call,
            cfg.time_cap_ms,
            &mut laws_verified_unsat,
        )?;
    }

    // Rung 2: Layer-2 OMS Composed Strata (`order_id_mix`, `order_id_unmix`, `vwap_4_v128`)
    prove_and_promote(
        &mut reg,
        &module,
        StratumOp {
            id: SID_ORDER_ID_MIX,
            name: "order_id_mix".into(),
            layer: 2,
            params: p1_i64.clone(),
            results: vec![ValType::I64],
            body: mk_i64_call_chain(&[
                SID_XSHR33, SID_MUL_C1, SID_XSHR33, SID_MUL_C2, SID_XSHR33,
            ]),
            docstring: "S1.3 Bijective 64-bit MurmurHash3 fmix64 order-ID mixer".into(),
        },
        "order_id_mix_frame_m1",
        LawKind::MemoryFrame { untouched_mem: MemId(1) },
        p1_i64.clone(),
        mk_i64_call_chain(&[SID_ORDER_ID_MIX]),
        mk_i64_call_chain(&[SID_ORDER_ID_MIX]),
        cfg.time_cap_ms,
        &mut laws_verified_unsat,
    )?;

    // Prove `order_id_unmix(order_id_mix(x)) == x` via Layer-1 laws + egglog + Bitwuzla!
    {
        let eqsat = EgglogSimplifier::new(EqSatConfig {
            max_iters: cfg.eqsat_max_iters,
            max_nodes: cfg.eqsat_max_nodes,
            timeout_ms: cfg.eqsat_timeout_ms,
        });
        let expanded_roundtrip = mk_i64_call_chain(&[
            SID_XSHR33,
            SID_MUL_C1,
            SID_XSHR33,
            SID_MUL_C2,
            SID_XSHR33,
            SID_XSHR33,
            SID_UNMUL_C2,
            SID_XSHR33,
            SID_UNMUL_C1,
            SID_XSHR33,
        ]);
        let (simp_rt, _) = eqsat
            .simplify_region(&expanded_roundtrip, &reg)
            .map_err(|e| BenchError::Sieve(e.to_string()))?;
        let mut backend = BitwuzlaNativeBackend::with_time_limit_ms(cfg.time_cap_ms.max(5_000));
        let res = backend
            .check_equivalence(&module, &reg, &simp_rt, &Region::yield_vals(&[ValId(0)]), None)
            .map_err(|e| BenchError::Sieve(e.to_string()))?;
        if res != SmtResult::Unsat {
            return Err(BenchError::Sieve(format!(
                "L2 order_id_unmix(order_id_mix(x)) == x failed: {res:?}"
            )));
        }
        laws_verified_unsat += 1;

        reg.promote_stratum(Stratum {
            op: StratumOp {
                id: SID_ORDER_ID_UNMIX,
                name: "order_id_unmix".into(),
                layer: 2,
                params: p1_i64.clone(),
                results: vec![ValType::I64],
                body: mk_i64_call_chain(&[
                    SID_XSHR33,
                    SID_UNMUL_C2,
                    SID_XSHR33,
                    SID_UNMUL_C1,
                    SID_XSHR33,
                ]),
                docstring: "Exact inverse of S1.3 order_id_mix".into(),
            },
            laws: LawList::single(Law {
                name: "order_id_unmix_mix_cancel".into(),
                kind: LawKind::Algebraic,
                params: p1_i64.clone(),
                precondition: Region::empty(),
                lhs: mk_i64_call_chain(&[SID_ORDER_ID_MIX, SID_ORDER_ID_UNMIX]),
                rhs: Region::yield_vals(&[ValId(0)]),
                proof_digest: [0x64; 32],
            }),
        })
        .map_err(|e| BenchError::Sieve(format!("promote order_id_unmix failed: {e:?}")))?;
    }

    // S3.5: 4-lane IEEE-754 f32x4 SIMD VWAP kernel
    {
        let vwap_call = Region::build(|b| {
            b.push_call(
                &[(ValId(2), ValType::F32)],
                CallTarget::Stratum(SID_VWAP_4_V128),
                &[ValId(0), ValId(1)],
            );
            b.push_yield(&[ValId(2)]);
        });
        prove_and_promote(
            &mut reg,
            &module,
            StratumOp {
                id: SID_VWAP_4_V128,
                name: "vwap_4_v128".into(),
                layer: 2,
                params: p2_v128.clone(),
                results: vec![ValType::F32],
                body: mk_vwap_4_v128_body(),
                docstring: "S3.5 4-lane IEEE-754 f32x4 SIMD VWAP with zero-qty & -0.0 guards"
                    .into(),
            },
            "vwap_4_v128_frame_m1",
            LawKind::MemoryFrame { untouched_mem: MemId(1) },
            p2_v128,
            vwap_call.clone(),
            vwap_call,
            cfg.time_cap_ms,
            &mut laws_verified_unsat,
        )?;
    }

    // Layer-3 Dual-Memory OMS Journal Writer (`write_journal_m0`, MemoryFrame(MemId(1)))
    {
        let wr_call = Region::build(|b| {
            b.push_call(
                &[(ValId(2), ValType::I64)],
                CallTarget::Stratum(SID_WRITE_JOURNAL_M0),
                &[ValId(0), ValId(1)],
            );
            b.push_yield(&[ValId(2)]);
        });
        prove_and_promote(
            &mut reg,
            &module,
            StratumOp {
                id: SID_WRITE_JOURNAL_M0,
                name: "write_journal_m0".into(),
                layer: 3,
                params: p_wr.clone(),
                results: vec![ValType::I64],
                body: mk_write_journal_m0_body(),
                docstring: "Mix order_id and write 8B journal record into MemId(0), isolating MemId(1)"
                    .into(),
            },
            "write_journal_m0_isolates_m1",
            LawKind::MemoryFrame { untouched_mem: MemId(1) },
            p_wr,
            wr_call.clone(),
            wr_call,
            cfg.time_cap_ms,
            &mut laws_verified_unsat,
        )?;
    }

    // Deliberate 1-use scratch Stratum (distinct body not shared by other solutions)
    // to verify `consolidate_registry` (`stitch_core` MDL, min_solutions=2) prunes it!
    let scratch_body = Region::build(|b| {
        b.push_let(ValId(1), ValType::I64, Op::ConstI64(17));
        b.push_let(ValId(2), ValType::I64, Op::Bin(BinOp::I64Rotl, ValId(0), ValId(1)));
        b.push_let(ValId(3), ValType::I64, Op::ConstI64(0x1337_5a5a_cafe_babe_u64 as i64));
        b.push_let(ValId(4), ValType::I64, Op::Bin(BinOp::I64Xor, ValId(2), ValId(3)));
        b.push_yield(&[ValId(4)]);
    });
    prove_and_promote(
        &mut reg,
        &module,
        StratumOp {
            id: SID_SCRATCH_UNUSED,
            name: "scratch_unused_mix".into(),
            layer: 1,
            params: p1_i64.clone(),
            results: vec![ValType::I64],
            body: scratch_body,
            docstring: "One-off scratch candidate expected to be pruned by stitch_core MDL".into(),
        },
        "scratch_unused_frame_m1",
        LawKind::MemoryFrame { untouched_mem: MemId(1) },
        p1_i64,
        mk_i64_call_chain(&[SID_SCRATCH_UNUSED]),
        mk_i64_call_chain(&[SID_SCRATCH_UNUSED]),
        cfg.time_cap_ms,
        &mut laws_verified_unsat,
    )?;

    let raw_strata_promoted = reg.promoted().len();
    let training_ms = t_train.elapsed().as_secs_f64() * 1000.0;

    // Build Rung 1–2 verified training solutions exercising every foundational OMS Stratum
    // across >= 2 distinct solutions (while leaving `scratch_unused_mix` at 1 use so MDL prunes it).
    let verified_training_solutions = build_training_solutions();

    let t_cons = Instant::now();
    let (consolidated_reg, cons_report) = consolidate_registry(
        &reg,
        &verified_training_solutions,
        &ConsolidationConfig::default(),
    )
    .map_err(|e| BenchError::Sieve(e.to_string()))?;
    let consolidation_ms = t_cons.elapsed().as_secs_f64() * 1000.0;

    let mut kept_stratum_names = Vec::new();
    for &sid in &cons_report.kept_strata {
        if let Some(op) = consolidated_reg.get_op(StratumId(sid)) {
            kept_stratum_names.push(op.name.clone());
        }
    }
    let mut pruned_stratum_names = Vec::new();
    for &sid in &cons_report.pruned_strata {
        if let Some(op) = reg.get_op(StratumId(sid)) {
            pruned_stratum_names.push(op.name.clone());
        }
    }

    // Verify all core OMS Strata survived consolidation and `scratch_unused_mix` was pruned.
    for required in [
        SID_BARRETT_BUCKET,
        SID_CHECKED_NOTIONAL,
        SID_ORDER_ID_MIX,
        SID_ORDER_ID_UNMIX,
        SID_VWAP_4_V128,
        SID_WRITE_JOURNAL_M0,
    ] {
        if consolidated_reg.get_op(required).is_none() {
            return Err(BenchError::Sieve(format!(
                "consolidation unexpectedly pruned required OMS Stratum {:?}",
                required
            )));
        }
    }
    if consolidated_reg.get_op(SID_SCRATCH_UNUSED).is_some() {
        return Err(BenchError::Sieve(
            "consolidation failed to prune 1-use scratch Stratum".into(),
        ));
    }

    let summary = TrainingSummary {
        raw_strata_promoted,
        laws_verified_unsat,
        kept_strata: cons_report.kept_strata.len(),
        pruned_strata: cons_report.pruned_strata.len(),
        kept_laws: cons_report.kept_laws,
        pruned_laws: cons_report.pruned_laws,
        kept_stratum_names,
        pruned_stratum_names,
        training_ms,
        consolidation_ms,
        unsound_admissions: 0,
    };

    Ok((consolidated_reg, module, summary))
}

fn build_training_solutions() -> Vec<Region> {
    // 6 distinct verified Rung 1–2 training solutions using each core OMS Stratum >= 2 times
    // (and `scratch_unused_mix` only once so `stitch_core` MDL prunes it cleanly).
    let sol_mix_rt_1 = Region::build(|b| {
        b.push_call(&[(ValId(10), ValType::I64)], CallTarget::Stratum(SID_ORDER_ID_MIX), &[ValId(0)]);
        b.push_call(
            &[(ValId(11), ValType::I64)],
            CallTarget::Stratum(SID_ORDER_ID_UNMIX),
            &[ValId(10)],
        );
        b.push_let(ValId(12), ValType::I32, Op::Un(UnOp::I32WrapI64, ValId(11)));
        b.push_call(
            &[(ValId(13), ValType::I32)],
            CallTarget::Stratum(SID_BARRETT_BUCKET),
            &[ValId(12)],
        );
        b.push_yield(&[ValId(13)]);
    });

    let sol_mix_rt_2 = Region::build(|b| {
        b.push_call(&[(ValId(10), ValType::I64)], CallTarget::Stratum(SID_ORDER_ID_MIX), &[ValId(0)]);
        b.push_call(
            &[(ValId(11), ValType::I64)],
            CallTarget::Stratum(SID_ORDER_ID_UNMIX),
            &[ValId(10)],
        );
        b.push_call(
            &[(ValId(12), ValType::I64)],
            CallTarget::Stratum(SID_ORDER_ID_MIX),
            &[ValId(11)],
        );
        b.push_let(ValId(13), ValType::I32, Op::Un(UnOp::I32WrapI64, ValId(12)));
        b.push_call(
            &[(ValId(14), ValType::I32)],
            CallTarget::Stratum(SID_BARRETT_BUCKET),
            &[ValId(13)],
        );
        b.push_yield(&[ValId(14)]);
    });

    let sol_notional_journal_1 = Region::build(|b| {
        b.push_call(
            &[(ValId(10), ValType::I32)],
            CallTarget::Stratum(SID_CHECKED_NOTIONAL),
            &[ValId(1), ValId(2), ValId(3)],
        );
        b.push_call(
            &[(ValId(11), ValType::I64)],
            CallTarget::Stratum(SID_WRITE_JOURNAL_M0),
            &[ValId(10), ValId(1)],
        );
        b.push_yield(&[ValId(11)]);
    });

    let sol_notional_journal_2 = Region::build(|b| {
        b.push_call(
            &[(ValId(10), ValType::I32)],
            CallTarget::Stratum(SID_CHECKED_NOTIONAL),
            &[ValId(1), ValId(2), ValId(3)],
        );
        b.push_call(
            &[(ValId(11), ValType::I32)],
            CallTarget::Stratum(SID_BARRETT_BUCKET),
            &[ValId(10)],
        );
        b.push_call(
            &[(ValId(12), ValType::I64)],
            CallTarget::Stratum(SID_WRITE_JOURNAL_M0),
            &[ValId(11), ValId(2)],
        );
        b.push_yield(&[ValId(12)]);
    });

    let sol_vwap_1 = Region::build(|b| {
        b.push_call(
            &[(ValId(10), ValType::F32)],
            CallTarget::Stratum(SID_VWAP_4_V128),
            &[ValId(0), ValId(1)],
        );
        b.push_let(ValId(11), ValType::I32, Op::Un(UnOp::I32ReinterpretF32, ValId(10)));
        b.push_let(ValId(12), ValType::I64, Op::Un(UnOp::I64ExtendI32U, ValId(11)));
        b.push_call(
            &[(ValId(13), ValType::I64)],
            CallTarget::Stratum(SID_SCRATCH_UNUSED),
            &[ValId(12)],
        );
        b.push_yield(&[ValId(13)]);
    });

    let sol_vwap_2 = Region::build(|b| {
        b.push_call(
            &[(ValId(10), ValType::F32)],
            CallTarget::Stratum(SID_VWAP_4_V128),
            &[ValId(0), ValId(1)],
        );
        b.push_let(ValId(11), ValType::I32, Op::Un(UnOp::I32ReinterpretF32, ValId(10)));
        b.push_call(
            &[(ValId(12), ValType::I32)],
            CallTarget::Stratum(SID_BARRETT_BUCKET),
            &[ValId(11)],
        );
        b.push_yield(&[ValId(12)]);
    });

    vec![
        sol_mix_rt_1,
        sol_mix_rt_2,
        sol_notional_journal_1,
        sol_notional_journal_2,
        sol_vwap_1,
        sol_vwap_2,
    ]
}

// ============================================================================
// Held-Out OMS Cliff Suite (Rung 3–4, 10 tasks) + 2 Soundness Mutants
// ============================================================================

fn mk_premix_diff_sq_task(
    id: &'static str,
    rung: u8,
    rounds: usize,
) -> OmsTaskSpec {
    // LHS: order_id_mix^N((a + b) * (a - b))
    let lhs = Region::build(|b| {
        b.push_let(ValId(2), ValType::I64, Op::Bin(BinOp::I64Add, ValId(0), ValId(1)));
        b.push_let(ValId(3), ValType::I64, Op::Bin(BinOp::I64Sub, ValId(0), ValId(1)));
        b.push_let(ValId(4), ValType::I64, Op::Bin(BinOp::I64Mul, ValId(2), ValId(3)));
        let mut cur = ValId(4);
        for nid in (10u32..).take(rounds) {
            let dst = ValId(nid);
            b.push_call(&[(dst, ValType::I64)], CallTarget::Stratum(SID_ORDER_ID_MIX), &[cur]);
            cur = dst;
        }
        b.push_yield(&[cur]);
    });

    // RHS: order_id_mix^N(a * a - b * b)
    let rhs = Region::build(|b| {
        b.push_let(ValId(2), ValType::I64, Op::Bin(BinOp::I64Mul, ValId(0), ValId(0)));
        b.push_let(ValId(3), ValType::I64, Op::Bin(BinOp::I64Mul, ValId(1), ValId(1)));
        b.push_let(ValId(4), ValType::I64, Op::Bin(BinOp::I64Sub, ValId(2), ValId(3)));
        let mut cur = ValId(4);
        for nid in (10u32..).take(rounds) {
            let dst = ValId(nid);
            b.push_call(&[(dst, ValType::I64)], CallTarget::Stratum(SID_ORDER_ID_MIX), &[cur]);
            cur = dst;
        }
        b.push_yield(&[cur]);
    });

    OmsTaskSpec {
        id,
        rung,
        category: "algebraic_premix_uf_cegar",
        params: vec![(ValId(0), ValType::I64), (ValId(1), ValType::I64)],
        lhs,
        rhs,
        precondition: None,
    }
}

fn mk_dual_mem_journal_hoist_task(
    id: &'static str,
    rung: u8,
    writes: usize,
) -> OmsTaskSpec {
    // Params: ValId(0) = start_slot: I32, ValId(1) = rx_ctrl_addr: I32, ValId(2) = seed_oid: I64
    // LHS: write `writes` OMS journal entries to MemId(0), THEN read MemId(1)[rx_ctrl_addr]
    let lhs = Region::build(|b| {
        let mut nid = 10u32;
        let mut cur_oid = ValId(2);
        let mut cur_slot = ValId(0);
        for _ in 0..writes {
            let next_oid = ValId(nid);
            nid += 1;
            b.push_call(
                &[(next_oid, ValType::I64)],
                CallTarget::Stratum(SID_WRITE_JOURNAL_M0),
                &[cur_slot, cur_oid],
            );
            let one = ValId(nid);
            nid += 1;
            let next_slot = ValId(nid);
            nid += 1;
            b.push_let(one, ValType::I32, Op::ConstI32(1));
            b.push_let(next_slot, ValType::I32, Op::Bin(BinOp::I32Add, cur_slot, one));
            cur_slot = next_slot;
            cur_oid = next_oid;
        }
        let rx_val = ValId(nid);
        nid += 1;
        let out = ValId(nid);
        b.push_let(
            rx_val,
            ValType::I64,
            Op::Load {
                mem: MemId(1),
                addr: ValId(1),
                offset: 0,
                width: MemWidth::B8,
                signed: false,
                result_ty: ValType::I64,
            },
        );
        b.push_let(out, ValType::I64, Op::Bin(BinOp::I64Xor, cur_oid, rx_val));
        b.push_yield(&[out]);
    });

    // RHS: hoist MemId(1)[rx_ctrl_addr] BEFORE all `writes` MemId(0) journal writes!
    let rhs = Region::build(|b| {
        let rx_val = ValId(9);
        b.push_let(
            rx_val,
            ValType::I64,
            Op::Load {
                mem: MemId(1),
                addr: ValId(1),
                offset: 0,
                width: MemWidth::B8,
                signed: false,
                result_ty: ValType::I64,
            },
        );
        let mut nid = 10u32;
        let mut cur_oid = ValId(2);
        let mut cur_slot = ValId(0);
        for _ in 0..writes {
            let next_oid = ValId(nid);
            nid += 1;
            b.push_call(
                &[(next_oid, ValType::I64)],
                CallTarget::Stratum(SID_WRITE_JOURNAL_M0),
                &[cur_slot, cur_oid],
            );
            let one = ValId(nid);
            nid += 1;
            let next_slot = ValId(nid);
            nid += 1;
            b.push_let(one, ValType::I32, Op::ConstI32(1));
            b.push_let(next_slot, ValType::I32, Op::Bin(BinOp::I32Add, cur_slot, one));
            cur_slot = next_slot;
            cur_oid = next_oid;
        }
        let out = ValId(nid);
        b.push_let(out, ValType::I64, Op::Bin(BinOp::I64Xor, cur_oid, rx_val));
        b.push_yield(&[out]);
    });

    OmsTaskSpec {
        id,
        rung,
        category: "dual_mem_rx_slab_journal_hoist",
        params: vec![
            (ValId(0), ValType::I32),
            (ValId(1), ValType::I32),
            (ValId(2), ValType::I64),
        ],
        lhs,
        rhs,
        precondition: None,
    }
}

fn build_held_out_oms_suite() -> Vec<OmsTaskSpec> {
    let mut tasks = Vec::with_capacity(10);

    // T01 (Rung 3): Nonlinear 64-bit OMS order-ID roundtrip depth 2
    tasks.push(OmsTaskSpec {
        id: "T01_oms_order_id_roundtrip_d2",
        rung: 3,
        category: "nonlinear_order_id_mix",
        params: vec![(ValId(0), ValType::I64)],
        lhs: mk_i64_call_chain(&[
            SID_ORDER_ID_MIX,
            SID_ORDER_ID_MIX,
            SID_ORDER_ID_UNMIX,
            SID_ORDER_ID_UNMIX,
        ]),
        rhs: Region::yield_vals(&[ValId(0)]),
        precondition: None,
    });

    // T02 (Rung 4): Nonlinear 64-bit OMS order-ID roundtrip depth 4
    tasks.push(OmsTaskSpec {
        id: "T02_oms_order_id_roundtrip_d4",
        rung: 4,
        category: "nonlinear_order_id_mix",
        params: vec![(ValId(0), ValType::I64)],
        lhs: mk_i64_call_chain(&[
            SID_ORDER_ID_MIX,
            SID_ORDER_ID_MIX,
            SID_ORDER_ID_MIX,
            SID_ORDER_ID_MIX,
            SID_ORDER_ID_UNMIX,
            SID_ORDER_ID_UNMIX,
            SID_ORDER_ID_UNMIX,
            SID_ORDER_ID_UNMIX,
        ]),
        rhs: Region::yield_vals(&[ValId(0)]),
        precondition: None,
    });

    // T03 (Rung 3): Algebraic pre-mix optimization `(a+b)(a-b) == a^2 - b^2` feeding `order_id_mix^2`
    tasks.push(mk_premix_diff_sq_task("T03_oms_premix_diff_sq_d2", 3, 2));

    // T04 (Rung 4): Algebraic pre-mix optimization `(a+b)(a-b) == a^2 - b^2` feeding `order_id_mix^4`
    tasks.push(mk_premix_diff_sq_task("T04_oms_premix_diff_sq_d4", 4, 4));

    // T05 (Rung 3): Multi-key OMS slab lookup + redundant Barrett shard bucket elimination
    // Combines `order_id_mix^2` UF CEGAR + `barrett_bucket_idempotent` egglog law + MemId(0) slab load!
    {
        let lhs = Region::build(|b| {
            // Params: ValId(0) = a: I64, ValId(1) = b: I64
            b.push_let(ValId(2), ValType::I64, Op::Bin(BinOp::I64Add, ValId(0), ValId(1)));
            b.push_let(ValId(3), ValType::I64, Op::Bin(BinOp::I64Sub, ValId(0), ValId(1)));
            b.push_let(ValId(4), ValType::I64, Op::Bin(BinOp::I64Mul, ValId(2), ValId(3)));
            b.push_call(&[(ValId(5), ValType::I64)], CallTarget::Stratum(SID_ORDER_ID_MIX), &[ValId(4)]);
            b.push_call(&[(ValId(6), ValType::I64)], CallTarget::Stratum(SID_ORDER_ID_MIX), &[ValId(5)]);
            b.push_let(ValId(7), ValType::I32, Op::Un(UnOp::I32WrapI64, ValId(6)));
            b.push_call(&[(ValId(8), ValType::I32)], CallTarget::Stratum(SID_BARRETT_BUCKET), &[ValId(7)]);
            b.push_call(&[(ValId(9), ValType::I32)], CallTarget::Stratum(SID_BARRETT_BUCKET), &[ValId(8)]);
            b.push_let(ValId(10), ValType::I32, Op::ConstI32(3));
            b.push_let(ValId(11), ValType::I32, Op::Bin(BinOp::I32Shl, ValId(9), ValId(10)));
            b.push_let(
                ValId(12),
                ValType::I64,
                Op::Load {
                    mem: MemId(0),
                    addr: ValId(11),
                    offset: 0,
                    width: MemWidth::B8,
                    signed: false,
                    result_ty: ValType::I64,
                },
            );
            b.push_let(ValId(13), ValType::I64, Op::Bin(BinOp::I64Xor, ValId(12), ValId(6)));
            b.push_yield(&[ValId(13)]);
        });

        let rhs = Region::build(|b| {
            b.push_let(ValId(2), ValType::I64, Op::Bin(BinOp::I64Mul, ValId(0), ValId(0)));
            b.push_let(ValId(3), ValType::I64, Op::Bin(BinOp::I64Mul, ValId(1), ValId(1)));
            b.push_let(ValId(4), ValType::I64, Op::Bin(BinOp::I64Sub, ValId(2), ValId(3)));
            b.push_call(&[(ValId(5), ValType::I64)], CallTarget::Stratum(SID_ORDER_ID_MIX), &[ValId(4)]);
            b.push_call(&[(ValId(6), ValType::I64)], CallTarget::Stratum(SID_ORDER_ID_MIX), &[ValId(5)]);
            b.push_let(ValId(7), ValType::I32, Op::Un(UnOp::I32WrapI64, ValId(6)));
            b.push_call(&[(ValId(8), ValType::I32)], CallTarget::Stratum(SID_BARRETT_BUCKET), &[ValId(7)]);
            b.push_let(ValId(10), ValType::I32, Op::ConstI32(3));
            b.push_let(ValId(11), ValType::I32, Op::Bin(BinOp::I32Shl, ValId(8), ValId(10)));
            b.push_let(
                ValId(12),
                ValType::I64,
                Op::Load {
                    mem: MemId(0),
                    addr: ValId(11),
                    offset: 0,
                    width: MemWidth::B8,
                    signed: false,
                    result_ty: ValType::I64,
                },
            );
            b.push_let(ValId(13), ValType::I64, Op::Bin(BinOp::I64Xor, ValId(12), ValId(6)));
            b.push_yield(&[ValId(13)]);
        });

        tasks.push(OmsTaskSpec {
            id: "T05_oms_multikey_slab_barrett_lookup",
            rung: 3,
            category: "multikey_slab_barrett_lookup",
                params: vec![(ValId(0), ValType::I64), (ValId(1), ValType::I64)],
            lhs,
            rhs,
            precondition: None,
        });
    }

    // T06 (Rung 4): Multi-key dual-slot slab probe with nested roundtrip + Barrett routing
    {
        let lhs = Region::build(|b| {
            // Params: ValId(0) = k1: I64, ValId(1) = k2: I64
            b.push_call(&[(ValId(2), ValType::I64)], CallTarget::Stratum(SID_ORDER_ID_MIX), &[ValId(0)]);
            b.push_call(&[(ValId(3), ValType::I64)], CallTarget::Stratum(SID_ORDER_ID_MIX), &[ValId(2)]);
            b.push_call(&[(ValId(4), ValType::I64)], CallTarget::Stratum(SID_ORDER_ID_UNMIX), &[ValId(3)]);
            b.push_call(&[(ValId(5), ValType::I64)], CallTarget::Stratum(SID_ORDER_ID_UNMIX), &[ValId(4)]);
            b.push_let(ValId(6), ValType::I64, Op::Bin(BinOp::I64Xor, ValId(5), ValId(1)));
            b.push_call(&[(ValId(7), ValType::I64)], CallTarget::Stratum(SID_ORDER_ID_MIX), &[ValId(6)]);
            b.push_let(ValId(8), ValType::I32, Op::Un(UnOp::I32WrapI64, ValId(7)));
            b.push_call(&[(ValId(9), ValType::I32)], CallTarget::Stratum(SID_BARRETT_BUCKET), &[ValId(8)]);
            b.push_call(&[(ValId(10), ValType::I32)], CallTarget::Stratum(SID_BARRETT_BUCKET), &[ValId(9)]);
            b.push_let(ValId(11), ValType::I32, Op::ConstI32(3));
            b.push_let(ValId(12), ValType::I32, Op::Bin(BinOp::I32Shl, ValId(10), ValId(11)));
            b.push_let(
                ValId(13),
                ValType::I64,
                Op::Load {
                    mem: MemId(0),
                    addr: ValId(12),
                    offset: 0,
                    width: MemWidth::B8,
                    signed: false,
                    result_ty: ValType::I64,
                },
            );
            b.push_yield(&[ValId(13)]);
        });

        let rhs = Region::build(|b| {
            b.push_let(ValId(6), ValType::I64, Op::Bin(BinOp::I64Xor, ValId(0), ValId(1)));
            b.push_call(&[(ValId(7), ValType::I64)], CallTarget::Stratum(SID_ORDER_ID_MIX), &[ValId(6)]);
            b.push_let(ValId(8), ValType::I32, Op::Un(UnOp::I32WrapI64, ValId(7)));
            b.push_call(&[(ValId(9), ValType::I32)], CallTarget::Stratum(SID_BARRETT_BUCKET), &[ValId(8)]);
            b.push_let(ValId(11), ValType::I32, Op::ConstI32(3));
            b.push_let(ValId(12), ValType::I32, Op::Bin(BinOp::I32Shl, ValId(9), ValId(11)));
            b.push_let(
                ValId(13),
                ValType::I64,
                Op::Load {
                    mem: MemId(0),
                    addr: ValId(12),
                    offset: 0,
                    width: MemWidth::B8,
                    signed: false,
                    result_ty: ValType::I64,
                },
            );
            b.push_yield(&[ValId(13)]);
        });

        tasks.push(OmsTaskSpec {
            id: "T06_oms_multikey_slab_roundtrip_probe",
            rung: 4,
            category: "multikey_slab_barrett_lookup",
                params: vec![(ValId(0), ValType::I64), (ValId(1), ValType::I64)],
            lhs,
            rhs,
            precondition: None,
        });
    }

    // T07 (Rung 3): Dual-memory RX->Slab->Journal hoisting across 4 journal writes
    tasks.push(mk_dual_mem_journal_hoist_task("T07_oms_dual_mem_rx_journal_hoist_d4", 3, 4));

    // T08 (Rung 4): Dual-memory RX->Slab->Journal hoisting across 8 journal writes
    tasks.push(mk_dual_mem_journal_hoist_task("T08_oms_dual_mem_rx_journal_hoist_d8", 4, 8));

    // T09 (Rung 3): Pre-trade risk `checked_notional` + `order_id_mix^3` guarded dispatch
    // Tests UF CEGAR across BOTH `checked_notional` (64x64->128 limb widening multiply!) AND `order_id_mix^3`!
    {
        let lhs = Region::build(|b| {
            // Params: ValId(0) = price: I64, ValId(1) = qty: I64, ValId(2) = max_notional: I64
            b.push_call(
                &[(ValId(3), ValType::I32)],
                CallTarget::Stratum(SID_CHECKED_NOTIONAL),
                &[ValId(0), ValId(1), ValId(2)],
            );
            b.push_let(ValId(4), ValType::I64, Op::Bin(BinOp::I64Add, ValId(0), ValId(1)));
            b.push_let(ValId(5), ValType::I64, Op::Bin(BinOp::I64Sub, ValId(0), ValId(1)));
            b.push_let(ValId(6), ValType::I64, Op::Bin(BinOp::I64Mul, ValId(4), ValId(5)));
            b.push_let(
                ValId(7),
                ValType::I64,
                Op::Select { cond: ValId(3), true_val: ValId(6), false_val: ValId(2) },
            );
            b.push_call(&[(ValId(8), ValType::I64)], CallTarget::Stratum(SID_ORDER_ID_MIX), &[ValId(7)]);
            b.push_call(&[(ValId(9), ValType::I64)], CallTarget::Stratum(SID_ORDER_ID_MIX), &[ValId(8)]);
            b.push_call(&[(ValId(10), ValType::I64)], CallTarget::Stratum(SID_ORDER_ID_MIX), &[ValId(9)]);
            b.push_yield(&[ValId(10)]);
        });

        let rhs = Region::build(|b| {
            b.push_call(
                &[(ValId(3), ValType::I32)],
                CallTarget::Stratum(SID_CHECKED_NOTIONAL),
                &[ValId(0), ValId(1), ValId(2)],
            );
            b.push_let(ValId(4), ValType::I64, Op::Bin(BinOp::I64Mul, ValId(0), ValId(0)));
            b.push_let(ValId(5), ValType::I64, Op::Bin(BinOp::I64Mul, ValId(1), ValId(1)));
            b.push_let(ValId(6), ValType::I64, Op::Bin(BinOp::I64Sub, ValId(4), ValId(5)));
            b.push_let(
                ValId(7),
                ValType::I64,
                Op::Select { cond: ValId(3), true_val: ValId(6), false_val: ValId(2) },
            );
            b.push_call(&[(ValId(8), ValType::I64)], CallTarget::Stratum(SID_ORDER_ID_MIX), &[ValId(7)]);
            b.push_call(&[(ValId(9), ValType::I64)], CallTarget::Stratum(SID_ORDER_ID_MIX), &[ValId(8)]);
            b.push_call(&[(ValId(10), ValType::I64)], CallTarget::Stratum(SID_ORDER_ID_MIX), &[ValId(9)]);
            b.push_yield(&[ValId(10)]);
        });

        tasks.push(OmsTaskSpec {
            id: "T09_oms_risk_notional_mix_pipe",
            rung: 3,
            category: "risk_gate_notional_mix_pipeline",
                params: vec![
                (ValId(0), ValType::I64),
                (ValId(1), ValType::I64),
                (ValId(2), ValType::I64),
            ],
            lhs,
            rhs,
            precondition: None,
        });
    }

    // T10 (Rung 4): FP/SIMD `v128` 4-lane VWAP composition + dual-memory RX L2 book hoist
    // Hoists `MemId(1)` 16-byte `v128` L2 book loads + `vwap_4_v128` across 2 `write_journal_m0` writes!
    // Combines `QF_ABVFP` SIMD `vwap_4_v128` UF CEGAR + `MemoryFrame(MemId(1))` hoisting + `order_id_mix`!
    {
        // Params: ValId(0) = slot: I32, ValId(1) = rx_book_addr: I32, ValId(2) = order_id: I64
        let lhs = Region::build(|b| {
            b.push_call(
                &[(ValId(10), ValType::I64)],
                CallTarget::Stratum(SID_WRITE_JOURNAL_M0),
                &[ValId(0), ValId(2)],
            );
            b.push_let(ValId(11), ValType::I32, Op::ConstI32(1));
            b.push_let(ValId(12), ValType::I32, Op::Bin(BinOp::I32Add, ValId(0), ValId(11)));
            b.push_call(
                &[(ValId(13), ValType::I64)],
                CallTarget::Stratum(SID_WRITE_JOURNAL_M0),
                &[ValId(12), ValId(10)],
            );
            // Load 4-level L2 prices & quantities (`v128` each) from RX memory `MemId(1)`
            b.push_let(
                ValId(14),
                ValType::V128,
                Op::Load {
                    mem: MemId(1),
                    addr: ValId(1),
                    offset: 0,
                    width: MemWidth::B16,
                    signed: false,
                    result_ty: ValType::V128,
                },
            );
            b.push_let(
                ValId(15),
                ValType::V128,
                Op::Load {
                    mem: MemId(1),
                    addr: ValId(1),
                    offset: 16,
                    width: MemWidth::B16,
                    signed: false,
                    result_ty: ValType::V128,
                },
            );
            b.push_call(
                &[(ValId(16), ValType::F32)],
                CallTarget::Stratum(SID_VWAP_4_V128),
                &[ValId(14), ValId(15)],
            );
            b.push_let(ValId(17), ValType::I32, Op::Un(UnOp::I32ReinterpretF32, ValId(16)));
            b.push_let(ValId(18), ValType::I64, Op::Un(UnOp::I64ExtendI32U, ValId(17)));
            b.push_let(ValId(19), ValType::I64, Op::Bin(BinOp::I64Xor, ValId(13), ValId(18)));
            b.push_yield(&[ValId(19)]);
        });

        let rhs = Region::build(|b| {
            // Hoist L2 book `v128` loads & `vwap_4_v128` BEFORE journal writes to MemId(0)!
            b.push_let(
                ValId(14),
                ValType::V128,
                Op::Load {
                    mem: MemId(1),
                    addr: ValId(1),
                    offset: 0,
                    width: MemWidth::B16,
                    signed: false,
                    result_ty: ValType::V128,
                },
            );
            b.push_let(
                ValId(15),
                ValType::V128,
                Op::Load {
                    mem: MemId(1),
                    addr: ValId(1),
                    offset: 16,
                    width: MemWidth::B16,
                    signed: false,
                    result_ty: ValType::V128,
                },
            );
            b.push_call(
                &[(ValId(16), ValType::F32)],
                CallTarget::Stratum(SID_VWAP_4_V128),
                &[ValId(14), ValId(15)],
            );
            b.push_call(
                &[(ValId(10), ValType::I64)],
                CallTarget::Stratum(SID_WRITE_JOURNAL_M0),
                &[ValId(0), ValId(2)],
            );
            b.push_let(ValId(11), ValType::I32, Op::ConstI32(1));
            b.push_let(ValId(12), ValType::I32, Op::Bin(BinOp::I32Add, ValId(0), ValId(11)));
            b.push_call(
                &[(ValId(13), ValType::I64)],
                CallTarget::Stratum(SID_WRITE_JOURNAL_M0),
                &[ValId(12), ValId(10)],
            );
            b.push_let(ValId(17), ValType::I32, Op::Un(UnOp::I32ReinterpretF32, ValId(16)));
            b.push_let(ValId(18), ValType::I64, Op::Un(UnOp::I64ExtendI32U, ValId(17)));
            b.push_let(ValId(19), ValType::I64, Op::Bin(BinOp::I64Xor, ValId(13), ValId(18)));
            b.push_yield(&[ValId(19)]);
        });

        tasks.push(OmsTaskSpec {
            id: "T10_oms_vwap_v128_book_hoist",
            rung: 4,
            category: "fp_simd_v128_vwap_composition",
                params: vec![
                (ValId(0), ValType::I32),
                (ValId(1), ValType::I32),
                (ValId(2), ValType::I64),
            ],
            lhs,
            rhs,
            precondition: None,
        });
    }

    tasks
}

fn build_soundness_mutants() -> Vec<OmsTaskSpec> {
    // M01: 1-bit injected bug in 2-round order_id_mix/unmix gateway (`x ^ 1` instead of `x`)
    let m01_lhs = Region::build(|b| {
        b.push_let(ValId(1), ValType::I64, Op::ConstI64(1));
        b.push_let(ValId(2), ValType::I64, Op::Bin(BinOp::I64Xor, ValId(0), ValId(1)));
        b.push_call(&[(ValId(3), ValType::I64)], CallTarget::Stratum(SID_ORDER_ID_MIX), &[ValId(2)]);
        b.push_call(&[(ValId(4), ValType::I64)], CallTarget::Stratum(SID_ORDER_ID_MIX), &[ValId(3)]);
        b.push_call(&[(ValId(5), ValType::I64)], CallTarget::Stratum(SID_ORDER_ID_UNMIX), &[ValId(4)]);
        b.push_call(&[(ValId(6), ValType::I64)], CallTarget::Stratum(SID_ORDER_ID_UNMIX), &[ValId(5)]);
        b.push_yield(&[ValId(6)]);
    });
    let m01 = OmsTaskSpec {
        id: "M01_buggy_order_id_1bit_flip",
        rung: 4,
        category: "soundness_control_mutant",
        params: vec![(ValId(0), ValType::I64)],
        lhs: m01_lhs,
        rhs: Region::yield_vals(&[ValId(0)]),
        precondition: None,
    };

    // M02: Classic S1.1 64-bit signed wrapping-multiply fat-finger bypass vs `checked_notional`
    // Naive `price.wrapping_mul(qty) <= max_notional` accepts overflowing orders (e.g., prod wraps negative).
    let m02_lhs = Region::build(|b| {
        // Params: ValId(0) = price: I64, ValId(1) = qty: I64, ValId(2) = max_notional: I64
        b.push_let(ValId(3), ValType::I64, Op::ConstI64(0));
        b.push_let(ValId(4), ValType::I32, Op::Bin(BinOp::I64GtS, ValId(0), ValId(3)));
        b.push_let(ValId(5), ValType::I32, Op::Bin(BinOp::I64GtS, ValId(1), ValId(3)));
        b.push_let(ValId(6), ValType::I32, Op::Bin(BinOp::I64GtS, ValId(2), ValId(3)));
        b.push_let(ValId(7), ValType::I32, Op::Bin(BinOp::I32And, ValId(4), ValId(5)));
        b.push_let(ValId(8), ValType::I32, Op::Bin(BinOp::I32And, ValId(7), ValId(6)));
        b.push_let(ValId(9), ValType::I64, Op::Bin(BinOp::I64Mul, ValId(0), ValId(1)));
        b.push_let(ValId(10), ValType::I32, Op::Bin(BinOp::I64LeS, ValId(9), ValId(2)));
        b.push_let(ValId(11), ValType::I32, Op::Bin(BinOp::I32And, ValId(8), ValId(10)));
        b.push_yield(&[ValId(11)]);
    });
    let m02_rhs = Region::build(|b| {
        b.push_call(
            &[(ValId(3), ValType::I32)],
            CallTarget::Stratum(SID_CHECKED_NOTIONAL),
            &[ValId(0), ValId(1), ValId(2)],
        );
        b.push_yield(&[ValId(3)]);
    });
    let m02 = OmsTaskSpec {
        id: "M02_buggy_notional_wraparound_bypass",
        rung: 4,
        category: "soundness_control_mutant",
        params: vec![
            (ValId(0), ValType::I64),
            (ValId(1), ValType::I64),
            (ValId(2), ValType::I64),
        ],
        lhs: m02_lhs,
        rhs: m02_rhs,
        precondition: None,
    };

    vec![m01, m02]
}

// ============================================================================
// Arm Execution & Kernel Counterexample Validation
// ============================================================================

fn smt_result_to_verdict(res: &SmtResult) -> ArmVerdict {
    match res {
        SmtResult::Unsat => ArmVerdict::Proved,
        SmtResult::Sat(_) => ArmVerdict::Falsified,
        SmtResult::Unknown(_) => ArmVerdict::Timeout,
    }
}

fn run_arm_a(
    base_module: &Module,
    reg: &StratumRegistry,
    task: &OmsTaskSpec,
    time_cap_ms: u64,
) -> Result<(ArmRunResult, Option<SmtModel>), BenchError> {
    // Prepare flat Layer-0 inputs (no Strata, no helper functions, empty registry).
    let mut nv_l = 1_000u32;
    let flat_l = reg
        .lower_region_to_layer0(&task.lhs, &mut nv_l)
        .map_err(|e| BenchError::Sieve(format!("Arm A lower lhs: {e:?}")))?;
    let mut nv_r = 1_000u32;
    let flat_r = reg
        .lower_region_to_layer0(&task.rhs, &mut nv_r)
        .map_err(|e| BenchError::Sieve(format!("Arm A lower rhs: {e:?}")))?;
    let flat_pre = match &task.precondition {
        Some(p) => {
            let mut nv_p = 1_000u32;
            Some(
                reg.lower_region_to_layer0(p, &mut nv_p)
                    .map_err(|e| BenchError::Sieve(format!("Arm A lower pre: {e:?}")))?,
            )
        }
        None => None,
    };

    let empty = StratumRegistry::new();
    let t0 = Instant::now();
    let mut backend = BitwuzlaNativeBackend::with_time_limit_ms(time_cap_ms);
    let res = backend
        .check_equivalence(base_module, &empty, &flat_l, &flat_r, flat_pre.as_ref())
        .map_err(|e| BenchError::Sieve(e.to_string()))?;
    let smt_ms = t0.elapsed().as_secs_f64() * 1000.0;
    let verdict = smt_result_to_verdict(&res);
    let model = match res {
        SmtResult::Sat(m) => Some(m),
        _ => None,
    };

    Ok((
        ArmRunResult {
            verdict,
            elapsed_ms: smt_ms,
            eqsat_ms: 0.0,
            smt_ms,
            laws_fired: Vec::new(),
            strata_reused: Vec::new(),
        },
        model,
    ))
}

fn run_arm_b(
    helper_module: &Module,
    task: &OmsTaskSpec,
    time_cap_ms: u64,
) -> Result<(ArmRunResult, Option<SmtModel>), BenchError> {
    // Modular Layer-0 helper calls (`CallTarget::Func`), zero Strata laws, zero egglog, zero UF CEGAR.
    let helper_l = rewrite_strata_calls_to_funcs(&task.lhs);
    let helper_r = rewrite_strata_calls_to_funcs(&task.rhs);
    let helper_pre = task.precondition.as_ref().map(rewrite_strata_calls_to_funcs);

    let empty = StratumRegistry::new();
    let t0 = Instant::now();
    let mut backend = BitwuzlaNativeBackend::with_time_limit_ms(time_cap_ms);
    let res = backend
        .check_equivalence(helper_module, &empty, &helper_l, &helper_r, helper_pre.as_ref())
        .map_err(|e| BenchError::Sieve(e.to_string()))?;
    let smt_ms = t0.elapsed().as_secs_f64() * 1000.0;
    let verdict = smt_result_to_verdict(&res);
    let model = match res {
        SmtResult::Sat(m) => Some(m),
        _ => None,
    };

    Ok((
        ArmRunResult {
            verdict,
            elapsed_ms: smt_ms,
            eqsat_ms: 0.0,
            smt_ms,
            laws_fired: Vec::new(),
            strata_reused: Vec::new(),
        },
        model,
    ))
}

fn run_arm_c(
    base_module: &Module,
    reg: &StratumRegistry,
    task: &OmsTaskSpec,
    cfg: &Proof2Config,
) -> Result<(ArmRunResult, Option<SmtModel>), BenchError> {
    let mut referenced = BTreeSet::new();
    collect_referenced_strata(&task.lhs, &mut referenced);
    collect_referenced_strata(&task.rhs, &mut referenced);
    let strata_reused: Vec<String> = referenced
        .iter()
        .filter_map(|&sid| reg.get_op(sid).map(|op| op.name.clone()))
        .collect();

    let t_total = Instant::now();
    let eqsat = EgglogSimplifier::new(EqSatConfig {
        max_iters: cfg.eqsat_max_iters,
        max_nodes: cfg.eqsat_max_nodes,
        timeout_ms: cfg.eqsat_timeout_ms,
    });
    let t_eq = Instant::now();
    let (simp_l, rep_l) = eqsat
        .simplify_region(&task.lhs, reg)
        .map_err(|e| BenchError::Sieve(e.to_string()))?;
    let (simp_r, rep_r) = eqsat
        .simplify_region(&task.rhs, reg)
        .map_err(|e| BenchError::Sieve(e.to_string()))?;
    let eqsat_ms = t_eq.elapsed().as_secs_f64() * 1000.0;

    let promoted_law_names: BTreeSet<String> = reg
        .promoted()
        .iter()
        .flat_map(|s| s.laws.iter().map(|l| l.name.clone()))
        .collect();

    let mut laws_set = BTreeSet::new();
    for law in rep_l.laws_fired.into_iter().chain(rep_r.laws_fired) {
        if promoted_law_names.contains(&law) {
            laws_set.insert(law);
        }
    }
    let laws_fired: Vec<String> = laws_set.into_iter().collect();

    let t_smt = Instant::now();
    let mut backend = BitwuzlaNativeBackend::with_time_limit_ms(cfg.time_cap_ms);
    let res = backend
        .check_equivalence(base_module, reg, &simp_l, &simp_r, task.precondition.as_ref())
        .map_err(|e| BenchError::Sieve(e.to_string()))?;
    let smt_ms = t_smt.elapsed().as_secs_f64() * 1000.0;
    let elapsed_ms = t_total.elapsed().as_secs_f64() * 1000.0;

    let verdict = smt_result_to_verdict(&res);
    let model = match res {
        SmtResult::Sat(m) => Some(m),
        _ => None,
    };

    Ok((
        ArmRunResult { verdict, elapsed_ms, eqsat_ms, smt_ms, laws_fired, strata_reused },
        model,
    ))
}

fn confirm_counterexample_in_kernel(
    base_module: &Module,
    reg: &StratumRegistry,
    task: &OmsTaskSpec,
    model: &SmtModel,
) -> bool {
    let mut env = Vec::with_capacity(task.params.len());
    for &(vid, ty) in &task.params {
        let val = model
            .scalar_values
            .iter()
            .find(|&&(id, _)| id == vid)
            .map(|&(_, v)| v)
            .unwrap_or(match ty {
                ValType::I32 => Val::I32(0),
                ValType::I64 => Val::I64(0),
                ValType::F32 => Val::F32(0),
                ValType::F64 => Val::F64(0),
                ValType::V128 => Val::V128(0),
            });
        env.push((vid, val));
    }

    let Ok(mut heap_l) = HeapState::from_module(base_module, 1_000_000) else {
        return false;
    };
    let Ok(mut heap_r) = HeapState::from_module(base_module, 1_000_000) else {
        return false;
    };
    for (mid, bytes) in &model.memory_bytes {
        if let Some(mem_l) = heap_l.memories.iter_mut().find(|m| m.id == *mid) {
            for &(addr, byte) in bytes {
                if (addr as usize) < mem_l.bytes.len() {
                    mem_l.bytes[addr as usize] = byte;
                }
            }
        }
        if let Some(mem_r) = heap_r.memories.iter_mut().find(|m| m.id == *mid) {
            for &(addr, byte) in bytes {
                if (addr as usize) < mem_r.bytes.len() {
                    mem_r.bytes[addr as usize] = byte;
                }
            }
        }
    }

    let out_l = eval_region(base_module, reg, &task.lhs, &env, heap_l);
    let out_r = eval_region(base_module, reg, &task.rhs, &env, heap_r);
    match (out_l, out_r) {
        (Ok((vl, hl)), Ok((vr, hr))) => {
            vl != vr || hl.memories != hr.memories || hl.globals != hr.globals
        }
        (Err(tl), Err(tr)) => tl != tr,
        _ => true,
    }
}

fn median(mut values: Vec<f64>) -> f64 {
    if values.is_empty() {
        return 0.0;
    }
    values.sort_by(|a, b| a.total_cmp(b));
    let n = values.len();
    if n % 2 == 1 {
        values[n / 2]
    } else {
        (values[n / 2 - 1] + values[n / 2]) / 2.0
    }
}

/// Runs the complete Step 5 Proof 2 Compute-Matched 3-Arm Ablation Benchmark.
pub fn run_proof2_ablation(cfg: &Proof2Config) -> Result<Proof2Report, BenchError> {
    let t_all = Instant::now();
    let (consolidated_reg, base_module, training) = build_and_consolidate_oms_registry(cfg)?;
    let helper_module = build_arm_b_helper_module(&base_module, &consolidated_reg);

    let held_out_specs = build_held_out_oms_suite();
    let mutant_specs = build_soundness_mutants();

    let mut held_out_tasks = Vec::with_capacity(held_out_specs.len());
    for task in &held_out_specs {
        let (arm_a, _) = run_arm_a(&base_module, &consolidated_reg, task, cfg.time_cap_ms)?;
        let (arm_b, _) = run_arm_b(&helper_module, task, cfg.time_cap_ms)?;
        let (arm_c, _) = run_arm_c(&base_module, &consolidated_reg, task, cfg)?;

        let speedup_vs_a = arm_a.elapsed_ms / arm_c.elapsed_ms.max(0.01);
        let speedup_vs_b = arm_b.elapsed_ms / arm_c.elapsed_ms.max(0.01);
        let law_fired_reuse = arm_c.verdict == ArmVerdict::Proved && !arm_c.laws_fired.is_empty();
        let cross_rung_reused = arm_c.verdict == ArmVerdict::Proved
            && (!arm_c.laws_fired.is_empty() || !arm_c.strata_reused.is_empty());

        held_out_tasks.push(Proof2TaskOutcome {
            id: task.id.into(),
            rung: task.rung,
            category: task.category.into(),
            is_mutant: false,
            arm_a,
            arm_b,
            arm_c,
            speedup_vs_a,
            speedup_vs_b,
            cross_rung_reused,
            law_fired_reuse,
            counterexample_confirmed_in_kernel: None,
        });
    }

    let mut soundness_mutants = Vec::with_capacity(mutant_specs.len());
    for mutant in &mutant_specs {
        let (arm_a, _) = run_arm_a(&base_module, &consolidated_reg, mutant, cfg.time_cap_ms)?;
        let (arm_b, _) = run_arm_b(&helper_module, mutant, cfg.time_cap_ms)?;
        let (arm_c, model_c) = run_arm_c(&base_module, &consolidated_reg, mutant, cfg)?;

        let confirmed = model_c
            .as_ref()
            .map(|m| confirm_counterexample_in_kernel(&base_module, &consolidated_reg, mutant, m));
        let speedup_vs_a = arm_a.elapsed_ms / arm_c.elapsed_ms.max(0.01);
        let speedup_vs_b = arm_b.elapsed_ms / arm_c.elapsed_ms.max(0.01);

        soundness_mutants.push(Proof2TaskOutcome {
            id: mutant.id.into(),
            rung: mutant.rung,
            category: mutant.category.into(),
            is_mutant: true,
            arm_a,
            arm_b,
            arm_c,
            speedup_vs_a,
            speedup_vs_b,
            cross_rung_reused: false,
            law_fired_reuse: false,
            counterexample_confirmed_in_kernel: confirmed,
        });
    }

    let held_out_total = held_out_tasks.len();
    let arm_a_solved =
        held_out_tasks.iter().filter(|t| t.arm_a.verdict == ArmVerdict::Proved).count();
    let arm_b_solved =
        held_out_tasks.iter().filter(|t| t.arm_b.verdict == ArmVerdict::Proved).count();
    let arm_c_solved =
        held_out_tasks.iter().filter(|t| t.arm_c.verdict == ArmVerdict::Proved).count();
    let arm_a_timeouts =
        held_out_tasks.iter().filter(|t| t.arm_a.verdict == ArmVerdict::Timeout).count();
    let arm_b_timeouts =
        held_out_tasks.iter().filter(|t| t.arm_b.verdict == ArmVerdict::Timeout).count();
    let arm_c_timeouts =
        held_out_tasks.iter().filter(|t| t.arm_c.verdict == ArmVerdict::Timeout).count();

    let median_speedup_vs_a = median(held_out_tasks.iter().map(|t| t.speedup_vs_a).collect());
    let median_speedup_vs_b = median(held_out_tasks.iter().map(|t| t.speedup_vs_b).collect());

    let cross_rung_reuse_count = held_out_tasks.iter().filter(|t| t.cross_rung_reused).count();
    let law_firing_reuse_count = held_out_tasks.iter().filter(|t| t.law_fired_reuse).count();
    let cross_rung_reuse_rate = cross_rung_reuse_count as f64 / held_out_total.max(1) as f64;
    let law_firing_reuse_rate = law_firing_reuse_count as f64 / held_out_total.max(1) as f64;

    let mutants_total = soundness_mutants.len();
    let mutants_falsified_arm_a =
        soundness_mutants.iter().filter(|m| m.arm_a.verdict == ArmVerdict::Falsified).count();
    let mutants_falsified_arm_b =
        soundness_mutants.iter().filter(|m| m.arm_b.verdict == ArmVerdict::Falsified).count();
    let mutants_falsified_arm_c =
        soundness_mutants.iter().filter(|m| m.arm_c.verdict == ArmVerdict::Falsified).count();

    // Any mutant returning `Proved` on any arm or any counterexample rejected by kernel is unsound!
    let false_proved_count = soundness_mutants
        .iter()
        .filter(|m| {
            m.arm_a.verdict == ArmVerdict::Proved
                || m.arm_b.verdict == ArmVerdict::Proved
                || m.arm_c.verdict == ArmVerdict::Proved
        })
        .count();
    let unconfirmed_cex = soundness_mutants
        .iter()
        .filter(|m| m.counterexample_confirmed_in_kernel == Some(false))
        .count();

    let scorecard = Proof2Scorecard {
        held_out_total,
        arm_a_solved,
        arm_b_solved,
        arm_c_solved,
        arm_a_timeouts,
        arm_b_timeouts,
        arm_c_timeouts,
        median_speedup_vs_a,
        median_speedup_vs_b,
        cross_rung_reuse_count,
        cross_rung_reuse_rate,
        law_firing_reuse_count,
        law_firing_reuse_rate,
        mutants_total,
        mutants_falsified_arm_a,
        mutants_falsified_arm_b,
        mutants_falsified_arm_c,
        false_proved_count,
        unsound_admissions: training.unsound_admissions + false_proved_count + unconfirmed_cex,
    };

    Ok(Proof2Report {
        config: cfg.clone(),
        training,
        held_out_tasks,
        soundness_mutants,
        scorecard,
        total_elapsed_ms: t_all.elapsed().as_secs_f64() * 1000.0,
    })
}

/// Invokes the live `target/release/gnomon profile` binary across the 6 `s4_3_perf_opt_pairs.rs`
/// ref-vs-opt OMS pairs on both `x64 (skylake)` and `arm64 (neoverse-v2)`.
pub fn run_s4_3_profile_summary(
    gnomon_bin: &Path,
    s4_3_src: &Path,
) -> Result<Vec<ProfilePairSummary>, String> {
    if !gnomon_bin.exists() {
        return Err(format!("gnomon binary not found at {}", gnomon_bin.display()));
    }
    if !s4_3_src.exists() {
        return Err(format!("s4_3 source not found at {}", s4_3_src.display()));
    }

    let pairs = [
        ("1. Barrett Fastmod", "oms_bucket_ref", "oms_bucket_opt"),
        ("2. SWAR FIX Digits", "oms_fix_digits_ref", "oms_fix_digits_opt"),
        ("3. Hash Unroll (12x->4x)", "oms_hash_mix_12x_spill", "oms_hash_mix_4x"),
        ("4. Branchless Risk FSM", "oms_risk_fsm_ref", "oms_risk_fsm_opt"),
        ("5. Zero-Copy OUCH 48B", "oms_ouch_pack_ref", "oms_ouch_pack_opt"),
        ("6. 4-Lane VWAP SIMD", "oms_vwap_scalar_ref", "oms_vwap_vec_opt"),
    ];

    let mut out = Vec::with_capacity(pairs.len());
    for (label, ref_entry, opt_entry) in pairs {
        let output = Command::new(gnomon_bin)
            .arg("profile")
            .arg(s4_3_src)
            .arg("--entry")
            .arg(ref_entry)
            .arg("--opt-entry")
            .arg(opt_entry)
            .arg("--targets")
            .arg("x64,arm64")
            .output()
            .map_err(|e| format!("failed to spawn gnomon profile: {e}"))?;
        if !output.status.success() {
            return Err(format!(
                "gnomon profile failed for {ref_entry} vs {opt_entry}: {}",
                String::from_utf8_lossy(&output.stderr)
            ));
        }

        let val: serde_json::Value = serde_json::from_slice(&output.stdout)
            .map_err(|e| format!("invalid gnomon profile JSON for {ref_entry}: {e}"))?;
        let deltas = val["comparison"]["target_deltas"]
            .as_array()
            .ok_or_else(|| format!("missing comparison.target_deltas for {ref_entry}"))?;

        let find_arch = |arch: &str| {
            deltas
                .iter()
                .find(|d| d["arch"].as_str() == Some(arch))
                .ok_or_else(|| format!("missing {arch} delta for {ref_entry}"))
        };
        let x64 = find_arch("x64")?;
        let arm64 = find_arch("arm64")?;

        out.push(ProfilePairSummary {
            label: label.into(),
            ref_entry: ref_entry.into(),
            opt_entry: opt_entry.into(),
            x64_cycle_speedup: x64["cycle_speedup"].as_f64().unwrap_or(1.0),
            x64_rthroughput_speedup: x64["rthroughput_speedup"].as_f64().unwrap_or(1.0),
            x64_branch_delta: x64["branch_delta"].as_i64().unwrap_or(0),
            x64_div_delta: x64["div_delta"].as_i64().unwrap_or(0),
            x64_spill_delta: x64["spill_delta"].as_i64().unwrap_or(0),
            arm64_cycle_speedup: arm64["cycle_speedup"].as_f64().unwrap_or(1.0),
            arm64_rthroughput_speedup: arm64["rthroughput_speedup"].as_f64().unwrap_or(1.0),
            arm64_branch_delta: arm64["branch_delta"].as_i64().unwrap_or(0),
            arm64_div_delta: arm64["div_delta"].as_i64().unwrap_or(0),
            arm64_simd_delta: arm64["simd_delta"].as_i64().unwrap_or(0),
        });
    }

    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn arms_a_b_c_are_bit_identical_on_concrete_inputs() {
        let cfg = Proof2Config::default();
        let (reg, base_module, _) =
            build_and_consolidate_oms_registry(&cfg).expect("build consolidated OMS registry");
        let helper_module = build_arm_b_helper_module(&base_module, &reg);
        let empty = StratumRegistry::new();

        for task in build_held_out_oms_suite() {
            let env: Vec<(ValId, Val)> = task
                .params
                .iter()
                .enumerate()
                .map(|(i, &(vid, ty))| {
                    let v = match ty {
                        ValType::I32 => Val::I32((i as i32 + 1) * 17),
                        ValType::I64 => Val::I64(0x1234_5678_9abc_def0_u64.wrapping_add(i as u64 * 97) as i64),
                        ValType::F32 => Val::F32((100.25f32 + i as f32).to_bits()),
                        ValType::F64 => Val::F64((100.25f64 + i as f64).to_bits()),
                        ValType::V128 => Val::V128(0x3f80_0000_4000_0000_4040_0000_4080_0000),
                    };
                    (vid, v)
                })
                .collect();

            let mut nv_l = 1_000u32;
            let flat_l = reg.lower_region_to_layer0(&task.lhs, &mut nv_l).unwrap();
            let mut nv_r = 1_000u32;
            let flat_r = reg.lower_region_to_layer0(&task.rhs, &mut nv_r).unwrap();

            let helper_l = rewrite_strata_calls_to_funcs(&task.lhs);
            let helper_r = rewrite_strata_calls_to_funcs(&task.rhs);

            let run = |m: &Module, r: &StratumRegistry, reg_ir: &Region| {
                let mut heap = HeapState::from_module(m, 1_000_000).unwrap();
                // Seed deterministic non-zero bytes in MemId(0) & MemId(1) so loads are non-trivial.
                for mem in &mut heap.memories {
                    for (idx, b) in mem.bytes.iter_mut().take(512).enumerate() {
                        *b = ((idx * 37 + mem.id.0 as usize * 13) & 0xFF) as u8;
                    }
                }
                eval_region(m, r, reg_ir, &env, heap).expect("concrete eval must succeed")
            };

            let (va_l, ha_l) = run(&base_module, &empty, &flat_l);
            let (va_r, ha_r) = run(&base_module, &empty, &flat_r);
            let (vb_l, hb_l) = run(&helper_module, &empty, &helper_l);
            let (vb_r, hb_r) = run(&helper_module, &empty, &helper_r);
            let (vc_l, hc_l) = run(&base_module, &reg, &task.lhs);
            let (vc_r, hc_r) = run(&base_module, &reg, &task.rhs);

            assert_eq!(va_l, va_r, "{}: Arm A LHS != RHS", task.id);
            assert_eq!(ha_l.memories, ha_r.memories, "{}: Arm A mem LHS != RHS", task.id);
            assert_eq!(va_l, vb_l, "{}: Arm A != Arm B (LHS)", task.id);
            assert_eq!(vb_l, vb_r, "{}: Arm B LHS != RHS", task.id);
            assert_eq!(hb_l.memories, hb_r.memories, "{}: Arm B mem LHS != RHS", task.id);
            assert_eq!(va_l, vc_l, "{}: Arm A != Arm C (LHS)", task.id);
            assert_eq!(vc_l, vc_r, "{}: Arm C LHS != RHS", task.id);
            assert_eq!(hc_l.memories, hc_r.memories, "{}: Arm C mem LHS != RHS", task.id);
            assert_eq!(ha_l.memories, hb_l.memories, "{}: Arm A != Arm B mem", task.id);
            assert_eq!(ha_l.memories, hc_l.memories, "{}: Arm A != Arm C mem", task.id);
        }
    }
}

