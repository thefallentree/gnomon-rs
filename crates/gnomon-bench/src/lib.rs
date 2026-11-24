#![forbid(unsafe_code)]

//! Workstream 1D (30+30 Wasm corpus) and Phase 2 (60-task 4-rung flywheel) benchmark harness.

pub mod corpus;
pub mod phase1;
pub mod proof2;
pub mod wasm_smith;

use serde::{Deserialize, Serialize};
use thiserror::Error;

pub use corpus::{
    CorpusManifestEntry, WasmBinarySummary, corpus_cases, corpus_manifest, inspect_wasm_binary,
};
pub use phase1::{
    CaseGateReport, Phase1Report, run_phase1_gate, run_phase1_gate_with_config,
    verify_counterexample_in_kernel,
};
pub use proof2::{
    ArmRunResult, ArmVerdict, DEFAULT_PROOF2_TIME_CAP_MS, ProfilePairSummary, Proof2Config,
    Proof2Report, Proof2Scorecard, Proof2TaskOutcome, TrainingSummary, run_proof2_ablation,
    run_s4_3_profile_summary,
};
pub use wasm_smith::{
    DEFAULT_BASE_SEED, LatencyStats, WasmSmithFailure, WasmSmithGateConfig, WasmSmithGateReport,
    generate_wasm_for_attempt, gnomon_wasm_smith_config, run_wasm_smith_gate,
    scan_wasm_smith_gate,
};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CorpusCase {
    pub id: String,
    pub category: String,
    pub reference_wasm: Vec<u8>,
    pub mutant_wasm: Vec<u8>,
    pub bug_kind: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Serialize, Deserialize)]
pub struct Phase1Scorecard {
    pub round_trip_passed: usize,
    pub round_trip_total: usize,
    pub mutants_falsified: usize,
    pub mutants_total: usize,
    pub median_falsify_ms: f64,
    pub unsound_count: usize,
}

impl Phase1Scorecard {
    pub fn exit_gate_passed(&self) -> bool {
        self.round_trip_total >= 30
            && self.round_trip_passed == self.round_trip_total
            && self.mutants_total >= 30
            && self.mutants_falsified == self.mutants_total
            && self.median_falsify_ms < 50.0
            && self.unsound_count == 0
    }
}

#[derive(Debug, Error)]
pub enum BenchError {
    #[error("invalid Wasm binary: {0}")]
    InvalidWasm(String),
    #[error("Wasm lifter/fuzzer error: {0}")]
    Wasm(String),
    #[error("SMT solver error: {0}")]
    Sieve(String),
    #[error("kernel evaluation trap: {0:?}")]
    KernelTrap(gnomon_kernel::TrapCode),
}
