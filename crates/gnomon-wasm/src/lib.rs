#![forbid(unsafe_code)]

//! Workstream 1B interface: lossless `.wasm` <-> `GnomonIR` lifter/emitter
//! and microsecond `wasmtime` Stage-1 falsifier.

mod emit;
mod fuzz;
mod lift;

use gnomon_kernel::{Module, TrapCode, Val};
use thiserror::Error;

pub use emit::emit_wasm;
pub use fuzz::{
    differential_check, fuzz_equivalence, fuzz_equivalence_by_name, run_wasmtime_func,
    verify_round_trip,
};
pub use lift::lift_wasm;

#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum WasmError {
    #[error("wasm parse error: {0}")]
    ParseError(String),
    #[error("wasm validation error: {0}")]
    ValidationError(String),
    #[error("unsupported wasm feature: {0}")]
    UnsupportedFeature(String),
    #[error("unimplemented: {0}")]
    Unimplemented(&'static str),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FuzzConfig {
    pub total_vectors: usize,
    pub fuel_per_run: u64,
    pub seed: u64,
}

impl Default for FuzzConfig {
    fn default() -> Self {
        Self {
            total_vectors: 50_000,
            fuel_per_run: 100_000,
            seed: 0x5EED_9E37_79B9_7F4A,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExecOutcome {
    Values(Vec<Val>),
    Trap(TrapCode),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Counterexample {
    pub inputs: Vec<Val>,
    pub memory_snapshots: Vec<Vec<u8>>,
    pub lhs_outcome: ExecOutcome,
    pub rhs_outcome: ExecOutcome,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FuzzOutcome {
    NoCounterexample {
        vectors_tested: usize,
        elapsed_micros: u64,
    },
    Falsified(Counterexample),
}

/// Convenience check confirming an already-lifted `Module` compiles cleanly back to Wasm.
pub fn validate_roundtrip_ir(module: &Module) -> Result<Vec<u8>, WasmError> {
    emit_wasm(module)
}
