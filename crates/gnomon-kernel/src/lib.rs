#![no_std]
#![forbid(unsafe_code)]

//! Trusted Computing Base (TCB) for Project Gnomon (`gnomon-rs`).
//! Contains the `GnomonIR` data model, deterministic small-step reference
//! interpreter, loop VC splitter, and Stratum admission registry.

extern crate alloc;

pub mod eval;
pub mod ir;
#[cfg(kani)]
mod kani_proofs;
pub mod registry;
pub mod vc;

pub use eval::{
    HeapState, MAX_CALL_DEPTH, MAX_WASM_PAGES, MemoryState, WASM_PAGE_SIZE, eval_func, eval_region,
};
pub use ir::*;
pub use registry::{Law, LawKind, RegistryError, Stratum, StratumOp, StratumRegistry};
pub use vc::{
    LoopVcs, VcError, VcEvalResult, VcKind, VcObligation, eval_vc, remap_region_vals,
    split_invariant_loop, validate_read_only, validate_read_only_with_registry,
};
