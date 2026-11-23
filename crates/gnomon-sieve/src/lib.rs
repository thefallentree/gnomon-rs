#![forbid(unsafe_code)]

//! Workstream 1C & 2A interface: `egglog` v3.0 regional simplification,
//! `Bitwuzla` `QF_ABV` SMT oracle, and `stitch_core` consolidation.

use gnomon_kernel::{MemId, Module, Region, StratumRegistry, Val, ValId, VcObligation};

pub mod consolidate;
pub mod eqsat;
pub mod smt_bitwuzla;
mod smt_ir;
pub mod smt_pipe;

pub use consolidate::{
    ConsolidationConfig, ConsolidationReport, DiscoveredAbstraction, LawRedundancyReport,
    OpMdlReport, consolidate_registry, discover_candidate_inventions, encode_region_as_stitch_expr,
    render_autodoc,
};
pub use eqsat::EgglogSimplifier;
pub use smt_bitwuzla::BitwuzlaNativeBackend;
pub use smt_pipe::BitwuzlaPipeBackend;

#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum SieveError {
    #[error("SMT encoding error: {0}")]
    EncodingError(String),
    #[error("SMT solver error: {0}")]
    SolverError(String),
    #[error("egglog simplification error: {0}")]
    EqSatError(String),
    #[error("unimplemented sieve feature: {0}")]
    Unimplemented(&'static str),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SmtModel {
    pub scalar_values: Vec<(ValId, Val)>,
    pub memory_bytes: Vec<(MemId, Vec<(u32, u8)>)>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SmtResult {
    Unsat,
    Sat(SmtModel),
    Unknown(String),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EqSatConfig {
    pub max_iters: usize,
    pub max_nodes: usize,
    pub timeout_ms: u64,
}

impl Default for EqSatConfig {
    fn default() -> Self {
        Self { max_iters: 5, max_nodes: 5_000, timeout_ms: 500 }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EqSatReport {
    pub iters_run: usize,
    pub laws_fired: Vec<String>,
    pub nodes_before: usize,
    pub nodes_after: usize,
}

/// Abstract SMT backend encoding loop-free `GnomonIR` obligations into `QF_ABV`.
pub trait SmtBackend {
    fn check_vc(
        &mut self,
        module: &Module,
        registry: &StratumRegistry,
        vc: &VcObligation,
    ) -> Result<SmtResult, SieveError>;

    fn check_equivalence(
        &mut self,
        module: &Module,
        registry: &StratumRegistry,
        lhs: &Region,
        rhs: &Region,
        precondition: Option<&Region>,
    ) -> Result<SmtResult, SieveError>;
}
