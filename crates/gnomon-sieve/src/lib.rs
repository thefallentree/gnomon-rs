#![forbid(unsafe_code)]

//! Workstream 1C & 2A interface: `egglog` v3.0 regional simplification,
//! `Bitwuzla` `QF_ABV` SMT oracle, and `stitch_core` consolidation.

use gnomon_kernel::{
    FuncDef, GlobalId, MemId, Module, Region, StratumRegistry, Val, ValId, ValType, VcObligation,
};

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
    pub global_values: Vec<(GlobalId, Val)>,
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

/// Specification of an application function/region contract verified by `SmtBackend::check_contract`.
///
/// ## Pre-state semantics
/// - `use_initial_state == false` (default — inductive preservation check):
///   mutable globals start as arbitrary fresh symbolic bit-vectors (immutable globals hold
///   `GlobalDef::init`), linear memories start as arbitrary fresh symbolic byte arrays with
///   symbolic page counts in `[min_pages, max_pages]`, and `invariant` (if provided) is
///   **assumed** on the pre-state and **asserted** on the post-state.
/// - `use_initial_state == true` (base-case / `init` check):
///   all globals start at their exact `GlobalDef::init` constants, linear memories start at
///   exact `min_pages * 65536` zeroed bytes with `MemoryDef::init_data` overlaid (matching
///   `gnomon_kernel::HeapState::from_module`), and `invariant` (if provided) is **NOT assumed**
///   on the pre-state (only **asserted** on the post-state so `init` cannot be proved vacuously).
///
/// ## `ValId` binding conventions
/// - `params`: symbolic inputs bound in `env` for `entry` (and `requires` when `requires_params`
///   is `None`).
/// - `requires_params`: when `Some(p)`, must match `params` in length and types; binds the
///   symbolic inputs to `p`'s `ValId`s when evaluating `requires`.
/// - `ensures_params`:
///   - When `Some(p)`:
///     - If `p.len() == params.len() + results.len()`, binds `(entry_args..., entry_results...)`
///       sequentially to `p`'s `ValId`s (checking exact types).
///     - Else if `p.len() == results.len()`, binds `(entry_results...)` sequentially to `p`'s
///       `ValId`s (checking exact types).
///     - Else if `p.is_empty()`, binds no scalar parameters (state-only postcondition).
///     - Otherwise returns `SieveError::EncodingError`.
///   - When `None`: binds `params` to `entry_args`, and binds `entry_results[i]` to
///     `ValId(base + i)` where `base = params.iter().map(|(v, _)| v.0 + 1).max().unwrap_or(0)`
///     (matching standard 0-based Wasm-lifted `FuncDef` params `ValId(0..k)` -> results
///     `ValId(k..k+r)`).
/// - `invariant`: evaluated with an empty scalar `env` (0 params) on `pre_state` (when
///   `!use_initial_state`) and `post_state`; must yield a single non-zero `i32` without trapping.
#[derive(Clone, Debug)]
pub struct ContractSpec<'a> {
    pub params: &'a [(ValId, ValType)],
    pub results: &'a [ValType],
    pub entry: &'a Region,
    pub requires: Option<&'a Region>,
    pub requires_params: Option<&'a [(ValId, ValType)]>,
    pub ensures: Option<&'a Region>,
    pub ensures_params: Option<&'a [(ValId, ValType)]>,
    pub invariant: Option<&'a Region>,
    pub check_trap_free: bool,
    pub use_initial_state: bool,
}

impl<'a> ContractSpec<'a> {
    /// Creates a contract specification for a raw `Region` with default inductive settings
    /// (`check_trap_free: true`, `use_initial_state: false`).
    pub fn new(
        params: &'a [(ValId, ValType)],
        results: &'a [ValType],
        entry: &'a Region,
    ) -> Self {
        Self {
            params,
            results,
            entry,
            requires: None,
            requires_params: None,
            ensures: None,
            ensures_params: None,
            invariant: None,
            check_trap_free: true,
            use_initial_state: false,
        }
    }

    /// Creates a contract specification targeting a `FuncDef` with default inductive settings
    /// (`check_trap_free: true`, `use_initial_state: false`).
    pub fn from_func(func: &'a FuncDef) -> Self {
        Self::new(&func.params, &func.results, &func.body)
    }

    pub fn with_requires(mut self, requires: &'a Region) -> Self {
        self.requires = Some(requires);
        self
    }

    pub fn with_requires_func(mut self, func: &'a FuncDef) -> Self {
        self.requires = Some(&func.body);
        self.requires_params = Some(&func.params);
        self
    }

    pub fn with_ensures(mut self, ensures: &'a Region) -> Self {
        self.ensures = Some(ensures);
        self
    }

    pub fn with_ensures_func(mut self, func: &'a FuncDef) -> Self {
        self.ensures = Some(&func.body);
        self.ensures_params = Some(&func.params);
        self
    }

    pub fn with_invariant(mut self, invariant: &'a Region) -> Self {
        self.invariant = Some(invariant);
        self
    }

    pub fn with_invariant_func(mut self, func: &'a FuncDef) -> Self {
        self.invariant = Some(&func.body);
        self
    }

    pub fn with_check_trap_free(mut self, check_trap_free: bool) -> Self {
        self.check_trap_free = check_trap_free;
        self
    }

    pub fn with_initial_state(mut self, use_initial_state: bool) -> Self {
        self.use_initial_state = use_initial_state;
        self
    }
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

    fn check_contract(
        &mut self,
        module: &Module,
        registry: &StratumRegistry,
        contract: &ContractSpec<'_>,
    ) -> Result<SmtResult, SieveError>;
}
