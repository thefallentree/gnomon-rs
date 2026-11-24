#![forbid(unsafe_code)]

//! Phase 2 Gnomon CLI, `.ir`/`.wasm` codec, 3-stage verification engine, and single
//! `rmcp` + `tokio` MCP server exposing the 7 atomic Gnomon tools.

pub mod engine;
pub mod ir_codec;
pub mod mcp_server;
pub mod rust_bridge;

pub use engine::{
    CheckContractOutput, CheckContractRequest, CheckGoalOutput, ContractCounterexampleJson,
    ContractMemoryBytesJson, ContractOpResult, ContractPred, CounterexampleJson, DefineOpOutput,
    EngineSnapshot, FuncSummary, GnomonEngine, LiftCheckOutput, MemoryDiffEntry, ProveLawOutput,
    RunTraceOutput,
};
pub use ir_codec::{
    InputType, IrBinOp, IrCallTarget, IrDocument, IrEffectOp, IrFuncDef, IrGlobalDef,
    IrHostContract, IrLaw, IrLawKind, IrMemWidth, IrMemoryDef, IrModule, IrOffsetRange, IrOp,
    IrRegion, IrSliceBound, IrStmt, IrStratum, IrStratumOp, IrTrapCode, IrTypedVar, IrUnOp, IrVal,
    IrValType, LoadedArtifact, load_artifact_bytes, load_artifact_bytes_with_registry,
    load_artifact_from_mcp_arg, load_artifact_from_mcp_arg_with_registry, read_input_bytes,
    resolve_input_type,
};
pub use mcp_server::GnomonMcpServer;
pub use rust_bridge::{
    bind_stratum_imports, compile_rust_to_wasm, compile_rust_to_wasm_with_registry,
    generate_strata_rs, looks_like_rust_source, lower_module_strata, module_has_stratum_calls,
    module_has_stratum_imports, normalize_nested_returns_for_stratum, sanitize_rust_ident,
};

pub const MCP_TOOL_NAMES: [&str; 7] = [
    "gnomon_lift_check",
    "gnomon_run_trace",
    "gnomon_define_op",
    "gnomon_prove_law",
    "gnomon_check_goal",
    "gnomon_consolidate",
    "gnomon_check_contract",
];

#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum GnomonError {
    #[error("I/O error: {0}")]
    Io(String),
    #[error("invalid input: {0}")]
    InvalidInput(String),
    #[error("wasm error: {0}")]
    Wasm(String),
    #[error("kernel error: {0}")]
    Kernel(String),
    #[error("registry error: {0}")]
    Registry(String),
    #[error("sieve error: {0}")]
    Sieve(String),
    #[error("internal error: {0}")]
    Internal(String),
}
