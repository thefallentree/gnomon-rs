#![forbid(unsafe_code)]

//! Phase 2 Gnomon CLI, `.ir`/`.wasm` codec, 3-stage verification engine, and single
//! `rmcp` + `tokio` MCP server exposing the 6 atomic Gnomon tools.

pub mod engine;
pub mod ir_codec;
pub mod mcp_server;

pub use engine::{
    CheckGoalOutput, CounterexampleJson, DefineOpOutput, EngineSnapshot, FuncSummary,
    GnomonEngine, LiftCheckOutput, MemoryDiffEntry, ProveLawOutput, RunTraceOutput,
};
pub use ir_codec::{
    InputType, IrBinOp, IrCallTarget, IrDocument, IrEffectOp, IrFuncDef, IrGlobalDef,
    IrHostContract, IrLaw, IrLawKind, IrMemWidth, IrMemoryDef, IrModule, IrOffsetRange, IrOp,
    IrRegion, IrSliceBound, IrStmt, IrStratum, IrStratumOp, IrTrapCode, IrTypedVar, IrUnOp, IrVal,
    IrValType, LoadedArtifact, load_artifact_bytes, load_artifact_from_mcp_arg, read_input_bytes,
    resolve_input_type,
};
pub use mcp_server::GnomonMcpServer;

pub const MCP_TOOL_NAMES: [&str; 6] = [
    "gnomon_lift_check",
    "gnomon_run_trace",
    "gnomon_define_op",
    "gnomon_prove_law",
    "gnomon_check_goal",
    "gnomon_consolidate",
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
