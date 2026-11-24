//! Single MCP server (`rmcp` + `tokio` stdio) exposing all 7 atomic Gnomon tools.

use std::path::PathBuf;
use std::sync::{Arc, Mutex};

use gnomon_kernel::{MemId, ValId};
use gnomon_sieve::{ConsolidationConfig, ConsolidationReport, SliceBoundExpr, SliceFrameSpec};
use rmcp::handler::server::router::tool::ToolRouter;
use rmcp::handler::server::wrapper::Parameters;
use rmcp::model::{CallToolResult, ContentBlock, Implementation, ServerCapabilities, ServerConfig};
use rmcp::{ErrorData as McpError, ServerHandler, ServiceExt, tool, tool_handler, tool_router};
use serde::{Deserialize, Serialize};

use crate::GnomonError;
use crate::engine::{CheckContractRequest, ContractPred, GnomonEngine, prepare_goal_artifacts};
use crate::ir_codec::{InputType, IrLawKind, IrTypedVar, IrVal, IrValType, LoadedArtifact};

/// Single stateful Gnomon MCP Server serving all 7 verification & abstraction tools.
#[derive(Clone)]
pub struct GnomonMcpServer {
    engine: Arc<Mutex<GnomonEngine>>,
    state_path: Option<PathBuf>,
    tool_router: ToolRouter<Self>,
}

impl GnomonMcpServer {
    pub fn new(state_path: Option<PathBuf>) -> Result<Self, GnomonError> {
        let engine = match &state_path {
            Some(p) => GnomonEngine::load_state_file(p)?,
            None => GnomonEngine::new(),
        };
        Ok(Self {
            engine: Arc::new(Mutex::new(engine)),
            state_path,
            tool_router: Self::tool_router(),
        })
    }

    async fn with_engine<F, T>(&self, persist: bool, f: F) -> Result<T, McpError>
    where
        F: FnOnce(&mut GnomonEngine) -> Result<T, GnomonError> + Send + 'static,
        T: Send + 'static,
    {
        let engine = Arc::clone(&self.engine);
        let state_path = self.state_path.clone();
        tokio::task::spawn_blocking(move || {
            let mut eng = engine
                .lock()
                .map_err(|_| McpError::internal_error("engine mutex poisoned", None))?;
            let out = f(&mut eng).map_err(map_err)?;
            if persist
                && let Some(ref p) = state_path
            {
                eng.save_state_file(p)
                    .map_err(|e| McpError::internal_error(e.to_string(), None))?;
            }
            Ok(out)
        })
        .await
        .map_err(|e| McpError::internal_error(format!("worker task panicked: {e}"), None))?
    }

    /// Runs the MCP server over standard input/output (newline-delimited JSON-RPC 2.0).
    pub async fn serve_stdio(self) -> Result<(), GnomonError> {
        let transport = rmcp::transport::stdio();
        let service = self
            .serve(transport)
            .await
            .map_err(|e| GnomonError::Internal(format!("MCP server init failed: {e}")))?;
        service
            .waiting()
            .await
            .map_err(|e| GnomonError::Internal(format!("MCP server runtime error: {e}")))?;
        Ok(())
    }
}

fn json_ok<T: serde::Serialize>(value: &T) -> Result<CallToolResult, McpError> {
    let text = serde_json::to_string_pretty(value)
        .map_err(|e| McpError::internal_error(format!("JSON serialize failed: {e}"), None))?;
    Ok(CallToolResult::success(vec![ContentBlock::text(text)]))
}

fn map_err(e: GnomonError) -> McpError {
    match e {
        GnomonError::InvalidInput(_) | GnomonError::Wasm(_) | GnomonError::Registry(_) => {
            McpError::invalid_params(e.to_string(), None)
        }
        GnomonError::Io(_)
        | GnomonError::Kernel(_)
        | GnomonError::Sieve(_)
        | GnomonError::Internal(_) => McpError::internal_error(e.to_string(), None),
    }
}

fn default_input_type() -> InputType {
    InputType::Auto
}

fn default_fuel() -> u64 {
    100_000
}

fn default_timeout_ms() -> u64 {
    5_000
}

fn default_true() -> bool {
    true
}

#[derive(Debug, Deserialize, schemars::JsonSchema)]
pub struct LiftCheckParams {
    /// Inline `.ir` JSON string, strict `#![no_std]` Rust source, or base64/hex encoded `.wasm` bytes.
    pub content: Option<String>,
    /// Optional local file path to a `.wasm`, `.rs`, or `.ir` file.
    pub path: Option<String>,
    /// Input format: `auto`, `wasm`, `ir`, or `rust`.
    #[serde(default = "default_input_type")]
    pub input_type: InputType,
    /// Include full serialized `.ir` document in the response.
    #[serde(default)]
    pub include_ir: bool,
}

#[derive(Debug, Deserialize, schemars::JsonSchema)]
pub struct RunTraceParams {
    /// Optional inline `.ir` JSON, strict `#![no_std]` Rust, or base64/hex `.wasm` to run (defaults to last lifted module).
    pub content: Option<String>,
    /// Optional local file path to `.wasm`, `.rs`, or `.ir`.
    pub path: Option<String>,
    /// Input format: `auto`, `wasm`, `ir`, or `rust`.
    #[serde(default = "default_input_type")]
    pub input_type: InputType,
    /// Optional entry function name (defaults to func 0).
    pub entry: Option<String>,
    /// Concrete input values, e.g. `[{"ty":"i32","val":7}]`.
    #[serde(default)]
    pub inputs: Vec<IrVal>,
    /// Deterministic execution fuel budget.
    #[serde(default = "default_fuel")]
    pub fuel: u64,
}

#[derive(Debug, Deserialize, schemars::JsonSchema)]
pub struct DefineOpParams {
    /// Name of the Layer-k Stratum op.
    pub name: String,
    /// Optional entry function name inside a multi-function `.wasm`/`.rs` module (defaults to matching `name`, else func 0).
    #[serde(default)]
    pub entry: Option<String>,
    /// Strictly positive DAG layer (`>= 1`).
    pub layer: u16,
    /// Typed parameter list `[{"id":0,"ty":"i32"}]`.
    #[serde(default)]
    pub params: Vec<IrTypedVar>,
    /// Result types `["i32"]`.
    #[serde(default)]
    pub results: Vec<IrValType>,
    /// Inline `.ir` JSON, strict `#![no_std]` Rust, or base64/hex `.wasm` defining the op body.
    pub body_content: Option<String>,
    /// Optional local file path to `.wasm`, `.rs`, or `.ir` defining the op body.
    pub body_path: Option<String>,
    /// Input format for body: `auto`, `wasm`, `ir`, or `rust`.
    #[serde(default = "default_input_type")]
    pub input_type: InputType,
    /// Human-readable docstring for AutoDoc prompt cache.
    #[serde(default)]
    pub docstring: String,
    /// Optional explicit numeric StratumId.
    pub stratum_id: Option<u32>,
}

#[derive(Debug, Deserialize, schemars::JsonSchema)]
pub struct ProveLawParams {
    /// Owning Stratum op name or numeric ID.
    pub op: String,
    /// Law name.
    pub name: String,
    /// Law kind: `"algebraic"` (default) or `"memory_frame"`.
    #[serde(default)]
    pub kind: Option<String>,
    /// For `"memory_frame"` laws, the `MemId` that must remain untouched.
    pub untouched_mem: Option<u16>,
    /// Quantified parameters `[{"id":0,"ty":"i32"}]`.
    #[serde(default)]
    pub params: Vec<IrTypedVar>,
    /// LHS pattern (`.ir` JSON, strict `#![no_std]` Rust, or base64/hex `.wasm`).
    pub lhs_content: Option<String>,
    pub lhs_path: Option<String>,
    #[serde(default)]
    pub lhs_entry: Option<String>,
    /// RHS pattern (`.ir` JSON, strict `#![no_std]` Rust, or base64/hex `.wasm`; omitted for `memory_frame` laws).
    pub rhs_content: Option<String>,
    pub rhs_path: Option<String>,
    #[serde(default)]
    pub rhs_entry: Option<String>,
    /// Optional precondition region (`.ir` JSON, `.rs`, or `.wasm`).
    pub pre_content: Option<String>,
    pub pre_path: Option<String>,
    #[serde(default)]
    pub pre_entry: Option<String>,
    /// Input format: `auto`, `wasm`, `ir`, or `rust`.
    #[serde(default = "default_input_type")]
    pub input_type: InputType,
}

#[derive(Debug, Deserialize, schemars::JsonSchema)]
pub struct CheckGoalParams {
    /// Candidate region/module (`.ir` JSON, strict `#![no_std]` Rust, or base64/hex `.wasm`).
    pub candidate_content: Option<String>,
    pub candidate_path: Option<String>,
    #[serde(default)]
    pub candidate_entry: Option<String>,
    /// Specification region/module (`.ir` JSON, strict `#![no_std]` Rust, or base64/hex `.wasm`).
    pub spec_content: Option<String>,
    pub spec_path: Option<String>,
    #[serde(default)]
    pub spec_entry: Option<String>,
    /// Optional precondition region.
    pub pre_content: Option<String>,
    pub pre_path: Option<String>,
    #[serde(default)]
    pub pre_entry: Option<String>,
    /// Optional explicit postcondition for `InvariantLoop` VC splitting.
    pub post_content: Option<String>,
    pub post_path: Option<String>,
    #[serde(default)]
    pub post_entry: Option<String>,
    /// Free parameters `[{"id":0,"ty":"i32"}]`.
    #[serde(default)]
    pub params: Vec<IrTypedVar>,
    /// Input format: `auto`, `wasm`, `ir`, or `rust`.
    #[serde(default = "default_input_type")]
    pub input_type: InputType,
    /// EqSat / solver budget in milliseconds.
    #[serde(default = "default_timeout_ms")]
    pub timeout_ms: u64,
    /// Ignore dead shadow-stack bytes below SP_in (`Global(0)`) while proving SP preservation and exact live-memory equivalence.
    #[serde(default)]
    pub ignore_dead_stack: bool,
}

/// Optional intra-memory write-frame restriction for `gnomon_check_contract`.
#[derive(Clone, Debug, Default, Deserialize, Serialize, schemars::JsonSchema)]
pub struct SliceFrameParam {
    /// Target linear memory ID (defaults to `0`).
    #[serde(default)]
    pub mem: u16,
    /// When `true`, proves the function writes zero bytes to live memory (`base = 0, len = 0`).
    #[serde(default)]
    pub readonly: bool,
    /// 0-based `ValId` of an `i32` entry parameter giving the writable slice base address.
    pub base_param: Option<u32>,
    /// Constant 32-bit unsigned byte offset giving the writable slice base address.
    pub base_const: Option<u32>,
    /// 0-based `ValId` of an `i32` entry parameter giving the writable slice byte length.
    pub len_param: Option<u32>,
    /// Constant 32-bit unsigned byte length giving the writable slice byte length.
    pub len_const: Option<u32>,
}

impl SliceFrameParam {
    pub fn into_spec(self) -> Result<SliceFrameSpec, GnomonError> {
        let has_explicit = self.base_param.is_some()
            || self.base_const.is_some()
            || self.len_param.is_some()
            || self.len_const.is_some();
        if self.readonly {
            if has_explicit {
                return Err(GnomonError::InvalidInput(
                    "slice_frame: cannot combine 'readonly: true' with explicit base/len bounds"
                        .into(),
                ));
            }
            return Ok(SliceFrameSpec {
                mem: MemId(self.mem),
                base: SliceBoundExpr::Const(0),
                len: SliceBoundExpr::Const(0),
            });
        }
        let base = match (self.base_param, self.base_const) {
            (Some(p), None) => SliceBoundExpr::Param(ValId(p)),
            (None, Some(c)) => SliceBoundExpr::Const(c),
            (Some(_), Some(_)) => {
                return Err(GnomonError::InvalidInput(
                    "slice_frame: specify only one of 'base_param' or 'base_const'".into(),
                ));
            }
            (None, None) => {
                return Err(GnomonError::InvalidInput(
                    "slice_frame: must specify 'base_param', 'base_const', or 'readonly: true'"
                        .into(),
                ));
            }
        };
        let len = match (self.len_param, self.len_const) {
            (Some(p), None) => SliceBoundExpr::Param(ValId(p)),
            (None, Some(c)) => SliceBoundExpr::Const(c),
            (Some(_), Some(_)) => {
                return Err(GnomonError::InvalidInput(
                    "slice_frame: specify only one of 'len_param' or 'len_const'".into(),
                ));
            }
            (None, None) => {
                return Err(GnomonError::InvalidInput(
                    "slice_frame: must specify 'len_param', 'len_const', or 'readonly: true'"
                        .into(),
                ));
            }
        };
        Ok(SliceFrameSpec { mem: MemId(self.mem), base, len })
    }
}

#[derive(Debug, Deserialize, schemars::JsonSchema)]
pub struct ConsolidateParams {
    /// Additional verified solution `.ir` JSON or strict `#![no_std]` Rust strings to include in MDL scoring.
    #[serde(default)]
    pub solutions: Vec<String>,
    /// Minimum distinct solutions required to keep an op (default 2).
    pub min_solutions: Option<usize>,
    /// Max `egglog` steps for law redundancy pruning (default 3, clamped to 1..=3).
    pub max_derivation_steps: Option<usize>,
    /// When `true`, include auto-generated `#![no_std]` `strata.rs` bindings in `strata_rs`.
    #[serde(default)]
    pub emit_rust: bool,
}

#[derive(Debug, Serialize)]
struct ConsolidateMcpOutput {
    #[serde(flatten)]
    report: ConsolidationReport,
    #[serde(skip_serializing_if = "Option::is_none")]
    strata_rs: Option<String>,
}

#[derive(Debug, Deserialize, schemars::JsonSchema)]
pub struct CheckContractParams {
    /// Optional inline `.ir` JSON or base64/hex `.wasm` module/region (defaults to last lifted module).
    pub content: Option<String>,
    /// Optional local file path to a `.wasm` or `.ir` module/region.
    pub path: Option<String>,
    /// Input format: `auto`, `wasm`, or `ir`.
    #[serde(default = "default_input_type")]
    pub input_type: InputType,
    /// Single-op mode: entry function name inside the module (defaults to func 0 when `ops`/`init` are omitted).
    pub entry: Option<String>,
    /// Inductive suite mode: list of operation function names checked with `use_initial_state = false`.
    #[serde(default)]
    pub ops: Vec<String>,
    /// Inductive suite mode: optional initializer function name checked with `use_initial_state = true`.
    pub init: Option<String>,
    /// Precondition function name inside the target module (or entry function inside `requires_content`/`requires_path`).
    pub requires: Option<String>,
    /// Optional inline `.ir` JSON or base64/hex `.wasm` precondition artifact.
    pub requires_content: Option<String>,
    /// Optional local file path to a `.wasm` or `.ir` precondition artifact.
    pub requires_path: Option<String>,
    /// Postcondition function name inside the target module (or entry function inside `ensures_content`/`ensures_path`).
    pub ensures: Option<String>,
    /// Optional inline `.ir` JSON or base64/hex `.wasm` postcondition artifact.
    pub ensures_content: Option<String>,
    /// Optional local file path to a `.wasm` or `.ir` postcondition artifact.
    pub ensures_path: Option<String>,
    /// State invariant function name (0-arg `() -> i32`) inside the target module (or entry inside `invariant_content`/`invariant_path`).
    pub invariant: Option<String>,
    /// Optional inline `.ir` JSON or base64/hex `.wasm` invariant artifact.
    pub invariant_content: Option<String>,
    /// Optional local file path to a `.wasm` or `.ir` invariant artifact.
    pub invariant_path: Option<String>,
    /// Single-op mode: start from concrete initial state (`GlobalDef::init` + zeroed `min_pages` + `init_data`) and do NOT assume `invariant` on pre-state (default `false`).
    #[serde(default)]
    pub use_initial_state: bool,
    /// Require trap-freedom on assumption-satisfying paths (default `true`).
    #[serde(default = "default_true")]
    pub check_trap_free: bool,
    /// Ignore dead shadow-stack bytes below SP_in (`Global(0)`) while proving SP preservation.
    #[serde(default)]
    pub ignore_dead_stack: bool,
    /// Optional intra-memory write-frame restriction (`readonly: true`, or `base_param`/`base_const` + `len_param`/`len_const`, optional `mem`).
    #[serde(default)]
    pub slice_frame: Option<SliceFrameParam>,
    /// Bitwuzla per-check timeout budget in milliseconds (default `5000`).
    #[serde(default = "default_timeout_ms")]
    pub timeout_ms: u64,
}

fn load_mcp_contract_pred(
    eng: &GnomonEngine,
    name: Option<String>,
    content: Option<&str>,
    path: Option<&str>,
    input_type: InputType,
) -> Result<Option<ContractPred>, GnomonError> {
    if content.is_some() || path.is_some() {
        let (_, artifact) = eng.load_artifact_from_mcp_arg(content, path, input_type)?;
        Ok(Some(ContractPred::Artifact { artifact: Box::new(artifact), entry: name }))
    } else {
        Ok(name.map(ContractPred::FuncName))
    }
}

#[tool_router]
impl GnomonMcpServer {
    #[tool(
        name = "gnomon_lift_check",
        description = "Lift a .wasm module, strict #![no_std] Rust source, or .ir document into typed GnomonIR, bind stratum imports, check round-trip emission, and return static diagnostics."
    )]
    async fn gnomon_lift_check(
        &self,
        Parameters(p): Parameters<LiftCheckParams>,
    ) -> Result<CallToolResult, McpError> {
        let out = self
            .with_engine(true, move |eng| {
                let (detected, artifact) = eng.load_artifact_from_mcp_arg(
                    p.content.as_deref(),
                    p.path.as_deref(),
                    p.input_type,
                )?;
                eng.lift_check(detected, artifact, p.include_ir)
            })
            .await?;
        json_ok(&out)
    }

    #[tool(
        name = "gnomon_run_trace",
        description = "Execute a lifted module, strict #![no_std] Rust source, or .ir region on the deterministic gnomon-kernel interpreter, returning outputs, traps, fuel consumed, and sparse memory diff."
    )]
    async fn gnomon_run_trace(
        &self,
        Parameters(p): Parameters<RunTraceParams>,
    ) -> Result<CallToolResult, McpError> {
        let out = self
            .with_engine(false, move |eng| {
                let artifact = if p.content.is_some() || p.path.is_some() {
                    let (_, art) = eng.load_artifact_from_mcp_arg(
                        p.content.as_deref(),
                        p.path.as_deref(),
                        p.input_type,
                    )?;
                    Some(art)
                } else {
                    None
                };
                eng.run_trace(artifact, p.entry.as_deref(), &p.inputs, p.fuel)
            })
            .await?;
        json_ok(&out)
    }

    #[tool(
        name = "gnomon_define_op",
        description = "Register a candidate Layer-k Stratum op from .wasm, strict #![no_std] Rust, or .ir after gnomon-kernel DAG acyclicity and type validation."
    )]
    async fn gnomon_define_op(
        &self,
        Parameters(p): Parameters<DefineOpParams>,
    ) -> Result<CallToolResult, McpError> {
        let out = self
            .with_engine(true, move |eng| {
                let (_, art) = eng.load_artifact_from_mcp_arg(
                    p.body_content.as_deref(),
                    p.body_path.as_deref(),
                    p.input_type,
                )?;
                let auto_entry = match (&p.entry, &art) {
                    (Some(e), _) => Some(e.as_str()),
                    (None, LoadedArtifact::Module(m))
                        if m.funcs.iter().any(|f| {
                            f.name == p.name || f.export_name.as_deref() == Some(p.name.as_str())
                        }) =>
                    {
                        Some(p.name.as_str())
                    }
                    _ => None,
                };
                let (_, art_params, art_results, body) = art.into_region(auto_entry)?;
                let params = if p.params.is_empty() {
                    art_params
                        .into_iter()
                        .map(|(id, ty)| IrTypedVar { id: id.0, ty: ty.into() })
                        .collect()
                } else {
                    p.params
                };
                let results = if p.results.is_empty() {
                    art_results.into_iter().map(Into::into).collect()
                } else {
                    p.results
                };
                eng.define_op(p.name, p.layer, params, results, body, p.docstring, p.stratum_id)
            })
            .await?;
        json_ok(&out)
    }

    #[tool(
        name = "gnomon_prove_law",
        description = "Run the 3-stage sieve (Wasmtime fuzz -> Bitwuzla QF_ABV -> gnomon-kernel TCB admission) to prove an algebraic or disjoint memory-frame law for a Stratum op."
    )]
    async fn gnomon_prove_law(
        &self,
        Parameters(p): Parameters<ProveLawParams>,
    ) -> Result<CallToolResult, McpError> {
        let kind = match p.kind.as_deref().unwrap_or("algebraic") {
            "algebraic" => IrLawKind::Algebraic,
            "memory_frame" | "memory-frame" => IrLawKind::MemoryFrame {
                untouched_mem: p.untouched_mem.ok_or_else(|| {
                    McpError::invalid_params("memory_frame law requires untouched_mem", None)
                })?,
            },
            other => {
                return Err(McpError::invalid_params(
                    format!("unknown law kind '{other}' (expected algebraic or memory_frame)"),
                    None,
                ));
            }
        };
        let out = self
            .with_engine(true, move |eng| {
                let (_, lhs_art) = eng.load_artifact_from_mcp_arg(
                    p.lhs_content.as_deref(),
                    p.lhs_path.as_deref(),
                    p.input_type,
                )?;
                let (_, lhs_params, _, lhs_reg) = lhs_art.into_region(p.lhs_entry.as_deref())?;
                let rhs_reg = if p.rhs_content.is_some() || p.rhs_path.is_some() {
                    let (_, rhs_art) = eng.load_artifact_from_mcp_arg(
                        p.rhs_content.as_deref(),
                        p.rhs_path.as_deref(),
                        p.input_type,
                    )?;
                    rhs_art.into_region(p.rhs_entry.as_deref())?.3
                } else {
                    gnomon_kernel::Region::empty()
                };
                let pre_reg = if p.pre_content.is_some() || p.pre_path.is_some() {
                    let (_, pre_art) = eng.load_artifact_from_mcp_arg(
                        p.pre_content.as_deref(),
                        p.pre_path.as_deref(),
                        p.input_type,
                    )?;
                    Some(pre_art.into_region(p.pre_entry.as_deref())?.3)
                } else {
                    None
                };
                let params = if p.params.is_empty() {
                    lhs_params
                        .into_iter()
                        .map(|(id, ty)| IrTypedVar { id: id.0, ty: ty.into() })
                        .collect()
                } else {
                    p.params
                };
                eng.prove_law(&p.op, p.name, kind, params, lhs_reg, rhs_reg, pre_reg)
            })
            .await?;
        json_ok(&out)
    }

    #[tool(
        name = "gnomon_check_goal",
        description = "Check equivalence or InvariantLoop VCs by running bounded egglog cancellation with proved Strata laws, sound Ackermann UF congruence CEGAR for shared pure-total Strata, and residual Bitwuzla QF_ABV proving (supports ignore_dead_stack for shadow-stack refinement)."
    )]
    async fn gnomon_check_goal(
        &self,
        Parameters(p): Parameters<CheckGoalParams>,
    ) -> Result<CallToolResult, McpError> {
        let out = self
            .with_engine(true, move |eng| {
                let (_, cand_art) = eng.load_artifact_from_mcp_arg(
                    p.candidate_content.as_deref(),
                    p.candidate_path.as_deref(),
                    p.input_type,
                )?;
                let spec_art = if p.spec_content.is_none()
                    && p.candidate_content.is_none()
                    && p.spec_path.is_some()
                    && p.spec_path == p.candidate_path
                {
                    cand_art.clone()
                } else {
                    eng.load_artifact_from_mcp_arg(
                        p.spec_content.as_deref(),
                        p.spec_path.as_deref(),
                        p.input_type,
                    )?
                    .1
                };
                let pre_art = if p.pre_content.is_some() || p.pre_path.is_some() {
                    let art = if p.pre_content.is_none()
                        && p.candidate_content.is_none()
                        && p.pre_path.is_some()
                        && p.pre_path == p.candidate_path
                    {
                        cand_art.clone()
                    } else if p.pre_content.is_none()
                        && p.spec_content.is_none()
                        && p.pre_path.is_some()
                        && p.pre_path == p.spec_path
                    {
                        spec_art.clone()
                    } else {
                        eng.load_artifact_from_mcp_arg(
                            p.pre_content.as_deref(),
                            p.pre_path.as_deref(),
                            p.input_type,
                        )?
                        .1
                    };
                    Some((art, p.pre_entry))
                } else {
                    None
                };
                let post_art = if p.post_content.is_some() || p.post_path.is_some() {
                    let art = if p.post_content.is_none()
                        && p.candidate_content.is_none()
                        && p.post_path.is_some()
                        && p.post_path == p.candidate_path
                    {
                        cand_art.clone()
                    } else if p.post_content.is_none()
                        && p.spec_content.is_none()
                        && p.post_path.is_some()
                        && p.post_path == p.spec_path
                    {
                        spec_art.clone()
                    } else {
                        eng.load_artifact_from_mcp_arg(
                            p.post_content.as_deref(),
                            p.post_path.as_deref(),
                            p.input_type,
                        )?
                        .1
                    };
                    Some((art, p.post_entry))
                } else {
                    None
                };
                let prepared = prepare_goal_artifacts(
                    cand_art,
                    p.candidate_entry.as_deref(),
                    spec_art,
                    p.spec_entry.as_deref(),
                    pre_art.as_ref().map(|(a, e)| (a.clone(), e.as_deref())),
                    post_art.as_ref().map(|(a, e)| (a.clone(), e.as_deref())),
                )?;
                let params = if p.params.is_empty() {
                    prepared
                        .candidate_params
                        .into_iter()
                        .map(|(id, ty)| IrTypedVar { id: id.0, ty: ty.into() })
                        .collect()
                } else {
                    p.params
                };
                eng.check_goal_with_module(
                    prepared.context_module,
                    prepared.candidate,
                    prepared.spec,
                    params,
                    prepared.precondition,
                    prepared.loop_postcondition,
                    p.timeout_ms,
                    p.ignore_dead_stack,
                )
            })
            .await?;
        json_ok(&out)
    }

    #[tool(
        name = "gnomon_consolidate",
        description = "Prune low-MDL ops (stitch_core across >=2 solutions) and redundant laws (<=3 egglog steps), rebuild the verified registry, export compact AutoDoc / Delta Spec, and optionally emit #![no_std] strata.rs bindings."
    )]
    async fn gnomon_consolidate(
        &self,
        Parameters(p): Parameters<ConsolidateParams>,
    ) -> Result<CallToolResult, McpError> {
        let out = self
            .with_engine(true, move |eng| {
                let mut extra = Vec::with_capacity(p.solutions.len());
                for s in &p.solutions {
                    let (_, art) =
                        eng.load_artifact_from_mcp_arg(Some(s.as_str()), None, InputType::Auto)?;
                    extra.push(art.into_region(None)?.3);
                }
                let mut cfg = ConsolidationConfig::default();
                if let Some(m) = p.min_solutions {
                    cfg.min_solutions = m;
                }
                if let Some(steps) = p.max_derivation_steps {
                    cfg.max_derivation_steps = steps;
                }
                let report = eng.consolidate(&extra, &cfg)?;
                let strata_rs = p.emit_rust.then(|| eng.emit_rust(true));
                Ok(ConsolidateMcpOutput { report, strata_rs })
            })
            .await?;
        json_ok(&out)
    }

    #[tool(
        name = "gnomon_check_contract",
        description = "Verify function contracts (requires/ensures, trap-freedom, intra-memory slice_frame write-frame bounds, shadow-stack ignore_dead_stack, inline gnomon_assume/gnomon_assert) or multi-op inductive state-invariant suites (init + ops + invariant) via Bitwuzla QF_ABV."
    )]
    async fn gnomon_check_contract(
        &self,
        Parameters(p): Parameters<CheckContractParams>,
    ) -> Result<CallToolResult, McpError> {
        let out = self
            .with_engine(false, move |eng| {
                let slice_frame = p.slice_frame.map(SliceFrameParam::into_spec).transpose()?;
                let artifact = if p.content.is_some() || p.path.is_some() {
                    let (_, art) = eng.load_artifact_from_mcp_arg(
                        p.content.as_deref(),
                        p.path.as_deref(),
                        p.input_type,
                    )?;
                    Some(art)
                } else {
                    None
                };
                let requires = load_mcp_contract_pred(
                    eng,
                    p.requires,
                    p.requires_content.as_deref(),
                    p.requires_path.as_deref(),
                    p.input_type,
                )?;
                let ensures = load_mcp_contract_pred(
                    eng,
                    p.ensures,
                    p.ensures_content.as_deref(),
                    p.ensures_path.as_deref(),
                    p.input_type,
                )?;
                let invariant = load_mcp_contract_pred(
                    eng,
                    p.invariant,
                    p.invariant_content.as_deref(),
                    p.invariant_path.as_deref(),
                    p.input_type,
                )?;
                eng.check_contract(CheckContractRequest {
                    artifact,
                    entry: p.entry,
                    ops: p.ops,
                    init: p.init,
                    requires,
                    ensures,
                    invariant,
                    use_initial_state: p.use_initial_state,
                    check_trap_free: p.check_trap_free,
                    ignore_dead_stack: p.ignore_dead_stack,
                    slice_frame,
                    timeout_ms: p.timeout_ms,
                })
            })
            .await?;
        json_ok(&out)
    }
}

#[tool_handler(router = self.tool_router)]
impl ServerHandler for GnomonMcpServer {
    fn get_info(&self) -> ServerConfig {
        let mut info = ServerConfig::new(ServerCapabilities::builder().enable_tools().build())
            .with_instructions(
                "Gnomon deterministic wasm32 formal verification and recursive Stratum abstraction server. \
                 Workflow: (1) gnomon_lift_check to lift .wasm/.rs/.ir and report static SMT-cliff warnings, \
                 (2) gnomon_run_trace to inspect concrete outputs/traps/memory diffs, \
                 (3) gnomon_define_op to decompose hard nonlinear/stateful tasks into Layer-k Strata, \
                 (4) gnomon_prove_law to prove algebraic or unconditional MemoryFrame laws (Wasmtime -> Bitwuzla QF_ABV -> kernel TCB), \
                 (5) gnomon_check_goal to verify equivalence via egglog + Ackermann UF CEGAR + Bitwuzla (supports ignore_dead_stack for shadow-stack refinement and 3-way InvariantLoop VC splits), \
                 (6) gnomon_consolidate to prune low-MDL ops (stitch_core) and redundant laws (<=3 egglog steps) into a compact AutoDoc, \
                 (7) gnomon_check_contract to verify pre/post contracts, trap-freedom, intra-memory slice_frame write-frame bounds (including readonly), shadow-stack ignore_dead_stack, inline gnomon_assume/gnomon_assert harnesses, and multi-op inductive state-invariant suites (init + ops + invariant).",
            );
        info.server_info = Implementation::new("gnomon", env!("CARGO_PKG_VERSION"));
        info
    }
}
