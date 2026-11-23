//! Single MCP server (`rmcp` + `tokio` stdio) exposing all 6 atomic Gnomon tools.

use std::path::PathBuf;
use std::sync::{Arc, Mutex};

use gnomon_sieve::ConsolidationConfig;
use rmcp::handler::server::router::tool::ToolRouter;
use rmcp::handler::server::wrapper::Parameters;
use rmcp::model::{CallToolResult, ContentBlock, Implementation, ServerCapabilities, ServerConfig};
use rmcp::{ErrorData as McpError, ServerHandler, ServiceExt, tool, tool_handler, tool_router};
use serde::Deserialize;

use crate::GnomonError;
use crate::engine::GnomonEngine;
use crate::ir_codec::{
    InputType, IrLawKind, IrTypedVar, IrVal, IrValType, load_artifact_from_mcp_arg,
};

/// Single stateful Gnomon MCP Server serving all 6 verification & abstraction tools.
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

#[derive(Debug, Deserialize, schemars::JsonSchema)]
pub struct LiftCheckParams {
    /// Inline `.ir` JSON string or base64/hex encoded `.wasm` bytes.
    pub content: Option<String>,
    /// Optional local file path to a `.wasm` or `.ir` file.
    pub path: Option<String>,
    /// Input format: `auto`, `wasm`, or `ir`.
    #[serde(default = "default_input_type")]
    pub input_type: InputType,
    /// Include full serialized `.ir` document in the response.
    #[serde(default)]
    pub include_ir: bool,
}

#[derive(Debug, Deserialize, schemars::JsonSchema)]
pub struct RunTraceParams {
    /// Optional inline `.ir` JSON or base64/hex `.wasm` to run (defaults to last lifted module).
    pub content: Option<String>,
    /// Optional local file path to `.wasm` or `.ir`.
    pub path: Option<String>,
    /// Input format: `auto`, `wasm`, or `ir`.
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
    /// Strictly positive DAG layer (`>= 1`).
    pub layer: u16,
    /// Typed parameter list `[{"id":0,"ty":"i32"}]`.
    #[serde(default)]
    pub params: Vec<IrTypedVar>,
    /// Result types `["i32"]`.
    #[serde(default)]
    pub results: Vec<IrValType>,
    /// Inline `.ir` JSON or base64/hex `.wasm` defining the op body.
    pub body_content: Option<String>,
    /// Optional local file path to `.wasm` or `.ir` defining the op body.
    pub body_path: Option<String>,
    /// Input format for body: `auto`, `wasm`, or `ir`.
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
    /// LHS pattern (`.ir` JSON or base64/hex `.wasm`).
    pub lhs_content: Option<String>,
    pub lhs_path: Option<String>,
    /// RHS pattern (`.ir` JSON or base64/hex `.wasm`; omitted for `memory_frame` laws).
    pub rhs_content: Option<String>,
    pub rhs_path: Option<String>,
    /// Optional precondition region (`.ir` JSON or `.wasm`).
    pub pre_content: Option<String>,
    pub pre_path: Option<String>,
    /// Input format: `auto`, `wasm`, or `ir`.
    #[serde(default = "default_input_type")]
    pub input_type: InputType,
}

#[derive(Debug, Deserialize, schemars::JsonSchema)]
pub struct CheckGoalParams {
    /// Candidate region/module (`.ir` JSON or base64/hex `.wasm`).
    pub candidate_content: Option<String>,
    pub candidate_path: Option<String>,
    /// Specification region/module (`.ir` JSON or base64/hex `.wasm`).
    pub spec_content: Option<String>,
    pub spec_path: Option<String>,
    /// Optional precondition region.
    pub pre_content: Option<String>,
    pub pre_path: Option<String>,
    /// Optional explicit postcondition for `InvariantLoop` VC splitting.
    pub post_content: Option<String>,
    pub post_path: Option<String>,
    /// Free parameters `[{"id":0,"ty":"i32"}]`.
    #[serde(default)]
    pub params: Vec<IrTypedVar>,
    /// Input format: `auto`, `wasm`, or `ir`.
    #[serde(default = "default_input_type")]
    pub input_type: InputType,
    /// EqSat / solver budget in milliseconds.
    #[serde(default = "default_timeout_ms")]
    pub timeout_ms: u64,
}

#[derive(Debug, Deserialize, schemars::JsonSchema)]
pub struct ConsolidateParams {
    /// Additional verified solution `.ir` JSON strings to include in MDL scoring.
    #[serde(default)]
    pub solutions: Vec<String>,
    /// Minimum distinct solutions required to keep an op (default 2).
    pub min_solutions: Option<usize>,
    /// Max `egglog` steps for law redundancy pruning (default 3, clamped to 1..=3).
    pub max_derivation_steps: Option<usize>,
}

#[tool_router]
impl GnomonMcpServer {
    #[tool(
        name = "gnomon_lift_check",
        description = "Lift a .wasm module or .ir document into typed GnomonIR, check round-trip emission, and return static diagnostics."
    )]
    async fn gnomon_lift_check(
        &self,
        Parameters(p): Parameters<LiftCheckParams>,
    ) -> Result<CallToolResult, McpError> {
        let out = self
            .with_engine(true, move |eng| {
                let (detected, artifact) = load_artifact_from_mcp_arg(
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
        description = "Execute a lifted module or .ir region on the deterministic gnomon-kernel interpreter, returning outputs, traps, fuel consumed, and sparse memory diff."
    )]
    async fn gnomon_run_trace(
        &self,
        Parameters(p): Parameters<RunTraceParams>,
    ) -> Result<CallToolResult, McpError> {
        let out = self
            .with_engine(false, move |eng| {
                let artifact = if p.content.is_some() || p.path.is_some() {
                    let (_, art) = load_artifact_from_mcp_arg(
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
        description = "Register a candidate Layer-k Stratum op after gnomon-kernel DAG acyclicity and type validation."
    )]
    async fn gnomon_define_op(
        &self,
        Parameters(p): Parameters<DefineOpParams>,
    ) -> Result<CallToolResult, McpError> {
        let out = self
            .with_engine(true, move |eng| {
                let (_, art) = load_artifact_from_mcp_arg(
                    p.body_content.as_deref(),
                    p.body_path.as_deref(),
                    p.input_type,
                )?;
                let (_, art_params, art_results, body) = art.into_region(None)?;
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
                let (_, lhs_art) = load_artifact_from_mcp_arg(
                    p.lhs_content.as_deref(),
                    p.lhs_path.as_deref(),
                    p.input_type,
                )?;
                let (_, lhs_params, _, lhs_reg) = lhs_art.into_region(None)?;
                let rhs_reg = if p.rhs_content.is_some() || p.rhs_path.is_some() {
                    let (_, rhs_art) = load_artifact_from_mcp_arg(
                        p.rhs_content.as_deref(),
                        p.rhs_path.as_deref(),
                        p.input_type,
                    )?;
                    rhs_art.into_region(None)?.3
                } else {
                    gnomon_kernel::Region::empty()
                };
                let pre_reg = if p.pre_content.is_some() || p.pre_path.is_some() {
                    let (_, pre_art) = load_artifact_from_mcp_arg(
                        p.pre_content.as_deref(),
                        p.pre_path.as_deref(),
                        p.input_type,
                    )?;
                    Some(pre_art.into_region(None)?.3)
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
        description = "Check equivalence or InvariantLoop VCs by running bounded egglog cancellation with proved Strata laws, sound Ackermann UF congruence CEGAR for shared pure-total Strata, and residual Bitwuzla QF_ABV proving."
    )]
    async fn gnomon_check_goal(
        &self,
        Parameters(p): Parameters<CheckGoalParams>,
    ) -> Result<CallToolResult, McpError> {
        let out = self
            .with_engine(true, move |eng| {
                let (_, cand_art) = load_artifact_from_mcp_arg(
                    p.candidate_content.as_deref(),
                    p.candidate_path.as_deref(),
                    p.input_type,
                )?;
                let (_, cand_params, _, cand_reg) = cand_art.into_region(None)?;
                let (_, spec_art) = load_artifact_from_mcp_arg(
                    p.spec_content.as_deref(),
                    p.spec_path.as_deref(),
                    p.input_type,
                )?;
                let (_, _, _, spec_reg) = spec_art.into_region(None)?;
                let pre_reg = if p.pre_content.is_some() || p.pre_path.is_some() {
                    let (_, pre_art) = load_artifact_from_mcp_arg(
                        p.pre_content.as_deref(),
                        p.pre_path.as_deref(),
                        p.input_type,
                    )?;
                    Some(pre_art.into_region(None)?.3)
                } else {
                    None
                };
                let post_reg = if p.post_content.is_some() || p.post_path.is_some() {
                    let (_, post_art) = load_artifact_from_mcp_arg(
                        p.post_content.as_deref(),
                        p.post_path.as_deref(),
                        p.input_type,
                    )?;
                    Some(post_art.into_region(None)?.3)
                } else {
                    None
                };
                let params = if p.params.is_empty() {
                    cand_params
                        .into_iter()
                        .map(|(id, ty)| IrTypedVar { id: id.0, ty: ty.into() })
                        .collect()
                } else {
                    p.params
                };
                eng.check_goal(cand_reg, spec_reg, params, pre_reg, post_reg, p.timeout_ms)
            })
            .await?;
        json_ok(&out)
    }

    #[tool(
        name = "gnomon_consolidate",
        description = "Prune low-MDL ops (stitch_core across >=2 solutions) and redundant laws (<=3 egglog steps), rebuild the verified registry, and export compact AutoDoc / Delta Spec."
    )]
    async fn gnomon_consolidate(
        &self,
        Parameters(p): Parameters<ConsolidateParams>,
    ) -> Result<CallToolResult, McpError> {
        let report = self
            .with_engine(true, move |eng| {
                let mut extra = Vec::with_capacity(p.solutions.len());
                for s in &p.solutions {
                    let (_, art) =
                        load_artifact_from_mcp_arg(Some(s.as_str()), None, InputType::Auto)?;
                    extra.push(art.into_region(None)?.3);
                }
                let mut cfg = ConsolidationConfig::default();
                if let Some(m) = p.min_solutions {
                    cfg.min_solutions = m;
                }
                if let Some(steps) = p.max_derivation_steps {
                    cfg.max_derivation_steps = steps;
                }
                eng.consolidate(&extra, &cfg)
            })
            .await?;
        json_ok(&report)
    }
}

#[tool_handler(router = self.tool_router)]
impl ServerHandler for GnomonMcpServer {
    fn get_info(&self) -> ServerConfig {
        let mut info = ServerConfig::new(ServerCapabilities::builder().enable_tools().build())
            .with_instructions(
                "Gnomon deterministic wasm32 formal verification and recursive Stratum abstraction server. \
                 Workflow: (1) gnomon_lift_check to lift .wasm/.ir, (2) gnomon_run_trace to inspect concrete outputs/traps/memory diffs, \
                 (3) gnomon_define_op to decompose hard nonlinear/stateful tasks into Layer-k Strata, \
                 (4) gnomon_prove_law to prove algebraic or unconditional MemoryFrame laws (Wasmtime -> Bitwuzla QF_ABV -> kernel TCB), \
                 (5) gnomon_check_goal to verify composite goals via egglog + Ackermann UF CEGAR + Bitwuzla (or 3-way InvariantLoop VC split), \
                 (6) gnomon_consolidate to prune low-MDL ops (stitch_core) and redundant laws (<=3 egglog steps) into a compact AutoDoc.",
            );
        info.server_info = Implementation::new("gnomon", env!("CARGO_PKG_VERSION"));
        info
    }
}
