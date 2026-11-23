#![forbid(unsafe_code)]

use std::io::IsTerminal;
use std::path::PathBuf;
use std::process::ExitCode;

use clap::{Parser, Subcommand, ValueEnum};
use gnomon_mcp::{
    GnomonEngine, GnomonError, GnomonMcpServer, InputType, IrLawKind, IrTypedVar, IrVal,
    IrValType, load_artifact_bytes, read_input_bytes,
};
use gnomon_sieve::ConsolidationConfig;
use gnomon_wasm::emit_wasm;

#[derive(Clone, Copy, Debug, ValueEnum)]
enum CliInputType {
    Auto,
    Wasm,
    Ir,
}

impl From<CliInputType> for InputType {
    fn from(v: CliInputType) -> Self {
        match v {
            CliInputType::Auto => InputType::Auto,
            CliInputType::Wasm => InputType::Wasm,
            CliInputType::Ir => InputType::Ir,
        }
    }
}

#[derive(Parser, Debug)]
#[command(
    name = "gnomon",
    version,
    about = "Gnomon deterministic Wasm verification, sieve, CLI, and MCP server"
)]
struct Cli {
    /// Input type for .wasm / .ir / stdin payloads (`auto`, `wasm`, `ir`).
    #[arg(short = 't', long = "type", value_enum, global = true, default_value_t = CliInputType::Auto)]
    input_type: CliInputType,

    /// Optional JSON session state file for persisting Strata registry across CLI invocations.
    #[arg(long = "state", global = true)]
    state: Option<PathBuf>,

    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand, Debug)]
enum Commands {
    /// Lift a .wasm or .ir input (file or stdin) into typed GnomonIR and run static diagnostics.
    Lift {
        /// Path to a .wasm or .ir file, or '-' / omitted to read from stdin.
        input: Option<String>,
        /// Include full serialized .ir JSON in the output.
        #[arg(long)]
        emit_ir: bool,
        /// Optionally write round-tripped .wasm bytes to a file.
        #[arg(long)]
        emit_wasm: Option<PathBuf>,
    },

    /// Execute a .wasm or .ir input (file or stdin) on the deterministic gnomon-kernel interpreter.
    Trace {
        /// Path to a .wasm or .ir file, or '-' / omitted to read from stdin.
        input: Option<String>,
        /// Entry function name (defaults to func 0).
        #[arg(long)]
        entry: Option<String>,
        /// Concrete inputs as JSON array, e.g. '[{"ty":"i32","val":7}]'.
        #[arg(long, default_value = "[]")]
        inputs: String,
        /// Deterministic fuel budget.
        #[arg(long, default_value_t = 100_000)]
        fuel: u64,
    },

    /// Register a candidate Layer-k Stratum op after gnomon-kernel DAG/type check.
    DefineOp {
        /// Path to .wasm or .ir body file, or '-' / omitted to read from stdin.
        input: Option<String>,
        /// Name of the Stratum op.
        #[arg(long)]
        name: String,
        /// Strictly positive DAG layer (>= 1).
        #[arg(long, default_value_t = 1)]
        layer: u16,
        /// Optional JSON params array `[{"id":0,"ty":"i32"}]` (defaults to input signature).
        #[arg(long)]
        params: Option<String>,
        /// Optional JSON result types `["i32"]` (defaults to input signature).
        #[arg(long)]
        results: Option<String>,
        /// Optional docstring.
        #[arg(long, default_value = "")]
        doc: String,
        /// Optional explicit numeric StratumId.
        #[arg(long)]
        id: Option<u32>,
    },

    /// Prove a law via 3-stage sieve (Wasmtime fuzz -> Bitwuzla QF_ABV -> kernel TCB admission).
    ProveLaw {
        /// Owning Stratum op name or numeric ID.
        #[arg(long)]
        op: String,
        /// Name of the law.
        #[arg(long)]
        name: String,
        /// Law kind: `algebraic` or `memory-frame`.
        #[arg(long, default_value = "algebraic")]
        kind: String,
        /// For `memory-frame` laws, the MemId that must remain untouched.
        #[arg(long)]
        untouched_mem: Option<u16>,
        /// Optional JSON params array `[{"id":0,"ty":"i32"}]`.
        #[arg(long)]
        params: Option<String>,
        /// Path to LHS .wasm or .ir file (or '-' for stdin).
        #[arg(long)]
        lhs: String,
        /// Path to RHS .wasm or .ir file (omitted for memory-frame).
        #[arg(long)]
        rhs: Option<String>,
        /// Optional precondition .wasm or .ir file.
        #[arg(long)]
        pre: Option<String>,
    },

    /// Check equivalence or InvariantLoop VCs via egglog cancellation + Bitwuzla QF_ABV.
    CheckGoal {
        /// Path to candidate .wasm or .ir file (or '-' for stdin).
        #[arg(long)]
        candidate: String,
        /// Path to specification .wasm or .ir file.
        #[arg(long)]
        spec: String,
        /// Optional precondition .wasm or .ir file.
        #[arg(long)]
        pre: Option<String>,
        /// Optional postcondition .wasm or .ir file for InvariantLoop VC splitting.
        #[arg(long)]
        post: Option<String>,
        /// Optional JSON params array `[{"id":0,"ty":"i32"}]`.
        #[arg(long)]
        params: Option<String>,
        /// Timeout budget in milliseconds.
        #[arg(long, default_value_t = 5_000)]
        timeout_ms: u64,
    },

    /// Run stitch_core MDL + egglog 3-step law non-redundancy consolidation and emit AutoDoc.
    Consolidate {
        /// Additional verified solution .wasm or .ir files.
        #[arg(long = "solution")]
        solutions: Vec<String>,
        /// Minimum distinct solutions required to keep an op (default 2).
        #[arg(long, default_value_t = 2)]
        min_solutions: usize,
        /// Max egglog steps for law redundancy pruning (1..=3).
        #[arg(long, default_value_t = 3)]
        max_derivation_steps: usize,
    },

    /// Start the single Gnomon MCP server over stdio (rmcp + tokio).
    Mcp,
}

fn load_cli_artifact(
    path: Option<&str>,
    kind: InputType,
) -> Result<(InputType, gnomon_mcp::LoadedArtifact), GnomonError> {
    let (bytes, resolved_path) = read_input_bytes(path)?;
    load_artifact_bytes(&bytes, kind, resolved_path)
}

fn run(cli: Cli) -> Result<bool, GnomonError> {
    let input_type: InputType = cli.input_type.into();
    match cli.command {
        Commands::Mcp => {
            let server = GnomonMcpServer::new(cli.state)?;
            let rt = tokio::runtime::Builder::new_multi_thread()
                .enable_all()
                .build()
                .map_err(|e| GnomonError::Internal(format!("tokio runtime error: {e}")))?;
            rt.block_on(server.serve_stdio())?;
            Ok(true)
        }
        Commands::Lift { input, emit_ir, emit_wasm: emit_wasm_path } => {
            let mut eng = match &cli.state {
                Some(p) => GnomonEngine::load_state_file(p)?,
                None => GnomonEngine::new(),
            };
            let (detected, art) = load_cli_artifact(input.as_deref(), input_type)?;
            let out = eng.lift_check(detected, art, emit_ir)?;
            if let Some(out_path) = emit_wasm_path
                && let Some(ref m) = eng.active_module
            {
                let bytes = emit_wasm(m).map_err(|e| GnomonError::Wasm(e.to_string()))?;
                std::fs::write(&out_path, bytes)
                    .map_err(|e| GnomonError::Io(format!("failed writing wasm: {e}")))?;
            }
            if let Some(ref p) = cli.state {
                eng.save_state_file(p)?;
            }
            println!(
                "{}",
                serde_json::to_string_pretty(&out)
                    .map_err(|e| GnomonError::Internal(e.to_string()))?
            );
            Ok(true)
        }
        Commands::Trace { input, entry, inputs, fuel } => {
            let eng = match &cli.state {
                Some(p) => GnomonEngine::load_state_file(p)?,
                None => GnomonEngine::new(),
            };
            let parsed_inputs: Vec<IrVal> = serde_json::from_str(&inputs)
                .map_err(|e| GnomonError::InvalidInput(format!("invalid --inputs JSON: {e}")))?;
            let art_override = if input.is_none()
                && std::io::stdin().is_terminal()
                && eng.active_module.is_some()
            {
                None
            } else {
                Some(load_cli_artifact(input.as_deref(), input_type)?.1)
            };
            let out = eng.run_trace(art_override, entry.as_deref(), &parsed_inputs, fuel)?;
            println!(
                "{}",
                serde_json::to_string_pretty(&out)
                    .map_err(|e| GnomonError::Internal(e.to_string()))?
            );
            Ok(out.status == "OK")
        }
        Commands::DefineOp { input, name, layer, params, results, doc, id } => {
            let mut eng = match &cli.state {
                Some(p) => GnomonEngine::load_state_file(p)?,
                None => GnomonEngine::new(),
            };
            let (_, art) = load_cli_artifact(input.as_deref(), input_type)?;
            let (_, art_params, art_results, body) = art.into_region(None)?;
            let k_params: Vec<IrTypedVar> = match params {
                Some(s) => serde_json::from_str(&s)
                    .map_err(|e| GnomonError::InvalidInput(format!("invalid --params JSON: {e}")))?,
                None => art_params
                    .into_iter()
                    .map(|(vid, ty)| IrTypedVar { id: vid.0, ty: ty.into() })
                    .collect(),
            };
            let k_results: Vec<IrValType> = match results {
                Some(s) => serde_json::from_str(&s)
                    .map_err(|e| GnomonError::InvalidInput(format!("invalid --results JSON: {e}")))?,
                None => art_results.into_iter().map(Into::into).collect(),
            };
            let out = eng.define_op(name, layer, k_params, k_results, body, doc, id)?;
            if let Some(ref p) = cli.state {
                eng.save_state_file(p)?;
            }
            println!(
                "{}",
                serde_json::to_string_pretty(&out)
                    .map_err(|e| GnomonError::Internal(e.to_string()))?
            );
            Ok(true)
        }
        Commands::ProveLaw { op, name, kind, untouched_mem, params, lhs, rhs, pre } => {
            let mut eng = match &cli.state {
                Some(p) => GnomonEngine::load_state_file(p)?,
                None => GnomonEngine::new(),
            };
            let (_, lhs_art) = load_cli_artifact(Some(lhs.as_str()), input_type)?;
            let (_, lhs_params, _, lhs_reg) = lhs_art.into_region(None)?;
            let rhs_reg = match rhs {
                Some(r) => load_cli_artifact(Some(r.as_str()), input_type)?.1.into_region(None)?.3,
                None => gnomon_kernel::Region::empty(),
            };
            let pre_reg = match pre {
                Some(p) => {
                    Some(load_cli_artifact(Some(p.as_str()), input_type)?.1.into_region(None)?.3)
                }
                None => None,
            };
            let law_kind = match kind.as_str() {
                "algebraic" => IrLawKind::Algebraic,
                "memory-frame" | "memory_frame" => IrLawKind::MemoryFrame {
                    untouched_mem: untouched_mem.ok_or_else(|| {
                        GnomonError::InvalidInput("--untouched-mem required for memory-frame".into())
                    })?,
                },
                other => {
                    return Err(GnomonError::InvalidInput(format!(
                        "unknown --kind '{other}' (expected algebraic or memory-frame)"
                    )));
                }
            };
            let k_params: Vec<IrTypedVar> = match params {
                Some(s) => serde_json::from_str(&s)
                    .map_err(|e| GnomonError::InvalidInput(format!("invalid --params JSON: {e}")))?,
                None => lhs_params
                    .into_iter()
                    .map(|(vid, ty)| IrTypedVar { id: vid.0, ty: ty.into() })
                    .collect(),
            };
            let out = eng.prove_law(&op, name, law_kind, k_params, lhs_reg, rhs_reg, pre_reg)?;
            if let Some(ref p) = cli.state {
                eng.save_state_file(p)?;
            }
            println!(
                "{}",
                serde_json::to_string_pretty(&out)
                    .map_err(|e| GnomonError::Internal(e.to_string()))?
            );
            Ok(out.status == "PROVED")
        }
        Commands::CheckGoal { candidate, spec, pre, post, params, timeout_ms } => {
            let mut eng = match &cli.state {
                Some(p) => GnomonEngine::load_state_file(p)?,
                None => GnomonEngine::new(),
            };
            let (_, cand_art) = load_cli_artifact(Some(candidate.as_str()), input_type)?;
            let (_, cand_params, _, cand_reg) = cand_art.into_region(None)?;
            let (_, spec_art) = load_cli_artifact(Some(spec.as_str()), input_type)?;
            let (_, _, _, spec_reg) = spec_art.into_region(None)?;
            let pre_reg = match pre {
                Some(p) => {
                    Some(load_cli_artifact(Some(p.as_str()), input_type)?.1.into_region(None)?.3)
                }
                None => None,
            };
            let post_reg = match post {
                Some(p) => {
                    Some(load_cli_artifact(Some(p.as_str()), input_type)?.1.into_region(None)?.3)
                }
                None => None,
            };
            let k_params: Vec<IrTypedVar> = match params {
                Some(s) => serde_json::from_str(&s)
                    .map_err(|e| GnomonError::InvalidInput(format!("invalid --params JSON: {e}")))?,
                None => cand_params
                    .into_iter()
                    .map(|(vid, ty)| IrTypedVar { id: vid.0, ty: ty.into() })
                    .collect(),
            };
            let out = eng.check_goal(cand_reg, spec_reg, k_params, pre_reg, post_reg, timeout_ms)?;
            if let Some(ref p) = cli.state {
                eng.save_state_file(p)?;
            }
            println!(
                "{}",
                serde_json::to_string_pretty(&out)
                    .map_err(|e| GnomonError::Internal(e.to_string()))?
            );
            Ok(out.status == "PROVED")
        }
        Commands::Consolidate { solutions, min_solutions, max_derivation_steps } => {
            let mut eng = match &cli.state {
                Some(p) => GnomonEngine::load_state_file(p)?,
                None => GnomonEngine::new(),
            };
            let mut extra = Vec::with_capacity(solutions.len());
            for s in &solutions {
                let (_, art) = load_cli_artifact(Some(s.as_str()), input_type)?;
                extra.push(art.into_region(None)?.3);
            }
            let cfg = ConsolidationConfig {
                min_solutions,
                max_derivation_steps,
                ..ConsolidationConfig::default()
            };
            let report = eng.consolidate(&extra, &cfg)?;
            if let Some(ref p) = cli.state {
                eng.save_state_file(p)?;
            }
            println!(
                "{}",
                serde_json::to_string_pretty(&report)
                    .map_err(|e| GnomonError::Internal(e.to_string()))?
            );
            Ok(true)
        }
    }
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    match run(cli) {
        Ok(true) => ExitCode::SUCCESS,
        Ok(false) => ExitCode::from(1),
        Err(e) => {
            eprintln!("gnomon error: {e}");
            ExitCode::from(2)
        }
    }
}
