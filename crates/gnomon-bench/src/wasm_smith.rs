#![forbid(unsafe_code)]

//! Deterministic `wasm-smith` differential & blowup fuzzer gate for Project Gnomon.
//!
//! Generates seeded valid deterministic `i32`/`i64` WebAssembly modules within Gnomon's
//! supported subset and validates every lifted module across three gates:
//! 1. **Lossless round-trip**: `emit_wasm` -> `wasmparser::validate` -> `lift_wasm`
//! 2. **3-way differential execution**: `gnomon-kernel::eval_func` vs `wasmtime(orig)` vs
//!    `wasmtime(emitted)` on concrete boundary and PRNG input vectors
//! 3. **Blowup ceiling check**: `estimate_smt_cliff` (< 50 ms), step-capped `EgglogSimplifier`
//!    (`max_iters: 3, max_nodes: 2_000, timeout_ms: 200`), and `BitwuzlaNativeBackend`
//!    reflexive equivalence (`f ≡ f` must NEVER return `Sat`).

use std::collections::BTreeMap;
use std::sync::OnceLock;
use std::time::Instant;

use arbitrary::Unstructured;
use gnomon_kernel::{
    FuncDef, FuncId, HeapState, Module, StratumRegistry, TrapCode, Val, ValId, ValType, eval_func,
};
use gnomon_sieve::{
    BitwuzlaNativeBackend, EgglogSimplifier, EqSatConfig, SieveError, SmtBackend, SmtResult,
    estimate_smt_cliff,
};
use gnomon_wasm::{ExecOutcome, WasmError, emit_wasm, lift_wasm};
use serde::{Deserialize, Serialize};
use wasm_smith::{Config as SmithConfig, InstructionKind, InstructionKinds, Module as SmithModule};
use wasmtime::{
    Config as WtConfig, Engine, Instance, Module as WtModule, OptLevel, Store, Trap, Val as WtVal,
};

/// Default base seed (`"GNOMONSM"` in ASCII) for deterministic `wasm-smith` runs.
pub const DEFAULT_BASE_SEED: u64 = 0x474E_4F4D_4F4E_534D;

/// Number of deterministic PRNG bytes fed to `Unstructured` per candidate module.
const SEED_BYTES_LEN: usize = 4096;

/// Configuration for the `wasm-smith` differential & blowup fuzzer gate.
#[derive(Clone, Debug, PartialEq)]
pub struct WasmSmithGateConfig {
    pub target_lifted: usize,
    pub base_seed: u64,
    pub max_attempts: usize,
    pub inputs_per_func: usize,
    pub fuel_per_run: u64,
    pub retry_fuel_per_run: u64,
    pub egglog_config: EqSatConfig,
    pub cliff_ceiling_ms: f64,
    pub egglog_ceiling_ms: f64,
    pub smt_sample_count: usize,
    pub smt_time_limit_ms: u64,
    pub smt_ceiling_ms: f64,
    pub trace: bool,
}

impl Default for WasmSmithGateConfig {
    fn default() -> Self {
        Self {
            target_lifted: 1_000,
            base_seed: DEFAULT_BASE_SEED,
            max_attempts: 10_000,
            inputs_per_func: 6,
            fuel_per_run: 50_000,
            retry_fuel_per_run: 500_000,
            egglog_config: EqSatConfig {
                max_iters: 3,
                max_nodes: 2_000,
                timeout_ms: 200,
            },
            cliff_ceiling_ms: 50.0,
            egglog_ceiling_ms: 1_000.0,
            smt_sample_count: 1_000,
            smt_time_limit_ms: 200,
            smt_ceiling_ms: 2_000.0,
            trace: false,
        }
    }
}

/// Summary percentiles (in milliseconds) for a latency series.
#[derive(Clone, Copy, Debug, Default, PartialEq, Serialize, Deserialize)]
pub struct LatencyStats {
    pub count: usize,
    pub p50_ms: f64,
    pub p95_ms: f64,
    pub p99_ms: f64,
    pub max_ms: f64,
    pub total_ms: f64,
}

impl LatencyStats {
    pub fn from_samples(samples: &mut [f64]) -> Self {
        if samples.is_empty() {
            return Self::default();
        }
        samples.sort_by(|a, b| a.total_cmp(b));
        let total_ms: f64 = samples.iter().sum();
        let max_ms = *samples.last().unwrap_or(&0.0);
        Self {
            count: samples.len(),
            p50_ms: percentile_sorted(samples, 0.50),
            p95_ms: percentile_sorted(samples, 0.95),
            p99_ms: percentile_sorted(samples, 0.99),
            max_ms,
            total_ms,
        }
    }
}

fn percentile_sorted(sorted: &[f64], q: f64) -> f64 {
    if sorted.is_empty() {
        return 0.0;
    }
    let idx = ((sorted.len() - 1) as f64 * q).round() as usize;
    sorted[idx.min(sorted.len() - 1)]
}

/// Full report produced by a successful `wasm-smith` gate run.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct WasmSmithGateReport {
    pub base_seed: u64,
    pub attempts: usize,
    pub generation_errors: usize,
    pub skipped_unsupported: usize,
    pub skipped_reasons: BTreeMap<String, usize>,
    pub lifted: usize,
    pub roundtrip_ok: usize,
    pub diff_funcs_checked: usize,
    pub diff_checks: usize,
    pub diff_fuel_or_depth_skipped: usize,
    pub cliff_latency: LatencyStats,
    pub egglog_latency: LatencyStats,
    pub egglog_max_iters_seen: usize,
    pub egglog_max_nodes_after: usize,
    pub smt_checked: usize,
    pub smt_unsat: usize,
    pub smt_unknown: usize,
    pub smt_sat: usize,
    pub smt_encoding_errors: usize,
    pub smt_latency: LatencyStats,
    pub total_elapsed_ms: f64,
}

/// Structured failure report containing the exact deterministic seed and failing stage.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WasmSmithFailure {
    pub base_seed: u64,
    pub attempt_index: usize,
    pub lifted_index: usize,
    pub stage: &'static str,
    pub detail: String,
    pub wasm_bytes: Vec<u8>,
}

impl std::fmt::Display for WasmSmithFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "wasm-smith failure at stage `{}` (base_seed=0x{:016x}, attempt={}, lifted_idx={}, wasm_len={}): {}",
            self.stage,
            self.base_seed,
            self.attempt_index,
            self.lifted_index,
            self.wasm_bytes.len(),
            self.detail
        )
    }
}

impl std::error::Error for WasmSmithFailure {}

/// Returns the `wasm-smith` `Config` restricted to Gnomon's deterministic `i32`/`i64` subset.
pub fn gnomon_wasm_smith_config() -> SmithConfig {
    SmithConfig {
        allow_floats: false,
        simd_enabled: false,
        relaxed_simd_enabled: false,
        reference_types_enabled: false,
        bulk_memory_enabled: true,
        sign_extension_ops_enabled: true,
        saturating_float_to_int_enabled: false,
        multi_value_enabled: false,
        memory64_enabled: false,
        threads_enabled: false,
        shared_everything_threads_enabled: false,
        exceptions_enabled: false,
        tail_call_enabled: false,
        gc_enabled: false,
        compact_imports_enabled: false,
        custom_descriptors_enabled: false,
        custom_page_sizes_enabled: false,
        wide_arithmetic_enabled: false,
        acquire_release_atomics_enabled: false,
        multibyte_array_access_enabled: false,
        extended_const_enabled: true,
        allow_start_export: false,
        allowed_instructions: InstructionKinds::new(&[
            InstructionKind::NumericInt,
            InstructionKind::Parametric,
            InstructionKind::Variable,
            InstructionKind::MemoryInt,
            InstructionKind::Control,
        ]),
        min_tables: 0,
        max_tables: 0,
        min_element_segments: 0,
        max_element_segments: 0,
        min_elements: 0,
        max_elements: 0,
        min_data_segments: 0,
        max_data_segments: 0,
        min_tags: 0,
        max_tags: 0,
        min_types: 1,
        max_types: 8,
        min_imports: 0,
        max_imports: 0,
        min_funcs: 1,
        max_funcs: 4,
        min_exports: 1,
        min_memories: 0,
        max_memories: 2,
        max_memory32_bytes: 2 * 65_536,
        min_globals: 0,
        max_globals: 4,
        max_instructions: 80,
        export_everything: true,
        ..SmithConfig::default()
    }
}

/// Deterministically generates `SEED_BYTES_LEN` bytes for `(base_seed, attempt_index)` via SplitMix64.
pub fn generate_seed_bytes(base_seed: u64, attempt_index: usize) -> Vec<u8> {
    let mut state = base_seed
        ^ (attempt_index as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15)
        ^ 0xBF58_476D_1CE4_E5B9;
    let mut out = Vec::with_capacity(SEED_BYTES_LEN);
    while out.len() < SEED_BYTES_LEN {
        state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^= z >> 31;
        out.extend_from_slice(&z.to_le_bytes());
    }
    out.truncate(SEED_BYTES_LEN);
    out
}

/// Generates a single deterministic `wasm-smith` module binary for `(base_seed, attempt_index)`.
pub fn generate_wasm_for_attempt(base_seed: u64, attempt_index: usize) -> arbitrary::Result<Vec<u8>> {
    let bytes = generate_seed_bytes(base_seed, attempt_index);
    let mut u = Unstructured::new(&bytes);
    let module = SmithModule::new(gnomon_wasm_smith_config(), &mut u)?;
    Ok(module.to_bytes())
}

fn shared_wasmtime_engine() -> Result<&'static Engine, String> {
    static ENGINE: OnceLock<Result<Engine, String>> = OnceLock::new();
    let res = ENGINE.get_or_init(|| {
        let mut cfg = WtConfig::new();
        cfg.consume_fuel(true)
            .wasm_multi_memory(true)
            .wasm_bulk_memory(true)
            .wasm_multi_value(true)
            .wasm_backtrace_max_frames(None)
            .generate_address_map(false)
            .parallel_compilation(false)
            .cranelift_opt_level(OptLevel::None);
        Engine::new(&cfg).map_err(|e| e.to_string())
    });
    match res {
        Ok(e) => Ok(e),
        Err(msg) => Err(msg.clone()),
    }
}

fn map_wasmtime_err(err: &wasmtime::Error) -> TrapCode {
    if let Some(trap) = err.downcast_ref::<Trap>() {
        match trap {
            Trap::IntegerDivisionByZero => TrapCode::DivByZero,
            Trap::IntegerOverflow => TrapCode::IntOverflow,
            Trap::MemoryOutOfBounds => TrapCode::OutOfBoundsMem,
            Trap::OutOfFuel | Trap::StackOverflow => TrapCode::OutOfFuel,
            Trap::UnreachableCodeReached => TrapCode::Unreachable,
            _ => TrapCode::Unreachable,
        }
    } else {
        TrapCode::Unreachable
    }
}

fn to_wt_val(v: Val) -> WtVal {
    match v {
        Val::I32(x) => WtVal::I32(x),
        Val::I64(x) => WtVal::I64(x),
    }
}

fn from_wt_val(v: &WtVal) -> Result<Val, String> {
    match *v {
        WtVal::I32(x) => Ok(Val::I32(x)),
        WtVal::I64(x) => Ok(Val::I64(x)),
        ref other => Err(format!("unexpected wasmtime result val: {other:?}")),
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct RunResult {
    outcome: ExecOutcome,
    memories: Vec<Vec<u8>>,
    globals: Vec<Val>,
    fuel_consumed: u64,
}

fn run_wasmtime_compiled(
    engine: &Engine,
    wt_mod: &WtModule,
    module: &Module,
    func: &FuncDef,
    args: &[Val],
    fuel: u64,
) -> Result<RunResult, String> {
    let export_name = func
        .export_name
        .as_deref()
        .ok_or_else(|| format!("func {:?} has no export name", func.id))?;
    let mut store = Store::new(engine, ());
    store.set_fuel(fuel).map_err(|e| format!("set_fuel: {e}"))?;
    let instance =
        Instance::new(&mut store, wt_mod, &[]).map_err(|e| format!("instantiate: {e}"))?;
    let wt_func = instance
        .get_func(&mut store, export_name)
        .ok_or_else(|| format!("missing exported func `{export_name}` in wasmtime instance"))?;

    let wt_args: Vec<WtVal> = args.iter().copied().map(to_wt_val).collect();
    let mut wt_results: Vec<WtVal> = func
        .results
        .iter()
        .map(|&ty| match ty {
            ValType::I32 => WtVal::I32(0),
            ValType::I64 => WtVal::I64(0),
        })
        .collect();

    let call_res = wt_func.call(&mut store, &wt_args, &mut wt_results);
    let remaining = store.get_fuel().unwrap_or(0);
    let fuel_consumed = fuel.saturating_sub(remaining);

    match call_res {
        Ok(()) => {
            let vals = wt_results
                .iter()
                .map(from_wt_val)
                .collect::<Result<Vec<_>, _>>()?;
            let mut memories = Vec::with_capacity(module.memory_exports.len());
            for (name, _) in &module.memory_exports {
                let mem = instance
                    .get_memory(&mut store, name)
                    .ok_or_else(|| format!("missing exported memory `{name}`"))?;
                memories.push(mem.data(&store).to_vec());
            }
            let mut globals = Vec::with_capacity(module.global_exports.len());
            for (name, _) in &module.global_exports {
                let g = instance
                    .get_global(&mut store, name)
                    .ok_or_else(|| format!("missing exported global `{name}`"))?;
                globals.push(from_wt_val(&g.get(&mut store))?);
            }
            Ok(RunResult {
                outcome: ExecOutcome::Values(vals),
                memories,
                globals,
                fuel_consumed,
            })
        }
        Err(err) => Ok(RunResult {
            outcome: ExecOutcome::Trap(map_wasmtime_err(&err)),
            memories: Vec::new(),
            globals: Vec::new(),
            fuel_consumed,
        }),
    }
}

fn run_kernel_func(
    module: &Module,
    reg: &StratumRegistry,
    func_id: FuncId,
    args: &[Val],
    fuel: u64,
) -> Result<RunResult, String> {
    let heap = HeapState::from_module(module, fuel)
        .map_err(|t| format!("HeapState::from_module failed: {t:?}"))?;
    match eval_func(module, reg, func_id, args, heap) {
        Ok((vals, post_heap)) => {
            let fuel_consumed = fuel.saturating_sub(post_heap.fuel_remaining);
            let mut memories = Vec::with_capacity(module.memory_exports.len());
            for (_, mid) in &module.memory_exports {
                let m = post_heap
                    .memory(*mid)
                    .map_err(|t| format!("missing kernel memory {mid:?}: {t:?}"))?;
                memories.push(m.bytes.clone());
            }
            let mut globals = Vec::with_capacity(module.global_exports.len());
            for (_, gid) in &module.global_exports {
                let v = post_heap
                    .globals
                    .get(gid.0 as usize)
                    .copied()
                    .ok_or_else(|| format!("missing kernel global {gid:?}"))?;
                globals.push(v);
            }
            Ok(RunResult {
                outcome: ExecOutcome::Values(vals),
                memories,
                globals,
                fuel_consumed,
            })
        }
        Err(trap) => Ok(RunResult {
            outcome: ExecOutcome::Trap(trap),
            memories: Vec::new(),
            globals: Vec::new(),
            fuel_consumed: fuel,
        }),
    }
}

fn build_input_vectors(
    params: &[(ValId, ValType)],
    count: usize,
    seed: u64,
) -> Vec<Vec<Val>> {
    if params.is_empty() {
        return vec![Vec::new()];
    }
    const B32: [i32; 8] = [0, 1, -1, 2, 16, 65_536, i32::MAX, i32::MIN];
    const B64: [i64; 8] = [0, 1, -1, 2, 63, 65_536, i64::MAX, i64::MIN];
    let mut state = seed ^ 0xD1B5_4A32_D192_ED03;
    let mut next_u64 = || {
        state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    };
    (0..count)
        .map(|vec_idx| {
            params
                .iter()
                .enumerate()
                .map(|(p_idx, &(_, ty))| {
                    let r = next_u64();
                    match ty {
                        ValType::I32 => {
                            if vec_idx < 4 {
                                Val::I32(B32[(vec_idx + p_idx) & 7])
                            } else {
                                Val::I32(r as i32)
                            }
                        }
                        ValType::I64 => {
                            if vec_idx < 4 {
                                Val::I64(B64[(vec_idx + p_idx) & 7])
                            } else {
                                Val::I64(r as i64)
                            }
                        }
                    }
                })
                .collect()
        })
        .collect()
}

fn verify_roundtrip_structure(lifted: &Module, relifted: &Module) -> Result<(), String> {
    if lifted.funcs.len() != relifted.funcs.len() {
        return Err(format!(
            "round-trip func count mismatch: {} vs {}",
            lifted.funcs.len(),
            relifted.funcs.len()
        ));
    }
    if lifted.memories.len() != relifted.memories.len() {
        return Err(format!(
            "round-trip memory count mismatch: {} vs {}",
            lifted.memories.len(),
            relifted.memories.len()
        ));
    }
    if lifted.globals.len() != relifted.globals.len() {
        return Err(format!(
            "round-trip global count mismatch: {} vs {}",
            lifted.globals.len(),
            relifted.globals.len()
        ));
    }
    for (orig, rt) in lifted.funcs.iter().zip(&relifted.funcs) {
        if orig.export_name != rt.export_name
            || orig.params.len() != rt.params.len()
            || orig
                .params
                .iter()
                .zip(&rt.params)
                .any(|((_, a), (_, b))| a != b)
            || orig.results != rt.results
        {
            return Err(format!(
                "round-trip signature mismatch for func {:?} ({:?} vs {:?})",
                orig.id, orig.export_name, rt.export_name
            ));
        }
    }
    Ok(())
}

fn compare_runs(
    label_a: &str,
    a: &RunResult,
    label_b: &str,
    b: &RunResult,
) -> Result<(), String> {
    if a.outcome != b.outcome {
        return Err(format!(
            "outcome mismatch: {label_a}={:?} vs {label_b}={:?}",
            a.outcome, b.outcome
        ));
    }
    if matches!(a.outcome, ExecOutcome::Values(_)) {
        if a.memories != b.memories {
            return Err(format!(
                "exported memory mismatch between {label_a} and {label_b}"
            ));
        }
        if a.globals != b.globals {
            return Err(format!(
                "exported global mismatch: {label_a}={:?} vs {label_b}={:?}",
                a.globals, b.globals
            ));
        }
    }
    Ok(())
}

fn select_entry_func(module: &Module) -> Option<&FuncDef> {
    module
        .funcs
        .iter()
        .find(|f| f.export_name.is_some())
        .or_else(|| module.funcs.first())
}

/// Runs the full deterministic `wasm-smith` differential & blowup fuzzer gate (fail-fast).
pub fn run_wasm_smith_gate(
    cfg: &WasmSmithGateConfig,
) -> Result<WasmSmithGateReport, WasmSmithFailure> {
    let (report, failures) = run_gate_inner(cfg, true)?;
    if let Some(first) = failures.into_iter().next() {
        return Err(first);
    }
    Ok(report)
}

/// Scans `cfg.target_lifted` modules without stopping on the first failure, collecting every
/// distinct failure along with aggregate stats. Useful for root-causing multiple bugs in one pass.
pub fn scan_wasm_smith_gate(
    cfg: &WasmSmithGateConfig,
) -> Result<(WasmSmithGateReport, Vec<WasmSmithFailure>), WasmSmithFailure> {
    run_gate_inner(cfg, false)
}

fn run_gate_inner(
    cfg: &WasmSmithGateConfig,
    fail_fast: bool,
) -> Result<(WasmSmithGateReport, Vec<WasmSmithFailure>), WasmSmithFailure> {
    let total_start = Instant::now();
    let engine = shared_wasmtime_engine().map_err(|detail| WasmSmithFailure {
        base_seed: cfg.base_seed,
        attempt_index: 0,
        lifted_index: 0,
        stage: "wasmtime_engine_init",
        detail,
        wasm_bytes: Vec::new(),
    })?;
    let registry = StratumRegistry::new();
    let simplifier = EgglogSimplifier::new(cfg.egglog_config);
    let mut smt = BitwuzlaNativeBackend::with_time_limit_ms(cfg.smt_time_limit_ms);

    let mut failures: Vec<WasmSmithFailure> = Vec::new();
    let mut record_failure = |failure: WasmSmithFailure| -> Result<(), WasmSmithFailure> {
        if fail_fast {
            Err(failure)
        } else {
            failures.push(failure);
            Ok(())
        }
    };

    let mut attempts = 0usize;
    let mut generation_errors = 0usize;
    let mut skipped_unsupported = 0usize;
    let mut skipped_reasons: BTreeMap<String, usize> = BTreeMap::new();
    let mut lifted_count = 0usize;
    let mut roundtrip_ok = 0usize;
    let mut diff_funcs_checked = 0usize;
    let mut diff_checks = 0usize;
    let mut diff_fuel_or_depth_skipped = 0usize;

    let mut cliff_samples_ms = Vec::with_capacity(cfg.target_lifted);
    let mut egglog_samples_ms = Vec::with_capacity(cfg.target_lifted);
    let mut egglog_max_iters_seen = 0usize;
    let mut egglog_max_nodes_after = 0usize;

    let mut smt_checked = 0usize;
    let mut smt_unsat = 0usize;
    let mut smt_unknown = 0usize;
    let mut smt_sat = 0usize;
    let mut smt_encoding_errors = 0usize;
    let mut smt_samples_ms = Vec::with_capacity(cfg.smt_sample_count.min(cfg.target_lifted));

    while lifted_count < cfg.target_lifted && attempts < cfg.max_attempts {
        let attempt_index = attempts;
        attempts += 1;

        let orig_wasm = match generate_wasm_for_attempt(cfg.base_seed, attempt_index) {
            Ok(bytes) => bytes,
            Err(_) => {
                generation_errors += 1;
                continue;
            }
        };

        if let Err(err) = wasmparser::validate(&orig_wasm) {
            record_failure(WasmSmithFailure {
                base_seed: cfg.base_seed,
                attempt_index,
                lifted_index: lifted_count,
                stage: "wasm_smith_validate",
                detail: format!("wasm-smith generated invalid wasm: {err}"),
                wasm_bytes: orig_wasm,
            })?;
            continue;
        }

        let lifted = match lift_wasm(&orig_wasm) {
            Ok(m) => m,
            Err(WasmError::UnsupportedFeature(reason)) => {
                skipped_unsupported += 1;
                let key = reason.chars().take(64).collect::<String>();
                *skipped_reasons.entry(key).or_insert(0) += 1;
                continue;
            }
            Err(err) => {
                record_failure(WasmSmithFailure {
                    base_seed: cfg.base_seed,
                    attempt_index,
                    lifted_index: lifted_count,
                    stage: "lift_wasm",
                    detail: format!("lift_wasm failed on valid subset module: {err:?}"),
                    wasm_bytes: orig_wasm,
                })?;
                continue;
            }
        };

        let lifted_index = lifted_count;
        lifted_count += 1;

        if cfg.trace {
            eprintln!("[trace] attempt={attempt_index} lifted={lifted_index} stage=roundtrip");
        }

        // ── Gate 1: Lossless Round-Trip (emit -> validate -> re-lift) ──────
        let emitted = match emit_wasm(&lifted) {
            Ok(bytes) => bytes,
            Err(err) => {
                record_failure(WasmSmithFailure {
                    base_seed: cfg.base_seed,
                    attempt_index,
                    lifted_index,
                    stage: "emit_wasm",
                    detail: format!("emit_wasm failed: {err:?}"),
                    wasm_bytes: orig_wasm,
                })?;
                continue;
            }
        };

        if let Err(err) = wasmparser::validate(&emitted) {
            record_failure(WasmSmithFailure {
                base_seed: cfg.base_seed,
                attempt_index,
                lifted_index,
                stage: "roundtrip_validate",
                detail: format!("wasmparser::validate(emitted) failed: {err}"),
                wasm_bytes: orig_wasm,
            })?;
            continue;
        }

        let relifted = match lift_wasm(&emitted) {
            Ok(m) => m,
            Err(err) => {
                record_failure(WasmSmithFailure {
                    base_seed: cfg.base_seed,
                    attempt_index,
                    lifted_index,
                    stage: "roundtrip_relift",
                    detail: format!("lift_wasm(emitted) failed: {err:?}"),
                    wasm_bytes: orig_wasm,
                })?;
                continue;
            }
        };

        if let Err(detail) = verify_roundtrip_structure(&lifted, &relifted) {
            record_failure(WasmSmithFailure {
                base_seed: cfg.base_seed,
                attempt_index,
                lifted_index,
                stage: "roundtrip_structure",
                detail,
                wasm_bytes: orig_wasm,
            })?;
            continue;
        }
        roundtrip_ok += 1;

        if cfg.trace {
            eprintln!("[trace] attempt={attempt_index} lifted={lifted_index} stage=diff");
        }
        // ── Gate 2: 3-Way Differential Execution (kernel vs wasmtime) ──────
        let wt_orig = match WtModule::new(engine, &orig_wasm) {
            Ok(m) => m,
            Err(err) => {
                record_failure(WasmSmithFailure {
                    base_seed: cfg.base_seed,
                    attempt_index,
                    lifted_index,
                    stage: "wasmtime_compile_orig",
                    detail: format!("wasmtime failed to compile orig wasm: {err}"),
                    wasm_bytes: orig_wasm,
                })?;
                continue;
            }
        };
        let wt_emit = match WtModule::new(engine, &emitted) {
            Ok(m) => m,
            Err(err) => {
                record_failure(WasmSmithFailure {
                    base_seed: cfg.base_seed,
                    attempt_index,
                    lifted_index,
                    stage: "wasmtime_compile_emitted",
                    detail: format!("wasmtime failed to compile emitted wasm: {err}"),
                    wasm_bytes: orig_wasm,
                })?;
                continue;
            }
        };

        'funcs: for func in &lifted.funcs {
            let Some(export_name) = func.export_name.as_deref() else {
                continue;
            };
            diff_funcs_checked += 1;
            let vec_seed = cfg
                .base_seed
                .wrapping_add((attempt_index as u64).wrapping_mul(31))
                .wrapping_add(u64::from(func.id.0));
            let vectors = build_input_vectors(&func.params, cfg.inputs_per_func, vec_seed);

            for (vec_idx, args) in vectors.iter().enumerate() {
                let mut orig_run = match run_wasmtime_compiled(
                    engine,
                    &wt_orig,
                    &lifted,
                    func,
                    args,
                    cfg.fuel_per_run,
                ) {
                    Ok(r) => r,
                    Err(detail) => {
                        record_failure(WasmSmithFailure {
                            base_seed: cfg.base_seed,
                            attempt_index,
                            lifted_index,
                            stage: "diff_wasmtime_orig",
                            detail: format!("func `{export_name}` vec {vec_idx}: {detail}"),
                            wasm_bytes: orig_wasm.clone(),
                        })?;
                        break 'funcs;
                    }
                };

                let mut emit_run = match run_wasmtime_compiled(
                    engine,
                    &wt_emit,
                    &lifted,
                    func,
                    args,
                    cfg.fuel_per_run,
                ) {
                    Ok(r) => r,
                    Err(detail) => {
                        record_failure(WasmSmithFailure {
                            base_seed: cfg.base_seed,
                            attempt_index,
                            lifted_index,
                            stage: "diff_wasmtime_emitted",
                            detail: format!("func `{export_name}` vec {vec_idx}: {detail}"),
                            wasm_bytes: orig_wasm.clone(),
                        })?;
                        break 'funcs;
                    }
                };

                let mut kern_run =
                    match run_kernel_func(&lifted, &registry, func.id, args, cfg.fuel_per_run) {
                        Ok(r) => r,
                        Err(detail) => {
                            record_failure(WasmSmithFailure {
                                base_seed: cfg.base_seed,
                                attempt_index,
                                lifted_index,
                                stage: "diff_kernel_eval",
                                detail: format!("func `{export_name}` vec {vec_idx}: {detail}"),
                                wasm_bytes: orig_wasm.clone(),
                            })?;
                            break 'funcs;
                        }
                    };

                let any_fuel = matches!(orig_run.outcome, ExecOutcome::Trap(TrapCode::OutOfFuel))
                    || matches!(emit_run.outcome, ExecOutcome::Trap(TrapCode::OutOfFuel))
                    || matches!(kern_run.outcome, ExecOutcome::Trap(TrapCode::OutOfFuel));

                if any_fuel {
                    let all_fuel =
                        matches!(orig_run.outcome, ExecOutcome::Trap(TrapCode::OutOfFuel))
                            && matches!(emit_run.outcome, ExecOutcome::Trap(TrapCode::OutOfFuel))
                            && matches!(kern_run.outcome, ExecOutcome::Trap(TrapCode::OutOfFuel));

                    if !all_fuel && cfg.retry_fuel_per_run > cfg.fuel_per_run {
                        if matches!(orig_run.outcome, ExecOutcome::Trap(TrapCode::OutOfFuel)) {
                            match run_wasmtime_compiled(
                                engine,
                                &wt_orig,
                                &lifted,
                                func,
                                args,
                                cfg.retry_fuel_per_run,
                            ) {
                                Ok(r) => orig_run = r,
                                Err(detail) => {
                                    record_failure(WasmSmithFailure {
                                        base_seed: cfg.base_seed,
                                        attempt_index,
                                        lifted_index,
                                        stage: "diff_wasmtime_orig_retry",
                                        detail: format!(
                                            "func `{export_name}` vec {vec_idx}: {detail}"
                                        ),
                                        wasm_bytes: orig_wasm.clone(),
                                    })?;
                                    break 'funcs;
                                }
                            }
                        }
                        if matches!(emit_run.outcome, ExecOutcome::Trap(TrapCode::OutOfFuel)) {
                            match run_wasmtime_compiled(
                                engine,
                                &wt_emit,
                                &lifted,
                                func,
                                args,
                                cfg.retry_fuel_per_run,
                            ) {
                                Ok(r) => emit_run = r,
                                Err(detail) => {
                                    record_failure(WasmSmithFailure {
                                        base_seed: cfg.base_seed,
                                        attempt_index,
                                        lifted_index,
                                        stage: "diff_wasmtime_emitted_retry",
                                        detail: format!(
                                            "func `{export_name}` vec {vec_idx}: {detail}"
                                        ),
                                        wasm_bytes: orig_wasm.clone(),
                                    })?;
                                    break 'funcs;
                                }
                            }
                        }
                        if matches!(kern_run.outcome, ExecOutcome::Trap(TrapCode::OutOfFuel)) {
                            match run_kernel_func(
                                &lifted,
                                &registry,
                                func.id,
                                args,
                                cfg.retry_fuel_per_run,
                            ) {
                                Ok(r) => kern_run = r,
                                Err(detail) => {
                                    record_failure(WasmSmithFailure {
                                        base_seed: cfg.base_seed,
                                        attempt_index,
                                        lifted_index,
                                        stage: "diff_kernel_eval_retry",
                                        detail: format!(
                                            "func `{export_name}` vec {vec_idx}: {detail}"
                                        ),
                                        wasm_bytes: orig_wasm.clone(),
                                    })?;
                                    break 'funcs;
                                }
                            }
                        }
                    }

                    let still_any_fuel =
                        matches!(orig_run.outcome, ExecOutcome::Trap(TrapCode::OutOfFuel))
                            || matches!(emit_run.outcome, ExecOutcome::Trap(TrapCode::OutOfFuel))
                            || matches!(kern_run.outcome, ExecOutcome::Trap(TrapCode::OutOfFuel));

                    if still_any_fuel {
                        if !matches!(orig_run.outcome, ExecOutcome::Trap(TrapCode::OutOfFuel))
                            && !matches!(emit_run.outcome, ExecOutcome::Trap(TrapCode::OutOfFuel))
                        {
                            if let Err(detail) = compare_runs(
                                "wasmtime_orig",
                                &orig_run,
                                "wasmtime_emit",
                                &emit_run,
                            ) {
                                record_failure(WasmSmithFailure {
                                    base_seed: cfg.base_seed,
                                    attempt_index,
                                    lifted_index,
                                    stage: "diff_roundtrip_mismatch",
                                    detail: format!(
                                        "func `{export_name}` args={args:?}: {detail}"
                                    ),
                                    wasm_bytes: orig_wasm.clone(),
                                })?;
                                break 'funcs;
                            }
                            if orig_run.fuel_consumed < 50
                                && matches!(
                                    kern_run.outcome,
                                    ExecOutcome::Trap(TrapCode::OutOfFuel)
                                )
                            {
                                record_failure(WasmSmithFailure {
                                    base_seed: cfg.base_seed,
                                    attempt_index,
                                    lifted_index,
                                    stage: "diff_kernel_hang",
                                    detail: format!(
                                        "func `{export_name}` args={args:?}: wasmtime finished in {} fuel ({:?}) while kernel exhausted {} fuel",
                                        orig_run.fuel_consumed,
                                        orig_run.outcome,
                                        cfg.retry_fuel_per_run
                                    ),
                                    wasm_bytes: orig_wasm.clone(),
                                })?;
                                break 'funcs;
                            }
                        }
                        diff_fuel_or_depth_skipped += 1;
                        continue;
                    }
                }

                if let Err(detail) = compare_runs("kernel", &kern_run, "wasmtime_orig", &orig_run) {
                    record_failure(WasmSmithFailure {
                        base_seed: cfg.base_seed,
                        attempt_index,
                        lifted_index,
                        stage: "diff_kernel_vs_wasmtime",
                        detail: format!("func `{export_name}` args={args:?}: {detail}"),
                        wasm_bytes: orig_wasm.clone(),
                    })?;
                    break 'funcs;
                }
                if let Err(detail) =
                    compare_runs("wasmtime_orig", &orig_run, "wasmtime_emit", &emit_run)
                {
                    record_failure(WasmSmithFailure {
                        base_seed: cfg.base_seed,
                        attempt_index,
                        lifted_index,
                        stage: "diff_roundtrip_mismatch",
                        detail: format!("func `{export_name}` args={args:?}: {detail}"),
                        wasm_bytes: orig_wasm.clone(),
                    })?;
                    break 'funcs;
                }
                diff_checks += 1;
            }
        }

        if cfg.trace {
            eprintln!("[trace] attempt={attempt_index} lifted={lifted_index} stage=cliff");
        }
        // ── Gate 3a: SMT Cliff Estimator (< 50 ms) ─────────────────────────
        let t_cliff = Instant::now();
        let _cliff = estimate_smt_cliff(&lifted, &registry);
        let cliff_ms = t_cliff.elapsed().as_secs_f64() * 1000.0;
        cliff_samples_ms.push(cliff_ms);
        if cliff_ms > cfg.cliff_ceiling_ms {
            record_failure(WasmSmithFailure {
                base_seed: cfg.base_seed,
                attempt_index,
                lifted_index,
                stage: "cliff_blowup",
                detail: format!(
                    "estimate_smt_cliff took {cliff_ms:.2} ms (ceiling {:.1} ms)",
                    cfg.cliff_ceiling_ms
                ),
                wasm_bytes: orig_wasm.clone(),
            })?;
        }

        // ── Gate 3b: Step-Capped EgglogSimplifier ──────────────────────────
        let Some(entry) = select_entry_func(&lifted) else {
            record_failure(WasmSmithFailure {
                base_seed: cfg.base_seed,
                attempt_index,
                lifted_index,
                stage: "missing_entry_func",
                detail: "lifted module has no functions despite min_funcs=1".into(),
                wasm_bytes: orig_wasm,
            })?;
            continue;
        };

        if cfg.trace {
            eprintln!("[trace] attempt={attempt_index} lifted={lifted_index} stage=egglog");
        }
        let t_egg = Instant::now();
        match simplifier.simplify_region(&entry.body, &registry) {
            Ok((_simplified, eq_rep)) => {
                let egg_ms = t_egg.elapsed().as_secs_f64() * 1000.0;
                egglog_samples_ms.push(egg_ms);
                egglog_max_iters_seen = egglog_max_iters_seen.max(eq_rep.iters_run);
                egglog_max_nodes_after = egglog_max_nodes_after.max(eq_rep.nodes_after);

                if eq_rep.iters_run > cfg.egglog_config.max_iters {
                    record_failure(WasmSmithFailure {
                        base_seed: cfg.base_seed,
                        attempt_index,
                        lifted_index,
                        stage: "egglog_iter_cap",
                        detail: format!(
                            "EgglogSimplifier ran {} iters (cap {})",
                            eq_rep.iters_run, cfg.egglog_config.max_iters
                        ),
                        wasm_bytes: orig_wasm.clone(),
                    })?;
                }
                if egg_ms > cfg.egglog_ceiling_ms {
                    record_failure(WasmSmithFailure {
                        base_seed: cfg.base_seed,
                        attempt_index,
                        lifted_index,
                        stage: "egglog_blowup",
                        detail: format!(
                            "EgglogSimplifier took {egg_ms:.2} ms (ceiling {:.1} ms, nodes {} -> {})",
                            cfg.egglog_ceiling_ms, eq_rep.nodes_before, eq_rep.nodes_after
                        ),
                        wasm_bytes: orig_wasm.clone(),
                    })?;
                }
            }
            Err(err) => {
                record_failure(WasmSmithFailure {
                    base_seed: cfg.base_seed,
                    attempt_index,
                    lifted_index,
                    stage: "egglog_error",
                    detail: format!("EgglogSimplifier failed on `{}`: {err:?}", entry.name),
                    wasm_bytes: orig_wasm.clone(),
                })?;
            }
        }

        // ── Gate 3c: Bitwuzla Reflexive Self-Equivalence (f ≡ f != Sat) ────
        if smt_checked < cfg.smt_sample_count {
            if cfg.trace {
                eprintln!("[trace] attempt={attempt_index} lifted={lifted_index} stage=smt");
            }
            let t_smt = Instant::now();
            let smt_res = smt.check_equivalence(&lifted, &registry, &entry.body, &entry.body, None);
            let smt_ms = t_smt.elapsed().as_secs_f64() * 1000.0;
            smt_samples_ms.push(smt_ms);
            smt_checked += 1;

            if smt_ms > cfg.smt_ceiling_ms {
                record_failure(WasmSmithFailure {
                    base_seed: cfg.base_seed,
                    attempt_index,
                    lifted_index,
                    stage: "smt_blowup",
                    detail: format!(
                        "Bitwuzla reflexive check took {smt_ms:.2} ms (ceiling {:.1} ms)",
                        cfg.smt_ceiling_ms
                    ),
                    wasm_bytes: orig_wasm.clone(),
                })?;
            }

            match smt_res {
                Ok(SmtResult::Unsat) => {
                    smt_unsat += 1;
                }
                Ok(SmtResult::Unknown(_)) => {
                    smt_unknown += 1;
                }
                Ok(SmtResult::Sat(model)) => {
                    smt_sat += 1;
                    record_failure(WasmSmithFailure {
                        base_seed: cfg.base_seed,
                        attempt_index,
                        lifted_index,
                        stage: "smt_reflexive_unsound_sat",
                        detail: format!(
                            "SOUNDNESS BUG: reflexive check_equivalence(f, f) returned Sat({model:?}) on `{}`",
                            entry.name
                        ),
                        wasm_bytes: orig_wasm,
                    })?;
                }
                Err(SieveError::EncodingError(msg)) => {
                    smt_encoding_errors += 1;
                    record_failure(WasmSmithFailure {
                        base_seed: cfg.base_seed,
                        attempt_index,
                        lifted_index,
                        stage: "smt_encoding_error",
                        detail: format!("Bitwuzla EncodingError on `{}`: {msg}", entry.name),
                        wasm_bytes: orig_wasm,
                    })?;
                }
                Err(err) => {
                    record_failure(WasmSmithFailure {
                        base_seed: cfg.base_seed,
                        attempt_index,
                        lifted_index,
                        stage: "smt_error",
                        detail: format!("Bitwuzla reflexive check failed: {err:?}"),
                        wasm_bytes: orig_wasm,
                    })?;
                }
            }
        }
    }

    if lifted_count < cfg.target_lifted {
        return Err(WasmSmithFailure {
            base_seed: cfg.base_seed,
            attempt_index: attempts,
            lifted_index: lifted_count,
            stage: "insufficient_lifted_modules",
            detail: format!(
                "only lifted {lifted_count} / {} modules after {attempts} attempts (gen_errors={generation_errors}, skipped={skipped_unsupported}, reasons={skipped_reasons:?})",
                cfg.target_lifted
            ),
            wasm_bytes: Vec::new(),
        });
    }

    Ok((
        WasmSmithGateReport {
            base_seed: cfg.base_seed,
            attempts,
            generation_errors,
            skipped_unsupported,
            skipped_reasons,
            lifted: lifted_count,
            roundtrip_ok,
            diff_funcs_checked,
            diff_checks,
            diff_fuel_or_depth_skipped,
            cliff_latency: LatencyStats::from_samples(&mut cliff_samples_ms),
            egglog_latency: LatencyStats::from_samples(&mut egglog_samples_ms),
            egglog_max_iters_seen,
            egglog_max_nodes_after,
            smt_checked,
            smt_unsat,
            smt_unknown,
            smt_sat,
            smt_encoding_errors,
            smt_latency: LatencyStats::from_samples(&mut smt_samples_ms),
            total_elapsed_ms: total_start.elapsed().as_secs_f64() * 1000.0,
        },
        failures,
    ))
}
