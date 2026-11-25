//! Native x86-64 & ARM64 performance oracle (`gnomon profile` CLI + `gnomon_profile` MCP tool).
//!
//! Lowers strict `#![no_std]` Rust sources to native `x86_64` and `aarch64` assembly via
//! `rustc -C opt-level=3` and LLVM-23 `llc`, extracts exact static hardware metrics
//! (instruction count, branches, hardware integer divisions, SIMD ops, stack frame bytes,
//! register spills/reloads), runs LLVM-23 `llvm-mca` for pipeline cycle/IPC/RThroughput
//! modeling, and supports opt-in native host microbenchmarking (`--bench`) and side-by-side
//! `ref` vs `opt` speedup comparison.

use std::collections::HashSet;
use std::fmt::Write as _;
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Instant, SystemTime, UNIX_EPOCH};

use gnomon_kernel::StratumRegistry;
use serde::{Deserialize, Serialize};

use crate::GnomonError;
use crate::rust_bridge::generate_strata_rs;

pub const DEFAULT_X64_CPU: &str = "skylake";
pub const DEFAULT_ARM64_CPU: &str = "neoverse-v2";
const BENCH_WARMUP_ITERS: u64 = 10_000;
const BENCH_TIMED_ITERS: u64 = 1_000_000;

static PROFILER_TMP_COUNTER: AtomicU64 = AtomicU64::new(0);

/// RAII temporary directory guard cleaned up unconditionally on drop.
struct TempDirGuard {
    path: PathBuf,
}

impl TempDirGuard {
    fn new(prefix: &str) -> Result<Self, GnomonError> {
        let pid = std::process::id();
        let seq = PROFILER_TMP_COUNTER.fetch_add(1, Ordering::Relaxed);
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0);
        let path = std::env::temp_dir().join(format!("{prefix}_{pid}_{seq}_{nanos}"));
        std::fs::create_dir_all(&path).map_err(|e| {
            GnomonError::Io(format!("failed creating temp dir '{}': {e}", path.display()))
        })?;
        Ok(Self { path })
    }

    fn path(&self) -> &Path {
        &self.path
    }
}

impl Drop for TempDirGuard {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.path);
    }
}

/// Supported native target architectures for the Gnomon performance oracle.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize, schemars::JsonSchema)]
#[serde(rename_all = "lowercase")]
pub enum ProfileArch {
    X64,
    Arm64,
}

impl ProfileArch {
    pub fn triple(self) -> &'static str {
        match self {
            ProfileArch::X64 => "x86_64-unknown-linux-gnu",
            ProfileArch::Arm64 => "aarch64-unknown-linux-gnu",
        }
    }

    pub fn as_str(self) -> &'static str {
        match self {
            ProfileArch::X64 => "x64",
            ProfileArch::Arm64 => "arm64",
        }
    }
}

/// Parses a single target architecture token (`x64`/`x86_64` or `arm64`/`aarch64`).
pub fn parse_target_arch(raw: &str) -> Result<ProfileArch, GnomonError> {
    match raw.trim().to_ascii_lowercase().as_str() {
        "x64" | "x86_64" | "x86-64" | "amd64" => Ok(ProfileArch::X64),
        "arm64" | "aarch64" => Ok(ProfileArch::Arm64),
        other => Err(GnomonError::InvalidInput(format!(
            "unknown profile target '{other}' (expected x64 or arm64)"
        ))),
    }
}

/// Parses a comma-separated target list such as `"x64,arm64"`.
pub fn parse_targets_csv(raw: &str) -> Result<Vec<ProfileArch>, GnomonError> {
    let mut out = Vec::new();
    for part in raw.split(',') {
        let trimmed = part.trim();
        if trimmed.is_empty() {
            continue;
        }
        let arch = parse_target_arch(trimmed)?;
        if !out.contains(&arch) {
            out.push(arch);
        }
    }
    if out.is_empty() {
        return Err(GnomonError::InvalidInput(
            "at least one profile target is required (x64, arm64)".into(),
        ));
    }
    Ok(out)
}

/// Built-in realistic hot-path input presets for `--bench` host microbenchmarking.
#[derive(
    Clone, Copy, Debug, Default, PartialEq, Eq, Hash, Serialize, Deserialize, schemars::JsonSchema,
)]
#[serde(rename_all = "kebab-case")]
pub enum BenchPreset {
    /// Deterministic pseudo-random positive values (original default).
    #[default]
    Default,
    /// Realistic 8-byte ASCII digit words (`"00000000".."99999999"`) mixed with
    /// occasional late-byte invalid edge cases (zero early-exit branch bias).
    #[serde(alias = "ascii_digits")]
    AsciiDigits,
    /// Realistic OMS hot-path values: valid FSM states `0..=7`, valid events `0..=7`,
    /// valid OUCH sides (`'B'`/`'S'`) & lengths `>= 48`, valid Barrett divisor/magic,
    /// valid prices/qtys/bps, and live stack buffers for pointer parameters.
    #[serde(alias = "oms_valid")]
    OmsValid,
}

impl BenchPreset {
    pub fn as_str(self) -> &'static str {
        match self {
            BenchPreset::Default => "default",
            BenchPreset::AsciiDigits => "ascii-digits",
            BenchPreset::OmsValid => "oms-valid",
        }
    }
}

/// Parses a `--bench-preset` token (`default`, `ascii-digits`, `oms-valid`).
pub fn parse_bench_preset(raw: &str) -> Result<BenchPreset, GnomonError> {
    match raw.trim().to_ascii_lowercase().as_str() {
        "" | "default" => Ok(BenchPreset::Default),
        "ascii-digits" | "ascii_digits" => Ok(BenchPreset::AsciiDigits),
        "oms-valid" | "oms_valid" => Ok(BenchPreset::OmsValid),
        other => Err(GnomonError::InvalidInput(format!(
            "unknown --bench-preset '{other}' (expected default, ascii-digits, or oms-valid)"
        ))),
    }
}

/// Parses `--bench-inputs` JSON (array of argument tuples, e.g. `[[3689348814741910323]]`).
pub fn parse_bench_inputs_json(raw: &str) -> Result<Vec<Vec<serde_json::Value>>, GnomonError> {
    let parsed: Vec<Vec<serde_json::Value>> = serde_json::from_str(raw).map_err(|e| {
        GnomonError::InvalidInput(format!(
            "invalid --bench-inputs JSON (expected array of argument tuples, e.g. '[[3689348814741910323]]'): {e}"
        ))
    })?;
    if parsed.is_empty() {
        return Err(GnomonError::InvalidInput(
            "--bench-inputs must contain at least one input tuple".into(),
        ));
    }
    Ok(parsed)
}

/// Request parameters for single-function or ref-vs-opt native profiling.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ProfileRequest {
    /// Inline Rust source for primary/reference target.
    pub content: Option<String>,
    /// File path to `.rs` source for primary/reference target.
    pub path: Option<String>,
    /// Target function symbol inside primary/reference source (auto-detected if omitted).
    pub entry: Option<String>,
    /// Optional inline Rust source for comparison (`opt`) target.
    pub compare_content: Option<String>,
    /// Optional file path to `.rs` source for comparison (`opt`) target.
    pub compare_path: Option<String>,
    /// Optional entry function symbol inside comparison (`opt`) source.
    /// When set without `compare_content`/`compare_path`, compares within the primary source.
    pub opt_entry: Option<String>,
    /// Target architectures (defaults to `[X64, Arm64]` if empty).
    pub targets: Vec<ProfileArch>,
    /// x86-64 target CPU (e.g. `"skylake"`).
    pub x64_cpu: String,
    /// ARM64 target CPU (e.g. `"neoverse-v2"`).
    pub arm64_cpu: String,
    /// Opt-in 1,000,000-iteration native host x86-64 microbenchmark.
    pub bench: bool,
    /// Optional explicit ring of hot-path input tuples for `--bench`
    /// (supports ints, floats, bools, `"0x..."`/ASCII strings, and `"buf"`/arrays for pointers).
    #[serde(default)]
    pub bench_inputs: Option<Vec<Vec<serde_json::Value>>>,
    /// Built-in realistic hot-path input preset for `--bench` (`default`, `ascii-digits`, `oms-valid`).
    #[serde(default)]
    pub bench_preset: BenchPreset,
}

impl Default for ProfileRequest {
    fn default() -> Self {
        Self {
            content: None,
            path: None,
            entry: None,
            compare_content: None,
            compare_path: None,
            opt_entry: None,
            targets: vec![ProfileArch::X64, ProfileArch::Arm64],
            x64_cpu: DEFAULT_X64_CPU.to_string(),
            arm64_cpu: DEFAULT_ARM64_CPU.to_string(),
            bench: false,
            bench_inputs: None,
            bench_preset: BenchPreset::Default,
        }
    }
}

/// Static assembly & `llvm-mca` hardware metrics for one `(function, arch)` pair.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TargetProfile {
    pub arch: ProfileArch,
    pub triple: String,
    pub cpu: String,
    pub lowering_backend: String,
    pub entry: String,
    pub instruction_count: usize,
    pub branch_count: usize,
    pub div_count: usize,
    pub simd_count: usize,
    pub stack_frame_bytes: u64,
    pub register_spills: usize,
    pub register_reloads: usize,
    pub total_cycles: Option<f64>,
    pub cycles_per_iter: Option<f64>,
    pub block_rthroughput: Option<f64>,
    pub ipc: Option<f64>,
    pub uops_per_cycle: Option<f64>,
    pub raw_mca_summary: String,
    pub assembly: String,
    #[serde(skip_serializing_if = "Vec::is_empty", default)]
    pub notes: Vec<String>,
}

/// Aggregated multi-target profile for a single exported Rust function.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FunctionProfile {
    pub entry: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_path: Option<String>,
    pub targets: Vec<TargetProfile>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub host_ns_per_op: Option<f64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub bench_mode: Option<String>,
    #[serde(skip_serializing_if = "Vec::is_empty", default)]
    pub notes: Vec<String>,
}

/// Per-architecture delta & speedup comparing `opt` against `ref`.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TargetDelta {
    pub arch: ProfileArch,
    pub cpu: String,
    pub ref_instructions: usize,
    pub opt_instructions: usize,
    pub instruction_delta: i64,
    pub branch_delta: i64,
    pub div_delta: i64,
    pub simd_delta: i64,
    pub stack_frame_delta: i64,
    pub spill_delta: i64,
    pub reload_delta: i64,
    pub cycle_speedup: Option<f64>,
    pub rthroughput_speedup: Option<f64>,
}

/// Side-by-side comparison summary (`ref` vs `opt`).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ProfileComparison {
    pub ref_entry: String,
    pub opt_entry: String,
    pub target_deltas: Vec<TargetDelta>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub host_speedup: Option<f64>,
}

/// Top-level JSON output returned by `gnomon profile` CLI and `gnomon_profile` MCP tool.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ProfileOutput {
    pub status: String,
    pub profile: FunctionProfile,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub opt_profile: Option<FunctionProfile>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub comparison: Option<ProfileComparison>,
    pub elapsed_ms: u128,
}

#[derive(Clone, Debug, Default)]
struct StaticAsmMetrics {
    instruction_count: usize,
    branch_count: usize,
    div_count: usize,
    simd_count: usize,
    stack_frame_bytes: u64,
    register_spills: usize,
    register_reloads: usize,
}

#[derive(Clone, Debug, Default)]
struct McaMetrics {
    total_cycles: Option<f64>,
    cycles_per_iter: Option<f64>,
    block_rthroughput: Option<f64>,
    ipc: Option<f64>,
    uops_per_cycle: Option<f64>,
    raw_mca_summary: String,
}

#[derive(Clone, Debug)]
struct CompiledTarget {
    arch: ProfileArch,
    cpu: String,
    backend: String,
    asm: String,
    notes: Vec<String>,
}

struct LoadedSource {
    src: String,
    path: Option<PathBuf>,
}

/// Profiles a strict `#![no_std]` Rust function (and optional comparison `opt` function)
/// across the requested native target architectures (`x64`, `arm64`).
pub fn profile_rust(
    req: &ProfileRequest,
    registry: Option<&StratumRegistry>,
) -> Result<ProfileOutput, GnomonError> {
    let t0 = Instant::now();
    let targets = if req.targets.is_empty() {
        vec![ProfileArch::X64, ProfileArch::Arm64]
    } else {
        let mut dedup = Vec::new();
        for &arch in &req.targets {
            if !dedup.contains(&arch) {
                dedup.push(arch);
            }
        }
        dedup
    };
    let x64_cpu = if req.x64_cpu.trim().is_empty() {
        DEFAULT_X64_CPU.to_string()
    } else {
        req.x64_cpu.trim().to_string()
    };
    let arm64_cpu = if req.arm64_cpu.trim().is_empty() {
        DEFAULT_ARM64_CPU.to_string()
    } else {
        req.arm64_cpu.trim().to_string()
    };

    if let Some(ref inputs) = req.bench_inputs
        && inputs.is_empty()
    {
        return Err(GnomonError::InvalidInput(
            "bench_inputs must contain at least one input tuple".into(),
        ));
    }

    let primary = load_rust_source(req.content.as_deref(), req.path.as_deref(), "primary")?;
    let fallback_strata = registry.map(|reg| generate_strata_rs(reg, true));

    let has_compare =
        req.compare_content.is_some() || req.compare_path.is_some() || req.opt_entry.is_some();

    let same_file_compare = has_compare
        && req.compare_content.is_none()
        && (req.compare_path.is_none()
            || (req.path.is_some() && req.compare_path == req.path));

    let compiled_primary = compile_targets(
        &primary,
        &targets,
        &x64_cpu,
        &arm64_cpu,
        fallback_strata.as_deref(),
    )?;

    let ref_entry = resolve_entry_name(req.entry.as_deref(), &primary.src, &compiled_primary)?;
    let mut ref_profile = build_function_profile(
        &primary,
        &ref_entry,
        &compiled_primary,
        &x64_cpu,
        req.bench,
        req.bench_inputs.as_deref(),
        req.bench_preset,
        fallback_strata.as_deref(),
    )?;

    if !has_compare {
        return Ok(ProfileOutput {
            status: "OK".to_string(),
            profile: ref_profile,
            opt_profile: None,
            comparison: None,
            elapsed_ms: t0.elapsed().as_millis(),
        });
    }

    let (opt_source, compiled_opt) = if same_file_compare {
        (None, None)
    } else {
        let opt_src = load_rust_source(
            req.compare_content.as_deref(),
            req.compare_path.as_deref(),
            "compare",
        )?;
        let compiled = compile_targets(
            &opt_src,
            &targets,
            &x64_cpu,
            &arm64_cpu,
            fallback_strata.as_deref(),
        )?;
        (Some(opt_src), Some(compiled))
    };

    let opt_src_ref = opt_source.as_ref().unwrap_or(&primary);
    let opt_compiled_ref = compiled_opt.as_ref().unwrap_or(&compiled_primary);
    let requested_opt_entry = req.opt_entry.as_deref().or(req.entry.as_deref());
    let opt_entry =
        resolve_entry_name(requested_opt_entry, &opt_src_ref.src, opt_compiled_ref)?;

    let opt_profile = build_function_profile(
        opt_src_ref,
        &opt_entry,
        opt_compiled_ref,
        &x64_cpu,
        req.bench,
        req.bench_inputs.as_deref(),
        req.bench_preset,
        fallback_strata.as_deref(),
    )?;

    let comparison = compute_comparison(&ref_profile, &opt_profile);
    // Avoid duplicating redundant notes when comparing inside the same file.
    if same_file_compare && ref_profile.source_path.is_none() {
        ref_profile.source_path = opt_profile.source_path.clone();
    }

    Ok(ProfileOutput {
        status: "OK".to_string(),
        profile: ref_profile,
        opt_profile: Some(opt_profile),
        comparison: Some(comparison),
        elapsed_ms: t0.elapsed().as_millis(),
    })
}

fn load_rust_source(
    content: Option<&str>,
    path: Option<&str>,
    label: &str,
) -> Result<LoadedSource, GnomonError> {
    match (content, path) {
        (Some(src), opt_path) => {
            if src.trim().is_empty() {
                return Err(GnomonError::InvalidInput(format!(
                    "{label} Rust source content is empty"
                )));
            }
            Ok(LoadedSource {
                src: src.to_string(),
                path: opt_path.map(PathBuf::from),
            })
        }
        (None, Some(p)) => {
            let pb = PathBuf::from(p);
            let src = std::fs::read_to_string(&pb).map_err(|e| {
                GnomonError::Io(format!("failed reading {label} Rust file '{}': {e}", pb.display()))
            })?;
            if src.trim().is_empty() {
                return Err(GnomonError::InvalidInput(format!(
                    "{label} Rust file '{}' is empty",
                    pb.display()
                )));
            }
            Ok(LoadedSource { src, path: Some(pb) })
        }
        (None, None) => Err(GnomonError::InvalidInput(format!(
            "provide either Rust source content or a .rs file path for {label} target"
        ))),
    }
}

fn find_rustc_binary() -> PathBuf {
    if let Some(env_rustc) = std::env::var_os("RUSTC")
        && !env_rustc.is_empty()
    {
        let p = PathBuf::from(env_rustc);
        if p.is_file() {
            return p;
        }
    }
    if let Some(path_os) = std::env::var_os("PATH") {
        for dir in std::env::split_paths(&path_os) {
            let candidate = dir.join("rustc");
            if candidate.is_file() {
                return candidate;
            }
        }
    }
    if let Some(home) = std::env::var_os("HOME") {
        let cargo_rustc = PathBuf::from(home).join(".cargo").join("bin").join("rustc");
        if cargo_rustc.is_file() {
            return cargo_rustc;
        }
    }
    PathBuf::from("rustc")
}

fn find_llvm_tool(tool: &str, env_var: &str) -> Option<PathBuf> {
    if let Some(val) = std::env::var_os(env_var)
        && !val.is_empty()
    {
        let p = PathBuf::from(val);
        if p.is_file() {
            return Some(p);
        }
    }
    let llvm23 = PathBuf::from("/usr/lib/llvm-23/bin").join(tool);
    if llvm23.is_file() {
        return Some(llvm23);
    }
    if let Some(path_os) = std::env::var_os("PATH") {
        for dir in std::env::split_paths(&path_os) {
            let candidate = dir.join(tool);
            if candidate.is_file() {
                return Some(candidate);
            }
        }
    }
    let usr_bin = PathBuf::from("/usr/bin").join(tool);
    if usr_bin.is_file() {
        return Some(usr_bin);
    }
    None
}

fn has_installed_rust_target(rustc: &Path, triple: &str) -> bool {
    let Ok(out) = Command::new(rustc).args(["--print", "sysroot"]).output() else {
        return false;
    };
    if !out.status.success() {
        return false;
    }
    let sysroot = String::from_utf8_lossy(&out.stdout).trim().to_string();
    if sysroot.is_empty() {
        return false;
    }
    let target_lib_dir = PathBuf::from(sysroot)
        .join("lib")
        .join("rustlib")
        .join(triple)
        .join("lib");
    target_lib_dir.is_dir()
}

/// Rewrites Wasm-only `core::arch::wasm32` panic/memory helpers so strict `#![no_std]`
/// Wasm-authored OMS kernels compile cleanly to native x86-64 and ARM64 assembly.
fn sanitize_for_native_asm(src: &str) -> (String, Vec<String>) {
    let mut out = src.to_string();
    let mut notes = Vec::new();
    if out.contains("core::arch::wasm32::unreachable()") {
        out = out.replace("core::arch::wasm32::unreachable()", "loop {}");
        notes.push("rewrote core::arch::wasm32::unreachable() -> loop {} for native lowering".into());
    }
    if out.contains("core::arch::wasm32::memory_size(0)") {
        out = out.replace("core::arch::wasm32::memory_size(0)", "256usize");
        notes.push("rewrote core::arch::wasm32::memory_size(0) -> 256usize for native lowering".into());
    }
    if out.contains("use core::arch::wasm32::unreachable;") {
        out = out.replace(
            "use core::arch::wasm32::unreachable;",
            "#[inline(always)] fn unreachable() -> ! { loop {} }",
        );
        notes.push("rewrote `use core::arch::wasm32::unreachable;` for native lowering".into());
    }
    (out, notes)
}

/// Disables all `#[panic_handler]` items via `#[cfg(any())]` so a `#![no_std]` object file
/// links cleanly into a `std` native host microbenchmark binary without duplicate
/// `rust_begin_unwind` AND without orphaning preceding outer attributes such as
/// `#[cfg(target_arch = "wasm32")]` onto the next function.
fn strip_panic_handler(src: &str) -> String {
    src.replace("#[panic_handler]", "#[cfg(any())]")
}

/// Strips x86-64 target datalayout/triple and CPU/feature attribute tags from LLVM IR
/// before passing it to `llc -mtriple=aarch64-unknown-linux-gnu -mcpu=<cpu>`.
fn strip_target_ir_metadata(ir: &str) -> String {
    let mut out = String::with_capacity(ir.len());
    for line in ir.lines() {
        let trimmed = line.trim_start();
        if trimmed.starts_with("target datalayout = ") || trimmed.starts_with("target triple = ") {
            continue;
        }
        if trimmed.starts_with("attributes #") {
            let cleaned = strip_ir_quoted_attr(line, "target-cpu");
            let cleaned = strip_ir_quoted_attr(&cleaned, "target-features");
            let cleaned = strip_ir_quoted_attr(&cleaned, "tune-cpu");
            out.push_str(&cleaned);
            out.push('\n');
        } else {
            out.push_str(line);
            out.push('\n');
        }
    }
    out
}

fn strip_ir_quoted_attr(line: &str, key: &str) -> String {
    let pattern = format!("\"{key}\"=\"");
    let mut cur = line.to_string();
    while let Some(pos) = cur.find(&pattern) {
        let val_start = pos + pattern.len();
        if let Some(rel_end) = cur[val_start..].find('"') {
            let mut end = val_start + rel_end + 1;
            if cur.as_bytes().get(end) == Some(&b' ') {
                end += 1;
            }
            cur.replace_range(pos..end, "");
        } else {
            break;
        }
    }
    cur
}

fn stage_rust_file(
    tmp: &TempDirGuard,
    filename: &str,
    sanitized_src: &str,
    orig_path: Option<&Path>,
    fallback_strata_rs: Option<&str>,
) -> Result<PathBuf, GnomonError> {
    let staged = tmp.path().join(filename);
    std::fs::write(&staged, sanitized_src).map_err(|e| {
        GnomonError::Io(format!("failed writing staged rust source '{}': {e}", staged.display()))
    })?;
    if sanitized_src.contains("mod strata") {
        let sibling = orig_path
            .and_then(|p| p.parent())
            .map(|dir| dir.join("strata.rs"))
            .filter(|p| p.is_file());
        if let Some(sib) = sibling {
            let body = std::fs::read_to_string(&sib).map_err(|e| {
                GnomonError::Io(format!("failed reading sibling '{}': {e}", sib.display()))
            })?;
            std::fs::write(tmp.path().join("strata.rs"), body).map_err(|e| {
                GnomonError::Io(format!("failed staging sibling strata.rs: {e}"))
            })?;
        } else if let Some(strata_code) = fallback_strata_rs {
            std::fs::write(tmp.path().join("strata.rs"), strata_code).map_err(|e| {
                GnomonError::Io(format!("failed staging fallback strata.rs: {e}"))
            })?;
        }
    }
    Ok(staged)
}

fn format_cmd_error(tool: &str, out: &std::process::Output) -> String {
    let stderr = String::from_utf8_lossy(&out.stderr).trim().to_string();
    let stdout = String::from_utf8_lossy(&out.stdout).trim().to_string();
    let diag = if !stderr.is_empty() {
        stderr
    } else if !stdout.is_empty() {
        stdout
    } else {
        format!("exit status {}", out.status)
    };
    format!("{tool} failed:\n{diag}")
}

fn compile_targets(
    loaded: &LoadedSource,
    targets: &[ProfileArch],
    x64_cpu: &str,
    arm64_cpu: &str,
    fallback_strata_rs: Option<&str>,
) -> Result<Vec<CompiledTarget>, GnomonError> {
    let tmp = TempDirGuard::new("gnomon_profile")?;
    let (sanitized, base_notes) = sanitize_for_native_asm(&loaded.src);
    let staged_rs = stage_rust_file(
        &tmp,
        "target_lib.rs",
        &sanitized,
        loaded.path.as_deref(),
        fallback_strata_rs,
    )?;

    let rustc = find_rustc_binary();
    let llc = find_llvm_tool("llc", "LLVM_LLC");
    let mut results = Vec::with_capacity(targets.len());

    for &arch in targets {
        let mut notes = base_notes.clone();
        match arch {
            ProfileArch::X64 => {
                let (asm, backend) = if let Some(ref llc_bin) = llc {
                    let ll_path = tmp.path().join("x64.ll");
                    let s_path = tmp.path().join("x64.s");
                    let rustc_out = Command::new(&rustc)
                        .args([
                            "--edition=2021",
                            "--crate-type=lib",
                            "-C",
                            "opt-level=3",
                            "-C",
                            "panic=abort",
                            "-C",
                            &format!("target-cpu={x64_cpu}"),
                            "--emit=llvm-ir",
                        ])
                        .arg(&staged_rs)
                        .arg("-o")
                        .arg(&ll_path)
                        .output()
                        .map_err(|e| {
                            GnomonError::InvalidInput(format!(
                                "failed invoking rustc ('{}'): {e}",
                                rustc.display()
                            ))
                        })?;
                    if !rustc_out.status.success() {
                        return Err(map_native_compile_err(
                            &loaded.src,
                            format_cmd_error("rustc (x86_64 llvm-ir)", &rustc_out),
                        ));
                    }
                    let llc_out = Command::new(llc_bin)
                        .args([
                            "-O3",
                            "-mtriple=x86_64-unknown-linux-gnu",
                            &format!("-mcpu={x64_cpu}"),
                            "-x86-asm-syntax=intel",
                        ])
                        .arg(&ll_path)
                        .arg("-o")
                        .arg(&s_path)
                        .output()
                        .map_err(|e| {
                            GnomonError::Internal(format!(
                                "failed invoking llc ('{}'): {e}",
                                llc_bin.display()
                            ))
                        })?;
                    if !llc_out.status.success() {
                        return Err(GnomonError::Internal(format_cmd_error(
                            "llc (x86_64)",
                            &llc_out,
                        )));
                    }
                    let asm = std::fs::read_to_string(&s_path).map_err(|e| {
                        GnomonError::Io(format!("failed reading x86_64 asm: {e}"))
                    })?;
                    (asm, "rustc-llvm-ir+llc".to_string())
                } else {
                    let s_path = tmp.path().join("x64.s");
                    let rustc_out = Command::new(&rustc)
                        .args([
                            "--edition=2021",
                            "--crate-type=lib",
                            "-C",
                            "opt-level=3",
                            "-C",
                            "panic=abort",
                            "-C",
                            &format!("target-cpu={x64_cpu}"),
                            "--emit=asm",
                            "-C",
                            "llvm-args=-x86-asm-syntax=intel",
                        ])
                        .arg(&staged_rs)
                        .arg("-o")
                        .arg(&s_path)
                        .output()
                        .map_err(|e| {
                            GnomonError::InvalidInput(format!(
                                "failed invoking rustc ('{}'): {e}",
                                rustc.display()
                            ))
                        })?;
                    if !rustc_out.status.success() {
                        return Err(map_native_compile_err(
                            &loaded.src,
                            format_cmd_error("rustc (x86_64 asm)", &rustc_out),
                        ));
                    }
                    let asm = std::fs::read_to_string(&s_path).map_err(|e| {
                        GnomonError::Io(format!("failed reading x86_64 asm: {e}"))
                    })?;
                    (asm, "rustc-asm".to_string())
                };
                results.push(CompiledTarget {
                    arch,
                    cpu: x64_cpu.to_string(),
                    backend,
                    asm,
                    notes,
                });
            }
            ProfileArch::Arm64 => {
                let arm64_installed = has_installed_rust_target(&rustc, ProfileArch::Arm64.triple());
                let (asm, backend) = if arm64_installed {
                    let ll_path = tmp.path().join("arm64_native.ll");
                    let s_path = tmp.path().join("arm64.s");
                    if let Some(ref llc_bin) = llc {
                        let rustc_out = Command::new(&rustc)
                            .args([
                                "--edition=2021",
                                "--target",
                                ProfileArch::Arm64.triple(),
                                "--crate-type=lib",
                                "-C",
                                "opt-level=3",
                                "-C",
                                "panic=abort",
                                "-C",
                                &format!("target-cpu={arm64_cpu}"),
                                "--emit=llvm-ir",
                            ])
                            .arg(&staged_rs)
                            .arg("-o")
                            .arg(&ll_path)
                            .output()
                            .map_err(|e| {
                                GnomonError::InvalidInput(format!(
                                    "failed invoking rustc (aarch64): {e}"
                                ))
                            })?;
                        if !rustc_out.status.success() {
                            return Err(map_native_compile_err(
                                &loaded.src,
                                format_cmd_error("rustc (aarch64 llvm-ir)", &rustc_out),
                            ));
                        }
                        let llc_out = Command::new(llc_bin)
                            .args([
                                "-O3",
                                "-mtriple=aarch64-unknown-linux-gnu",
                                &format!("-mcpu={arm64_cpu}"),
                            ])
                            .arg(&ll_path)
                            .arg("-o")
                            .arg(&s_path)
                            .output()
                            .map_err(|e| {
                                GnomonError::Internal(format!(
                                    "failed invoking llc ('{}'): {e}",
                                    llc_bin.display()
                                ))
                            })?;
                        if !llc_out.status.success() {
                            return Err(GnomonError::Internal(format_cmd_error(
                                "llc (aarch64)",
                                &llc_out,
                            )));
                        }
                        let asm = std::fs::read_to_string(&s_path).map_err(|e| {
                            GnomonError::Io(format!("failed reading aarch64 asm: {e}"))
                        })?;
                        (asm, "rustc-aarch64+llc".to_string())
                    } else {
                        let rustc_out = Command::new(&rustc)
                            .args([
                                "--edition=2021",
                                "--target",
                                ProfileArch::Arm64.triple(),
                                "--crate-type=lib",
                                "-C",
                                "opt-level=3",
                                "-C",
                                "panic=abort",
                                "-C",
                                &format!("target-cpu={arm64_cpu}"),
                                "--emit=asm",
                            ])
                            .arg(&staged_rs)
                            .arg("-o")
                            .arg(&s_path)
                            .output()
                            .map_err(|e| {
                                GnomonError::InvalidInput(format!(
                                    "failed invoking rustc (aarch64 asm): {e}"
                                ))
                            })?;
                        if !rustc_out.status.success() {
                            return Err(map_native_compile_err(
                                &loaded.src,
                                format_cmd_error("rustc (aarch64 asm)", &rustc_out),
                            ));
                        }
                        let asm = std::fs::read_to_string(&s_path).map_err(|e| {
                            GnomonError::Io(format!("failed reading aarch64 asm: {e}"))
                        })?;
                        (asm, "rustc-aarch64-asm".to_string())
                    }
                } else {
                    let llc_bin = llc.as_ref().ok_or_else(|| {
                        GnomonError::Internal(
                            "aarch64-unknown-linux-gnu rustup target is not installed and LLVM `llc` binary was not found".into(),
                        )
                    })?;
                    let generic_ll = tmp.path().join("generic.ll");
                    let clean_ll = tmp.path().join("arm64_clean.ll");
                    let s_path = tmp.path().join("arm64.s");
                    let rustc_out = Command::new(&rustc)
                        .args([
                            "--edition=2021",
                            "--crate-type=lib",
                            "-C",
                            "opt-level=3",
                            "-C",
                            "panic=abort",
                            "--emit=llvm-ir",
                        ])
                        .arg(&staged_rs)
                        .arg("-o")
                        .arg(&generic_ll)
                        .output()
                        .map_err(|e| {
                            GnomonError::InvalidInput(format!(
                                "failed invoking rustc ('{}'): {e}",
                                rustc.display()
                            ))
                        })?;
                    if !rustc_out.status.success() {
                        return Err(map_native_compile_err(
                            &loaded.src,
                            format_cmd_error("rustc (generic llvm-ir for arm64)", &rustc_out),
                        ));
                    }
                    let raw_ir = std::fs::read_to_string(&generic_ll).map_err(|e| {
                        GnomonError::Io(format!("failed reading emitted llvm-ir: {e}"))
                    })?;
                    let cleaned_ir = strip_target_ir_metadata(&raw_ir);
                    std::fs::write(&clean_ll, cleaned_ir).map_err(|e| {
                        GnomonError::Io(format!("failed writing target-neutral llvm-ir: {e}"))
                    })?;
                    let llc_out = Command::new(llc_bin)
                        .args([
                            "-O3",
                            "-mtriple=aarch64-unknown-linux-gnu",
                            &format!("-mcpu={arm64_cpu}"),
                        ])
                        .arg(&clean_ll)
                        .arg("-o")
                        .arg(&s_path)
                        .output()
                        .map_err(|e| {
                            GnomonError::Internal(format!(
                                "failed invoking llc ('{}'): {e}",
                                llc_bin.display()
                            ))
                        })?;
                    if !llc_out.status.success() {
                        return Err(GnomonError::Internal(format_cmd_error(
                            "llc (aarch64)",
                            &llc_out,
                        )));
                    }
                    let asm = std::fs::read_to_string(&s_path).map_err(|e| {
                        GnomonError::Io(format!("failed reading aarch64 asm: {e}"))
                    })?;
                    notes.push(
                        "aarch64-unknown-linux-gnu rustup target not installed; lowered via rustc --emit=llvm-ir + llc -mtriple=aarch64-unknown-linux-gnu".into(),
                    );
                    (asm, "rustc-llvm-ir+llc".to_string())
                };
                results.push(CompiledTarget {
                    arch,
                    cpu: arm64_cpu.to_string(),
                    backend,
                    asm,
                    notes,
                });
            }
        }
    }

    Ok(results)
}

fn map_native_compile_err(orig_src: &str, msg: String) -> GnomonError {
    if orig_src.contains("core::arch::wasm32")
        && (msg.contains("wasm32") || msg.contains("v128"))
    {
        return GnomonError::InvalidInput(format!(
            "source uses Wasm-only `core::arch::wasm32` intrinsics that cannot be lowered directly to native x86-64/ARM64 (use portable Rust for native profiling):\n{msg}"
        ));
    }
    GnomonError::InvalidInput(msg)
}

fn resolve_entry_name(
    requested: Option<&str>,
    src: &str,
    compiled: &[CompiledTarget],
) -> Result<String, GnomonError> {
    if let Some(name) = requested
        && !name.trim().is_empty()
    {
        return Ok(name.trim().to_string());
    }
    if let Some(found) = find_first_exported_fn_in_rust(src) {
        return Ok(found);
    }
    if let Some(first) = compiled.first()
        && let Some(sym) = list_asm_function_symbols(&first.asm).into_iter().next()
    {
        return Ok(sym);
    }
    Err(GnomonError::InvalidInput(
        "could not auto-detect an exported `extern \"C\" fn` entry; pass --entry <FUNC>".into(),
    ))
}

fn find_first_exported_fn_in_rust(src: &str) -> Option<String> {
    let mut saw_no_mangle = false;
    let mut fallback: Option<String> = None;
    for raw_line in src.lines() {
        let line = raw_line.trim();
        if line.starts_with("//") {
            continue;
        }
        if line.contains("no_mangle") {
            saw_no_mangle = true;
            continue;
        }
        if let Some(idx) = line.find("extern \"C\" fn ") {
            let after = &line[idx + "extern \"C\" fn ".len()..];
            let name: String = after
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
                .collect();
            if !name.is_empty() {
                if saw_no_mangle {
                    return Some(name);
                }
                if fallback.is_none() {
                    fallback = Some(name);
                }
            }
            saw_no_mangle = false;
        } else if !line.is_empty() && !line.starts_with("#[") {
            saw_no_mangle = false;
        }
    }
    fallback
}

fn list_asm_function_symbols(asm: &str) -> Vec<String> {
    let mut syms = Vec::new();
    for line in asm.lines() {
        let trimmed = line.trim_end();
        if trimmed.is_empty() || trimmed.starts_with('\t') || trimmed.starts_with(' ') {
            continue;
        }
        let code = strip_asm_comment_any(trimmed).trim();
        if let Some(label) = code.strip_suffix(':')
            && !label.is_empty()
            && !label.starts_with('.')
            && !label.starts_with("_RNv")
            && !label.starts_with("_ZN")
            && label != "rust_begin_unwind"
        {
            syms.push(label.to_string());
        }
    }
    syms
}

fn strip_asm_comment_any(line: &str) -> &str {
    let s = line.split("//").next().unwrap_or(line);
    s.split('#').next().unwrap_or(s)
}

fn strip_asm_comment(arch: ProfileArch, line: &str) -> (&str, &str) {
    match arch {
        ProfileArch::X64 => match line.find('#') {
            Some(idx) => (&line[..idx], &line[idx..]),
            None => (line, ""),
        },
        ProfileArch::Arm64 => match line.find("//") {
            Some(idx) => (&line[..idx], &line[idx..]),
            None => (line, ""),
        },
    }
}

/// Extracts the exact assembly body (`<entry>:` through `.Lfunc_end` / `.size`).
pub(crate) fn extract_function_asm(asm: &str, entry: &str) -> Result<String, GnomonError> {
    let mut capturing = false;
    let mut lines = Vec::new();
    let label_prefix = format!("{entry}:");
    let size_prefix_tab = format!(".size\t{entry},");
    let size_prefix_sp = format!(".size {entry},");

    for line in asm.lines() {
        let trimmed_start = line.trim_start();
        if !capturing {
            if !line.starts_with(' ') && !line.starts_with('\t') {
                let code = strip_asm_comment_any(line).trim();
                if code == label_prefix {
                    capturing = true;
                    lines.push(line);
                }
            }
            continue;
        }

        if trimmed_start.starts_with(".Lfunc_end")
            || trimmed_start.starts_with(&size_prefix_tab)
            || trimmed_start.starts_with(&size_prefix_sp)
            || trimmed_start.starts_with(".cfi_endproc")
            || trimmed_start.starts_with(".section")
            || trimmed_start.starts_with(".ident")
        {
            break;
        }
        // Stop if another top-level non-local function label begins.
        if !line.starts_with(' ') && !line.starts_with('\t') && !trimmed_start.starts_with('.') {
            let code = strip_asm_comment_any(line).trim();
            if code.ends_with(':') && !code.starts_with('.') {
                break;
            }
        }
        lines.push(line);
    }

    if !capturing {
        let available = list_asm_function_symbols(asm);
        return Err(GnomonError::InvalidInput(format!(
            "entry function '{entry}' not found in emitted assembly (available exported symbols: {available:?})"
        )));
    }

    Ok(lines.join("\n"))
}

fn parse_imm_u64(tok: &str) -> Option<u64> {
    let cleaned = tok
        .trim()
        .trim_start_matches('#')
        .trim_end_matches([',', ']', '!']);
    if let Some(hex) = cleaned.strip_prefix("0x").or_else(|| cleaned.strip_prefix("0X")) {
        u64::from_str_radix(hex, 16).ok()
    } else {
        cleaned.parse::<u64>().ok()
    }
}

fn parse_signed_imm_i64(tok: &str) -> Option<i64> {
    let cleaned = tok
        .trim()
        .trim_start_matches('#')
        .trim_end_matches([',', ']', '!']);
    if let Some(neg) = cleaned.strip_prefix('-') {
        parse_imm_u64(neg).map(|v| -(v as i64))
    } else {
        parse_imm_u64(cleaned).map(|v| v as i64)
    }
}

fn is_x64_branch(mnemonic: &str) -> bool {
    if mnemonic == "loop" || mnemonic == "loope" || mnemonic == "loopne" || mnemonic == "loopz" || mnemonic == "loopnz" {
        return true;
    }
    mnemonic.starts_with('j')
}

fn is_arm64_branch(mnemonic: &str) -> bool {
    matches!(mnemonic, "b" | "cbz" | "cbnz" | "tbz" | "tbnz" | "br")
        || mnemonic.starts_with("b.")
}

fn is_x64_simd_operands(operands: &str) -> bool {
    for tok in operands.split(|c: char| !c.is_ascii_alphanumeric() && c != '_') {
        if let Some(rest) = tok
            .strip_prefix("xmm")
            .or_else(|| tok.strip_prefix("ymm"))
            .or_else(|| tok.strip_prefix("zmm"))
            && !rest.is_empty()
            && rest.chars().all(|c| c.is_ascii_digit())
        {
            return true;
        }
    }
    false
}

fn is_arm64_simd_operands(operands: &str) -> bool {
    // Match NEON vector registers v0..v31 (e.g. `v0.4s`, `v12.2d`, `v3`) and q0..q31.
    for raw_tok in operands.split(|c: char| c.is_ascii_whitespace() || matches!(c, ',' | '[' | ']' | '{' | '}' | '!')) {
        if raw_tok.is_empty() || raw_tok.starts_with('.') || raw_tok.starts_with('#') {
            continue;
        }
        let base = raw_tok.split('.').next().unwrap_or(raw_tok);
        if let Some(rest) = base.strip_prefix('v').or_else(|| base.strip_prefix('q'))
            && !rest.is_empty()
            && rest.chars().all(|c| c.is_ascii_digit())
            && let Ok(num) = rest.parse::<u32>()
            && num <= 31
        {
            return true;
        }
    }
    false
}

fn extract_x64_red_zone_depth(operands: &str) -> Option<u64> {
    let idx = operands.find("[rsp - ")?;
    let after = &operands[idx + "[rsp - ".len()..];
    let num_str: String = after
        .chars()
        .take_while(|c| c.is_ascii_hexdigit() || *c == 'x' || *c == 'X')
        .collect();
    parse_imm_u64(&num_str)
}

fn extract_x64_rsp_pos_offset(operands: &str) -> Option<u64> {
    if operands.contains("[rsp]") {
        return Some(0);
    }
    let idx = operands.find("[rsp + ")?;
    let after = &operands[idx + "[rsp + ".len()..];
    let num_str: String = after
        .chars()
        .take_while(|c| c.is_ascii_hexdigit() || *c == 'x' || *c == 'X')
        .collect();
    parse_imm_u64(&num_str)
}

fn is_arm64_callee_saved_reg(reg: &str) -> bool {
    let base = reg.trim().trim_end_matches(',');
    if let Some(rest) = base.strip_prefix('x').or_else(|| base.strip_prefix('w'))
        && let Ok(n) = rest.parse::<u32>()
    {
        return (19..=30).contains(&n);
    }
    if let Some(rest) = base
        .strip_prefix('d')
        .or_else(|| base.strip_prefix('s'))
        .or_else(|| base.strip_prefix('q'))
        .or_else(|| base.strip_prefix('b'))
        && let Ok(n) = rest.parse::<u32>()
    {
        return (8..=15).contains(&n);
    }
    false
}

fn collect_arm64_cfi_regs(fn_asm: &str) -> HashSet<String> {
    let mut regs = HashSet::new();
    for line in fn_asm.lines() {
        let trimmed = line.trim();
        if let Some(rest) = trimmed
            .strip_prefix(".cfi_offset")
            .or_else(|| trimmed.strip_prefix(".cfi_restore"))
            && let Some(tok) = rest.split_whitespace().next()
        {
            let clean = tok.trim_end_matches(',');
            if let Some(num) = clean
                .strip_prefix('w')
                .or_else(|| clean.strip_prefix('x'))
            {
                regs.insert(format!("x{num}"));
                regs.insert(format!("w{num}"));
            } else if let Some(num) = clean
                .strip_prefix('b')
                .or_else(|| clean.strip_prefix('d'))
                .or_else(|| clean.strip_prefix('s'))
                .or_else(|| clean.strip_prefix('q'))
            {
                regs.insert(format!("d{num}"));
                regs.insert(format!("q{num}"));
                regs.insert(format!("s{num}"));
            }
        }
    }
    regs
}

fn arm64_sp_op_uses_only_callee_saved(
    mnemonic: &str,
    operands: &str,
    cfi_regs: &HashSet<String>,
) -> bool {
    if !matches!(mnemonic, "stp" | "ldp" | "str" | "ldr") {
        return false;
    }
    let Some(bracket) = operands.find('[') else {
        return false;
    };
    let regs_part = operands[..bracket].trim().trim_end_matches(',');
    let regs: Vec<&str> = regs_part
        .split(',')
        .map(|s| s.trim())
        .filter(|s| !s.is_empty())
        .collect();
    if regs.is_empty() {
        return false;
    }
    regs.iter()
        .all(|r| is_arm64_callee_saved_reg(r) && (cfi_regs.is_empty() || cfi_regs.contains(*r)))
}

fn comment_is_spill(comment: &str) -> bool {
    comment.contains("Spill") && !comment.contains("Reload")
}

fn comment_is_reload(comment: &str) -> bool {
    comment.contains("Reload")
}

/// Computes exact deterministic static hardware metrics from an extracted function's assembly.
fn analyze_function_asm(arch: ProfileArch, fn_asm: &str) -> StaticAsmMetrics {
    let mut metrics = StaticAsmMetrics::default();
    let mut sub_sp_bytes: u64 = 0;
    let mut max_red_zone: u64 = 0;

    // Pre-scan for explicit LLVM spill/reload comments and ARM64 CFI callee-saved registers.
    let mut has_explicit_spill_comments = false;
    for line in fn_asm.lines() {
        let (_, comment) = strip_asm_comment(arch, line);
        if comment_is_spill(comment) || comment_is_reload(comment) {
            has_explicit_spill_comments = true;
            break;
        }
    }
    let arm64_cfi_regs = if arch == ProfileArch::Arm64 {
        collect_arm64_cfi_regs(fn_asm)
    } else {
        HashSet::new()
    };

    // First pass: collect instructions and stack frame allocation size.
    struct ParsedInst<'a> {
        mnemonic: String,
        operands: &'a str,
        comment: &'a str,
        in_bb0: bool,
        before_ret_epilogue: bool,
    }

    let raw_lines: Vec<&str> = fn_asm.lines().collect();
    // Mark lines in straight-line fallthrough to `ret` (no intervening branch or label)
    // so ARM64 ABI epilogue `ldp`/`ldr` callee-saved restores scheduled alongside return
    // expressions are distinguished from genuine body register spills/reloads.
    let mut in_epilogue_block = vec![false; raw_lines.len()];
    if arch == ProfileArch::Arm64 {
        let mut reaches_ret = false;
        for idx in (0..raw_lines.len()).rev() {
            let (code_raw, _) = strip_asm_comment(arch, raw_lines[idx]);
            let code = code_raw.trim();
            if code.is_empty() || code.starts_with('.') {
                if code.ends_with(':') {
                    reaches_ret = false;
                }
                continue;
            }
            if code.ends_with(':') {
                reaches_ret = false;
                continue;
            }
            let mnemonic = code
                .split_whitespace()
                .next()
                .unwrap_or("")
                .to_ascii_lowercase();
            if mnemonic == "ret" {
                reaches_ret = true;
                continue;
            }
            if is_arm64_branch(&mnemonic) {
                reaches_ret = false;
                continue;
            }
            in_epilogue_block[idx] = reaches_ret;
        }
    }

    let mut insts: Vec<ParsedInst<'_>> = Vec::new();
    let mut in_bb0 = true;

    for (line_idx, line) in raw_lines.iter().enumerate() {
        let (code_raw, comment) = strip_asm_comment(arch, line);
        let code = code_raw.trim();
        if code.is_empty() {
            continue;
        }
        if code.ends_with(':') {
            if code.starts_with(".LBB") {
                in_bb0 = false;
            }
            continue;
        }
        if code.starts_with('.') {
            continue;
        }

        let mut parts = code.splitn(2, |c: char| c.is_ascii_whitespace());
        let mnemonic = parts.next().unwrap_or("").to_ascii_lowercase();
        let operands = parts.next().unwrap_or("").trim();
        if mnemonic.is_empty() {
            continue;
        }

        let before_ret_epilogue = in_epilogue_block[line_idx];

        // Stack frame accounting
        match arch {
            ProfileArch::X64 => {
                if mnemonic == "sub"
                    && let Some(rest) = operands.strip_prefix("rsp,")
                    && let Some(n) = parse_imm_u64(rest)
                {
                    sub_sp_bytes = sub_sp_bytes.saturating_add(n);
                }
                if let Some(rz) = extract_x64_red_zone_depth(operands) {
                    max_red_zone = max_red_zone.max(rz);
                }
            }
            ProfileArch::Arm64 => {
                if mnemonic == "sub" {
                    let ops: Vec<&str> = operands.split(',').map(|s| s.trim()).collect();
                    if ops.len() >= 3
                        && ops[0] == "sp"
                        && ops[1] == "sp"
                        && let Some(n) = parse_imm_u64(ops[2])
                    {
                        sub_sp_bytes = sub_sp_bytes.saturating_add(n);
                    }
                } else if matches!(mnemonic.as_str(), "stp" | "str")
                    && let Some(sp_idx) = operands.find("[sp,")
                    && operands.contains("]!")
                {
                    let after = &operands[sp_idx + "[sp,".len()..];
                    if let Some(imm) = parse_signed_imm_i64(after)
                        && imm < 0
                    {
                        sub_sp_bytes = sub_sp_bytes.saturating_add(imm.unsigned_abs());
                    }
                }
            }
        }

        insts.push(ParsedInst {
            mnemonic,
            operands,
            comment,
            in_bb0,
            before_ret_epilogue,
        });
    }

    metrics.stack_frame_bytes = if sub_sp_bytes > 0 {
        sub_sp_bytes
    } else {
        max_red_zone
    };

    for inst in &insts {
        metrics.instruction_count += 1;

        match arch {
            ProfileArch::X64 => {
                if is_x64_branch(&inst.mnemonic) {
                    metrics.branch_count += 1;
                }
                if matches!(inst.mnemonic.as_str(), "div" | "idiv") {
                    metrics.div_count += 1;
                }
                if is_x64_simd_operands(inst.operands) {
                    metrics.simd_count += 1;
                }

                if has_explicit_spill_comments {
                    if comment_is_spill(inst.comment) {
                        metrics.register_spills += 1;
                    } else if comment_is_reload(inst.comment) {
                        metrics.register_reloads += 1;
                    }
                } else {
                    // Fallback heuristic for non-verbose `rustc --emit=asm` output:
                    // Detect stores to `[rsp ...]` and loads from `[rsp - K]` or `[rsp + K]`
                    // inside the local frame (`K < sub_sp_bytes`), ignoring incoming stack args.
                    let mut ops = inst.operands.splitn(2, ',');
                    let dst = ops.next().unwrap_or("").trim();
                    let src = ops.next().unwrap_or("").trim();
                    if dst.contains("[rsp") {
                        let is_local_slot = dst.contains("[rsp - ")
                            || extract_x64_rsp_pos_offset(dst)
                                .is_some_and(|off| off < sub_sp_bytes);
                        if is_local_slot {
                            metrics.register_spills += 1;
                        }
                    } else if src.contains("[rsp") {
                        let is_local_slot = src.contains("[rsp - ")
                            || extract_x64_rsp_pos_offset(src)
                                .is_some_and(|off| off < sub_sp_bytes);
                        if is_local_slot {
                            metrics.register_reloads += 1;
                        }
                    }
                }
            }
            ProfileArch::Arm64 => {
                if is_arm64_branch(&inst.mnemonic) {
                    metrics.branch_count += 1;
                }
                if matches!(inst.mnemonic.as_str(), "udiv" | "sdiv") {
                    metrics.div_count += 1;
                }
                if is_arm64_simd_operands(inst.operands) {
                    metrics.simd_count += 1;
                }

                // Distinguish ARM64 ABI callee-saved prologue/epilogue saves (`stp/ldp x19..x30`)
                // from genuine register-allocator body spills/reloads.
                let is_abi_callee_save = (inst.in_bb0 || inst.before_ret_epilogue)
                    && arm64_sp_op_uses_only_callee_saved(
                        &inst.mnemonic,
                        inst.operands,
                        &arm64_cfi_regs,
                    );

                if !is_abi_callee_save {
                    if comment_is_spill(inst.comment) {
                        metrics.register_spills += 1;
                    } else if comment_is_reload(inst.comment) {
                        metrics.register_reloads += 1;
                    } else if !has_explicit_spill_comments && inst.operands.contains("[sp") {
                        if matches!(inst.mnemonic.as_str(), "str" | "stp" | "stur") {
                            metrics.register_spills += 1;
                        } else if matches!(inst.mnemonic.as_str(), "ldr" | "ldp" | "ldur") {
                            metrics.register_reloads += 1;
                        }
                    }
                }
            }
        }
    }

    metrics
}

fn prepare_asm_for_mca(arch: ProfileArch, fn_asm: &str) -> String {
    let mut out = String::with_capacity(fn_asm.len() + 32);
    if arch == ProfileArch::X64 {
        out.push_str(".intel_syntax noprefix\n");
    }
    for line in fn_asm.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }
        // Strip assembler directives that confuse or fail llvm-mca, keeping instructions & labels.
        if trimmed.starts_with('.') {
            if trimmed.ends_with(':') && !trimmed.starts_with(".Lfunc_end") {
                out.push_str(line);
                out.push('\n');
            }
            continue;
        }
        out.push_str(line);
        out.push('\n');
    }
    out
}

fn parse_mca_f64_after_colon(line: &str) -> Option<f64> {
    let rhs = line.split_once(':')?.1.trim();
    rhs.split_whitespace().next()?.parse::<f64>().ok()
}

fn parse_llvm_mca_output(stdout: &str) -> McaMetrics {
    let mut iterations: Option<f64> = None;
    let mut total_cycles: Option<f64> = None;
    let mut block_rthroughput: Option<f64> = None;
    let mut ipc: Option<f64> = None;
    let mut uops_per_cycle: Option<f64> = None;
    let mut summary_lines: Vec<&str> = Vec::new();

    for line in stdout.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("Iterations:") {
            iterations = parse_mca_f64_after_colon(trimmed);
        } else if trimmed.starts_with("Total Cycles:") {
            total_cycles = parse_mca_f64_after_colon(trimmed);
        } else if trimmed.starts_with("Block RThroughput:") {
            block_rthroughput = parse_mca_f64_after_colon(trimmed);
        } else if trimmed.starts_with("IPC:") {
            ipc = parse_mca_f64_after_colon(trimmed);
        } else if trimmed.starts_with("uOps Per Cycle:") {
            uops_per_cycle = parse_mca_f64_after_colon(trimmed);
        }

        if summary_lines.len() < 12 {
            if trimmed.starts_with("Instruction Info:") {
                break;
            }
            if !trimmed.is_empty() {
                summary_lines.push(line.trim_end());
            }
        }
    }

    let iters = iterations.filter(|&v| v > 0.0).unwrap_or(100.0);
    let cycles_per_iter = total_cycles.map(|c| (c / iters * 10_000.0).round() / 10_000.0);

    McaMetrics {
        total_cycles,
        cycles_per_iter,
        block_rthroughput,
        ipc,
        uops_per_cycle,
        raw_mca_summary: summary_lines.join("\n"),
    }
}

fn run_llvm_mca(arch: ProfileArch, cpu: &str, fn_asm: &str) -> (McaMetrics, Option<String>) {
    let Some(mca_bin) = find_llvm_tool("llvm-mca", "LLVM_MCA") else {
        return (
            McaMetrics::default(),
            Some("llvm-mca binary not found; skipped pipeline cycle simulation".into()),
        );
    };
    let mca_input = prepare_asm_for_mca(arch, fn_asm);
    let mut child = match Command::new(&mca_bin)
        .args([
            &format!("-mtriple={}", arch.triple()),
            &format!("-mcpu={cpu}"),
        ])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
    {
        Ok(c) => c,
        Err(e) => {
            return (
                McaMetrics::default(),
                Some(format!("failed spawning llvm-mca ('{}'): {e}", mca_bin.display())),
            );
        }
    };

    if let Some(mut stdin) = child.stdin.take() {
        let _ = stdin.write_all(mca_input.as_bytes());
    }
    let output = match child.wait_with_output() {
        Ok(o) => o,
        Err(e) => {
            return (
                McaMetrics::default(),
                Some(format!("failed waiting on llvm-mca: {e}")),
            );
        }
    };
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr).trim().to_string();
        return (
            McaMetrics::default(),
            Some(format!("llvm-mca exited with {}: {stderr}", output.status)),
        );
    }
    let stdout = String::from_utf8_lossy(&output.stdout);
    (parse_llvm_mca_output(&stdout), None)
}

#[derive(Clone, Debug)]
struct ParsedFnSig {
    params: Vec<(String, String)>,
    ret_ty: String,
}

/// Parses an exported `extern "C" fn <entry>(...) -> <ret>` signature from Rust source
/// to generate a typed native host microbenchmark harness.
fn parse_extern_c_signature(src: &str, entry: &str) -> Option<ParsedFnSig> {
    // Strip `//` line comments for simpler multi-line signature scanning.
    let mut cleaned = String::with_capacity(src.len());
    for line in src.lines() {
        let code = line.split("//").next().unwrap_or(line);
        cleaned.push_str(code);
        cleaned.push('\n');
    }

    let needle = format!("fn {entry}");
    let mut search_from = 0usize;
    while let Some(rel) = cleaned[search_from..].find(&needle) {
        let pos = search_from + rel;
        let after_name = pos + needle.len();
        search_from = after_name;

        // Verify exact identifier boundary before and after `entry`.
        if pos > 0 {
            let prev = cleaned.as_bytes()[pos - 1] as char;
            if prev.is_ascii_alphanumeric() || prev == '_' {
                continue;
            }
        }
        let tail = &cleaned[after_name..];
        let trimmed_tail = tail.trim_start();
        if !trimmed_tail.starts_with('(') {
            continue;
        }
        let open_paren = after_name + (tail.len() - trimmed_tail.len());
        let bytes = cleaned.as_bytes();
        let mut depth = 0usize;
        let mut close_paren = None;
        for (i, &b) in bytes.iter().enumerate().skip(open_paren) {
            if b == b'(' {
                depth += 1;
            } else if b == b')' {
                depth = depth.saturating_sub(1);
                if depth == 0 {
                    close_paren = Some(i);
                    break;
                }
            }
        }
        let close_paren = close_paren?;
        let params_raw = &cleaned[open_paren + 1..close_paren];
        let after_paren = &cleaned[close_paren + 1..];
        let brace_pos = after_paren.find('{')?;
        let ret_section = after_paren[..brace_pos].trim();
        let ret_ty = if let Some(after_arrow) = ret_section.strip_prefix("->") {
            after_arrow.trim().to_string()
        } else {
            "()".to_string()
        };

        let mut params = Vec::new();
        for item in split_top_level_commas(params_raw) {
            let item = item.trim();
            if item.is_empty() {
                continue;
            }
            let (pname, pty) = item.split_once(':')?;
            let pname = pname.trim().trim_start_matches("mut ").trim().to_string();
            let pty = pty.trim().to_string();
            params.push((pname, pty));
        }
        return Some(ParsedFnSig { params, ret_ty });
    }
    None
}

fn split_top_level_commas(s: &str) -> Vec<&str> {
    let mut parts = Vec::new();
    let mut start = 0usize;
    let mut angle = 0usize;
    let mut paren = 0usize;
    let mut bracket = 0usize;
    for (i, ch) in s.char_indices() {
        match ch {
            '<' => angle += 1,
            '>' => angle = angle.saturating_sub(1),
            '(' => paren += 1,
            ')' => paren = paren.saturating_sub(1),
            '[' => bracket += 1,
            ']' => bracket = bracket.saturating_sub(1),
            ',' if angle == 0 && paren == 0 && bracket == 0 => {
                parts.push(&s[start..i]);
                start = i + 1;
            }
            _ => {}
        }
    }
    if start <= s.len() {
        parts.push(&s[start..]);
    }
    parts
}

const PRESET_RING_LEN: usize = 256;

fn splitmix64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

fn default_ptr_buffer_setup(idx: usize, ptr_ty: &str) -> (String, String) {
    let is_mut = ptr_ty.starts_with("*mut ");
    let elem = ptr_ty
        .strip_prefix("*const ")
        .or_else(|| ptr_ty.strip_prefix("*mut "))
        .unwrap_or("u8")
        .trim();
    let ptr_method = if is_mut { "as_mut_ptr" } else { "as_ptr" };
    let setup = match elem {
        "f32" => format!(
            "let mut buf_{idx}: [f32; 128] = core::array::from_fn(|k| 100.25f32 + ((k & 15) as f32) * 0.25f32);"
        ),
        "f64" => format!(
            "let mut buf_{idx}: [f64; 64] = core::array::from_fn(|k| 100.25f64 + ((k & 15) as f64) * 0.25f64);"
        ),
        _ => format!("let mut buf_{idx} = [0x3736_3534_3332_3130u64; 64];"),
    };
    let arg = format!("std::hint::black_box(buf_{idx}.{ptr_method}() as {ptr_ty})");
    (setup, arg)
}

fn bench_param_setup_and_arg_default(idx: usize, ty: &str) -> Result<(Option<String>, String), String> {
    let t = ty.trim();
    // Deterministic non-trivial positive non-zero values (avoid div-by-0, i32::MIN/-1, NaN).
    let seed = format!(
        "(i.wrapping_mul(0x9e37_79b9_7f4a_7c15u64).wrapping_add({}u64) ^ acc)",
        (idx as u64 + 1).wrapping_mul(0x517c_c1b7_2722_0a95)
    );
    match t {
        "u64" => Ok((None, format!("std::hint::black_box(({seed} & 0x3fff_ffff_ffff_ffffu64) | 1u64)"))),
        "i64" => Ok((None, format!("std::hint::black_box((({seed} & 0x3fff_ffff_ffff_ffffu64) | 1u64) as i64)"))),
        "u32" => Ok((None, format!("std::hint::black_box(((({seed} >> 16) as u32) & 0x3fff_ffffu32) | 1u32)"))),
        "i32" => Ok((None, format!("std::hint::black_box((((({seed} >> 16) as u32) & 0x3fff_ffffu32) | 1u32) as i32)"))),
        "usize" => Ok((None, format!("std::hint::black_box(((({seed} & 0x3fff_ffffu64) | 1u64)) as usize)"))),
        "isize" => Ok((None, format!("std::hint::black_box(((({seed} & 0x3fff_ffffu64) | 1u64)) as isize)"))),
        "u16" => Ok((None, format!("std::hint::black_box(((({seed} >> 16) as u16) & 0x3fffu16) | 1u16)"))),
        "i16" => Ok((None, format!("std::hint::black_box((((({seed} >> 16) as u16) & 0x3fffu16) | 1u16) as i16)"))),
        "u8" => Ok((None, format!("std::hint::black_box(((({seed} >> 16) as u8) & 0x7fu8) | 1u8)"))),
        "i8" => Ok((None, format!("std::hint::black_box((((({seed} >> 16) as u8) & 0x7fu8) | 1u8) as i8)"))),
        "bool" => Ok((None, format!("std::hint::black_box(({seed} & 1u64) != 0)"))),
        "f32" => Ok((None, format!("std::hint::black_box((({seed} & 1023u64) as f32) * 0.125f32 + 1.0f32)"))),
        "f64" => Ok((None, format!("std::hint::black_box((({seed} & 1023u64) as f64) * 0.125f64 + 1.0f64)"))),
        _ if t.starts_with("*const ") || t.starts_with("*mut ") => {
            let (setup, arg) = default_ptr_buffer_setup(idx, t);
            Ok((Some(setup), arg))
        }
        other => Err(format!("unsupported bench parameter type '{other}'")),
    }
}

fn format_u64_for_int_type(u: u64, ty: &str) -> Result<String, String> {
    match ty {
        "u64" => Ok(format!("{u}u64")),
        "i64" => Ok(format!("({u}u64 as i64)")),
        "u32" => Ok(format!("({u}u64 as u32)")),
        "i32" => Ok(format!("({u}u64 as i32)")),
        "u16" => Ok(format!("({u}u64 as u16)")),
        "i16" => Ok(format!("({u}u64 as i16)")),
        "u8" => Ok(format!("({u}u64 as u8)")),
        "i8" => Ok(format!("({u}u64 as i8)")),
        "usize" => Ok(format!("({u}u64 as usize)")),
        "isize" => Ok(format!("({u}u64 as isize)")),
        other => Err(format!("expected integer type, got '{other}'")),
    }
}

fn format_i64_for_int_type(n: i64, ty: &str) -> Result<String, String> {
    match ty {
        "i64" => Ok(format!("{n}i64")),
        "u64" => Ok(format!("({n}i64 as u64)")),
        "i32" => Ok(format!("({n}i64 as i32)")),
        "u32" => Ok(format!("({n}i64 as u32)")),
        "i16" => Ok(format!("({n}i64 as i16)")),
        "u16" => Ok(format!("({n}i64 as u16)")),
        "i8" => Ok(format!("({n}i64 as i8)")),
        "u8" => Ok(format!("({n}i64 as u8)")),
        "isize" => Ok(format!("({n}i64 as isize)")),
        "usize" => Ok(format!("({n}i64 as usize)")),
        other => Err(format!("expected integer type, got '{other}'")),
    }
}

fn format_json_scalar_literal(val: &serde_json::Value, ty: &str) -> Result<String, String> {
    let t = ty.trim();
    match t {
        "u64" | "i64" | "u32" | "i32" | "u16" | "i16" | "u8" | "i8" | "usize" | "isize" => {
            if let Some(u) = val.as_u64() {
                format_u64_for_int_type(u, t)
            } else if let Some(n) = val.as_i64() {
                format_i64_for_int_type(n, t)
            } else if let Some(b) = val.as_bool() {
                format_u64_for_int_type(u64::from(b), t)
            } else if let Some(s) = val.as_str() {
                let st = s.trim();
                if let Some(hex) = st.strip_prefix("0x").or_else(|| st.strip_prefix("0X")) {
                    let clean: String = hex.chars().filter(|&c| c != '_').collect();
                    let u = u64::from_str_radix(&clean, 16)
                        .map_err(|_| format!("invalid hex literal '{s}' for type '{t}'"))?;
                    format_u64_for_int_type(u, t)
                } else {
                    let bytes = s.as_bytes();
                    match t {
                        "u8" | "i8" if bytes.len() == 1 => {
                            format_u64_for_int_type(u64::from(bytes[0]), t)
                        }
                        "u32" | "i32" if !bytes.is_empty() && bytes.len() <= 4 => {
                            let mut arr = [b'0'; 4];
                            arr[..bytes.len()].copy_from_slice(bytes);
                            format_u64_for_int_type(u64::from(u32::from_le_bytes(arr)), t)
                        }
                        "u64" | "i64" if !bytes.is_empty() && bytes.len() <= 8 => {
                            let mut arr = [b'0'; 8];
                            arr[..bytes.len()].copy_from_slice(bytes);
                            format_u64_for_int_type(u64::from_le_bytes(arr), t)
                        }
                        _ => Err(format!(
                            "cannot convert string '{s}' to parameter type '{t}'"
                        )),
                    }
                }
            } else {
                Err(format!("expected integer for parameter type '{t}', got {val}"))
            }
        }
        "f32" => {
            let f = val
                .as_f64()
                .ok_or_else(|| format!("expected float for parameter type 'f32', got {val}"))?;
            Ok(format!("f32::from_bits({:#010x}u32)", (f as f32).to_bits()))
        }
        "f64" => {
            let f = val
                .as_f64()
                .ok_or_else(|| format!("expected float for parameter type 'f64', got {val}"))?;
            Ok(format!("f64::from_bits({:#018x}u64)", f.to_bits()))
        }
        "bool" => {
            if let Some(b) = val.as_bool() {
                Ok(if b { "true".to_string() } else { "false".to_string() })
            } else if let Some(u) = val.as_u64() {
                Ok(if u != 0 { "true".to_string() } else { "false".to_string() })
            } else if let Some(n) = val.as_i64() {
                Ok(if n != 0 { "true".to_string() } else { "false".to_string() })
            } else {
                Err(format!("expected bool for parameter type 'bool', got {val}"))
            }
        }
        other => Err(format!("unsupported bench scalar parameter type '{other}'")),
    }
}

fn format_custom_ptr_param(
    idx: usize,
    ptr_ty: &str,
    values: &[&serde_json::Value],
    slot_expr: &str,
) -> Result<(String, String), String> {
    let is_mut = ptr_ty.starts_with("*mut ");
    let elem_ty = ptr_ty
        .strip_prefix("*const ")
        .or_else(|| ptr_ty.strip_prefix("*mut "))
        .unwrap_or("u8")
        .trim();
    let ptr_method = if is_mut { "as_mut_ptr" } else { "as_ptr" };

    let is_placeholder = |v: &serde_json::Value| -> bool {
        v.is_null()
            || v.is_i64()
            || v.is_u64()
            || matches!(v.as_str(), Some("buf" | "ptr" | "buffer" | ""))
    };

    if values.iter().all(|v| is_placeholder(v)) {
        return Ok(default_ptr_buffer_setup(idx, ptr_ty));
    }

    // Check if any tuple supplies an explicit array of element literals or a byte string.
    let mut max_len = 64usize;
    for v in values {
        if let Some(arr) = v.as_array() {
            max_len = max_len.max(arr.len());
        } else if let Some(s) = v.as_str()
            && !matches!(s, "buf" | "ptr" | "buffer" | "")
        {
            max_len = max_len.max(s.len());
        }
    }

    let default_elem = match elem_ty {
        "f32" => "100.0f32",
        "f64" => "100.0f64",
        "bool" => "false",
        "u8" | "i8" | "u16" | "i16" | "u32" | "i32" | "u64" | "i64" | "usize" | "isize" => "0",
        other => {
            return Err(format!(
                "unsupported custom buffer element type '{other}' for pointer '{ptr_ty}'"
            ));
        }
    };

    let mut rows = Vec::with_capacity(values.len());
    for v in values {
        let mut elems = Vec::with_capacity(max_len);
        if let Some(arr) = v.as_array() {
            for item in arr {
                elems.push(format_json_scalar_literal(item, elem_ty)?);
            }
            while elems.len() < max_len {
                elems.push(default_elem.to_string());
            }
        } else if let Some(s) = v.as_str()
            && !matches!(s, "buf" | "ptr" | "buffer" | "")
            && matches!(elem_ty, "u8" | "i8")
        {
            for &b in s.as_bytes() {
                elems.push(format_u64_for_int_type(u64::from(b), elem_ty)?);
            }
            while elems.len() < max_len {
                elems.push(default_elem.to_string());
            }
        } else if is_placeholder(v) {
            for _ in 0..max_len {
                elems.push(default_elem.to_string());
            }
        } else {
            return Err(format!(
                "expected null/\"buf\"/0, element array, or byte string for pointer parameter '{ptr_ty}', got {v}"
            ));
        }
        rows.push(format!("[{}]", elems.join(", ")));
    }

    let setup = format!(
        "let mut bufs_{idx}: [[{elem_ty}; {max_len}]; {}] = [{}];",
        values.len(),
        rows.join(", ")
    );
    let arg = if values.len() == 1 {
        format!("std::hint::black_box(bufs_{idx}[0].{ptr_method}() as {ptr_ty})")
    } else {
        format!("std::hint::black_box(bufs_{idx}[{slot_expr}].{ptr_method}() as {ptr_ty})")
    };
    Ok((setup, arg))
}

fn generate_ascii_digit_word(k: usize, rng: &mut u64) -> u64 {
    // Include canonical edge cases in slots 0..4, then 87.5% valid 8-byte ASCII digits
    // mixed with 12.5% late-byte (bytes 5..7) invalid delimiters so branchy loops run deep.
    match k {
        0 => u64::from_le_bytes(*b"00000000"),
        1 => u64::from_le_bytes(*b"99999999"),
        2 => u64::from_le_bytes(*b"33333333"),
        3 => u64::from_le_bytes(*b"12345678"),
        _ => {
            let mut bytes = [0u8; 8];
            let r1 = splitmix64(rng);
            for (b_idx, slot) in bytes.iter_mut().enumerate() {
                *slot = b'0' + (((r1 >> (b_idx * 8)) as u8) % 10);
            }
            let r2 = splitmix64(rng);
            if (r2 & 7) == 0 {
                // Inject a realistic late-byte non-digit (bytes 5, 6, or 7) ~12.5% of the time.
                const BAD_CHARS: [u8; 8] = [b'/', b':', b'.', b' ', b'A', b';', b'-', 0];
                let bad_pos = 5 + ((r2 >> 8) as usize % 3);
                bytes[bad_pos] = BAD_CHARS[((r2 >> 16) as usize) & 7];
            }
            u64::from_le_bytes(bytes)
        }
    }
}

fn generate_oms_valid_u64(entry: &str, pname: &str, ty: &str, k: usize, rng: &mut u64) -> u64 {
    let fn_lower = entry.to_ascii_lowercase();
    let norm = pname.trim_start_matches('_').to_ascii_lowercase();
    if fn_lower.contains("fix")
        || fn_lower.contains("digit")
        || fn_lower.contains("ascii")
        || norm.contains("ascii")
        || norm.contains("digit")
        || norm.contains("fix")
    {
        return generate_ascii_digit_word(k, rng);
    }

    let r = splitmix64(rng);
    match norm.as_str() {
        "d" | "denom" | "divisor" => 13,
        "magic" => (1u64 << 32) / 13, // 330_382_099
        "state" | "st" => {
            // Cover all 8 valid states 0..=7, favoring active states 0..=4 (75%).
            if (r & 3) == 0 {
                5 + ((r >> 8) % 3)
            } else {
                (r >> 8) % 5
            }
        }
        "event" | "ev" => r & 7,
        "max_qty" | "max_shares" | "limit" | "cap" => 1_000,
        "qty" | "shares" | "parent_qty" | "q0" | "q1" | "q2" | "q3" => {
            if (r & 15) == 0 {
                1_200
            } else {
                1 + (r % 900)
            }
        }
        "risk_flags" | "flags" => match r & 15 {
            0 => 1,
            1 => 2,
            2 => 4,
            3..=8 => 12, // short + locate confirmed (valid)
            _ => 0,
        },
        "collar_ok" => u64::from((r & 15) != 0),
        "kill_switch" | "halted" => 0,
        "meta" => {
            let side = if (r & 1) == 0 {
                u64::from(b'B')
            } else {
                u64::from(b'S')
            };
            let tif = (r >> 8) % 3_600;
            let shares = 1 + ((r >> 20) % 10_000);
            (side << 56) | (tif << 32) | shares
        }
        "side" => {
            if matches!(ty, "u8" | "i8") {
                if (r & 1) == 0 {
                    u64::from(b'B')
                } else {
                    u64::from(b'S')
                }
            } else {
                r & 1
            }
        }
        "tick" | "tick_size" => {
            const TICKS: [u64; 7] = [1, 2, 4, 8, 16, 32, 64];
            TICKS[(r as usize) % TICKS.len()]
        }
        "key" => 1 + (r % 65_535),
        "cl_ord_id" | "order_id" | "symbol" | "seed" | "salt" => r | 1,
        other if other == "len" || other.ends_with("_len") || other.contains("len") => {
            64 + (r % 192)
        }
        other if other.contains("notional") => 1_000_000_000,
        other if other.contains("bps") => 50 + (r % 450),
        other
            if other.contains("price")
                || matches!(other, "p0" | "p1" | "p2" | "p3" | "bid" | "ask") =>
        {
            10_000 + (r % 190_000)
        }
        _ => 1 + (r % 64),
    }
}

fn bench_param_setup_and_arg_preset(
    preset: BenchPreset,
    entry: &str,
    idx: usize,
    pname: &str,
    ty: &str,
    slot_expr: &str,
) -> Result<(Option<String>, String), String> {
    let t = ty.trim();
    if t.starts_with("*const ") || t.starts_with("*mut ") {
        let (setup, arg) = default_ptr_buffer_setup(idx, t);
        return Ok((Some(setup), arg));
    }

    let mut rng = 0x676e_6f6d_6f6e_3031u64
        ^ ((idx as u64 + 1).wrapping_mul(0x517c_c1b7_2722_0a95))
        ^ match preset {
            BenchPreset::Default => 0,
            BenchPreset::AsciiDigits => 0x1111_2222_3333_4444,
            BenchPreset::OmsValid => 0x5555_6666_7777_8888,
        };

    let mut literals = Vec::with_capacity(PRESET_RING_LEN);
    for k in 0..PRESET_RING_LEN {
        match t {
            "u64" | "i64" | "u32" | "i32" | "u16" | "i16" | "u8" | "i8" | "usize" | "isize" => {
                let raw = match preset {
                    BenchPreset::AsciiDigits => {
                        let norm = pname.trim_start_matches('_').to_ascii_lowercase();
                        if norm == "len" || norm.ends_with("_len") {
                            64
                        } else {
                            generate_ascii_digit_word(k, &mut rng)
                        }
                    }
                    BenchPreset::OmsValid => generate_oms_valid_u64(entry, pname, t, k, &mut rng),
                    BenchPreset::Default => splitmix64(&mut rng) | 1,
                };
                literals.push(format_u64_for_int_type(raw, t)?);
            }
            "f32" => {
                let r = splitmix64(&mut rng);
                let f = 100.0f32 + ((r & 255) as f32) * 0.25f32;
                literals.push(format!("f32::from_bits({:#010x}u32)", f.to_bits()));
            }
            "f64" => {
                let r = splitmix64(&mut rng);
                let f = 100.0f64 + ((r & 255) as f64) * 0.25f64;
                literals.push(format!("f64::from_bits({:#018x}u64)", f.to_bits()));
            }
            "bool" => {
                let r = splitmix64(&mut rng);
                literals.push(if (r & 1) != 0 { "true" } else { "false" }.to_string());
            }
            other => return Err(format!("unsupported bench parameter type '{other}'")),
        }
    }

    let setup = format!(
        "const INPUT_{idx}: [{t}; {PRESET_RING_LEN}] = [{}];",
        literals.join(", ")
    );
    let arg = format!("std::hint::black_box(INPUT_{idx}[{slot_expr}])");
    Ok((Some(setup), arg))
}

fn bench_ret_mix(ret_ty: &str, call_expr: &str) -> Result<String, String> {
    match ret_ty.trim() {
        "()" | "" => Ok(format!("{call_expr}; acc = acc.wrapping_add(1);")),
        "u64" => Ok(format!("let r = {call_expr}; acc = acc.wrapping_add(std::hint::black_box(r));")),
        "i64" | "u32" | "i32" | "usize" | "isize" | "u16" | "i16" | "u8" | "i8" | "bool" => {
            Ok(format!("let r = {call_expr}; acc = acc.wrapping_add(std::hint::black_box(r) as u64);"))
        }
        "f32" => Ok(format!("let r = {call_expr}; acc = acc.wrapping_add(std::hint::black_box(r).to_bits() as u64);")),
        "f64" => Ok(format!("let r = {call_expr}; acc = acc.wrapping_add(std::hint::black_box(r).to_bits());")),
        other => Err(format!("unsupported bench return type '{other}'")),
    }
}

struct HostBenchResult {
    ns_per_op: Option<f64>,
    note: Option<String>,
    mode: Option<String>,
}

impl HostBenchResult {
    fn skipped(note: String) -> Self {
        Self { ns_per_op: None, note: Some(note), mode: None }
    }
}

fn run_host_microbench(
    loaded: &LoadedSource,
    entry: &str,
    x64_cpu: &str,
    bench_inputs: Option<&[Vec<serde_json::Value>]>,
    bench_preset: BenchPreset,
    fallback_strata_rs: Option<&str>,
) -> Result<HostBenchResult, GnomonError> {
    let Some(sig) = parse_extern_c_signature(&loaded.src, entry) else {
        return Ok(HostBenchResult::skipped(format!(
            "host microbenchmark skipped: could not parse Rust signature for '{entry}'"
        )));
    };

    let mut setups = Vec::new();
    let mut arg_exprs = Vec::new();
    let mut extern_params = Vec::new();
    let mut slot_decl: Option<String> = None;
    let mut use_lcg_slot = false;
    let bench_mode: String;

    if let Some(tuples) = bench_inputs {
        if tuples.is_empty() {
            return Err(GnomonError::InvalidInput(
                "bench_inputs must contain at least one input tuple".into(),
            ));
        }
        for (t_idx, tuple) in tuples.iter().enumerate() {
            if tuple.len() != sig.params.len() {
                return Err(GnomonError::InvalidInput(format!(
                    "bench_inputs[{t_idx}] arity mismatch for '{entry}': expected {} argument(s), got {}",
                    sig.params.len(),
                    tuple.len()
                )));
            }
        }
        let n = tuples.len();
        bench_mode = format!("custom:{n}_tuples");
        let slot_expr = if n == 1 {
            "0usize".to_string()
        } else if n.is_power_of_two() {
            slot_decl = Some(format!("let slot = (i as usize) & {};", n - 1));
            "slot".to_string()
        } else {
            slot_decl = Some(format!("let slot = (i as usize) % {n};"));
            "slot".to_string()
        };

        for (idx, (_pname, pty)) in sig.params.iter().enumerate() {
            extern_params.push(format!("p{idx}: {pty}"));
            let t = pty.trim();
            let col_vals: Vec<&serde_json::Value> = tuples.iter().map(|row| &row[idx]).collect();
            if t.starts_with("*const ") || t.starts_with("*mut ") {
                let (setup, arg) = format_custom_ptr_param(idx, t, &col_vals, &slot_expr)
                    .map_err(|reason| {
                        GnomonError::InvalidInput(format!(
                            "invalid bench_inputs for '{entry}' param {idx}: {reason}"
                        ))
                    })?;
                setups.push(setup);
                arg_exprs.push(arg);
            } else {
                let mut lits = Vec::with_capacity(n);
                for (t_idx, val) in col_vals.iter().enumerate() {
                    let lit = format_json_scalar_literal(val, t).map_err(|reason| {
                        GnomonError::InvalidInput(format!(
                            "invalid bench_inputs[{t_idx}][{idx}] for '{entry}': {reason}"
                        ))
                    })?;
                    lits.push(lit);
                }
                setups.push(format!("const INPUT_{idx}: [{t}; {n}] = [{}];", lits.join(", ")));
                let arg = if n == 1 {
                    format!("std::hint::black_box(INPUT_{idx}[0])")
                } else {
                    format!("std::hint::black_box(INPUT_{idx}[{slot_expr}])")
                };
                arg_exprs.push(arg);
            }
        }
    } else if bench_preset == BenchPreset::Default {
        bench_mode = format!("preset:{}", bench_preset.as_str());
        for (idx, (_pname, pty)) in sig.params.iter().enumerate() {
            extern_params.push(format!("p{idx}: {pty}"));
            match bench_param_setup_and_arg_default(idx, pty) {
                Ok((setup, arg)) => {
                    if let Some(s) = setup {
                        setups.push(s);
                    }
                    arg_exprs.push(arg);
                }
                Err(reason) => {
                    return Ok(HostBenchResult::skipped(format!(
                        "host microbenchmark skipped: {reason}"
                    )));
                }
            }
        }
    } else {
        bench_mode = format!("preset:{}", bench_preset.as_str());
        let has_scalar = sig.params.iter().any(|(_, pty)| {
            let t = pty.trim();
            !t.starts_with("*const ") && !t.starts_with("*mut ")
        });
        if has_scalar {
            // Non-repeating 64-bit LCG index into the 256-entry hot-path table so TAGE branch
            // predictors cannot memorize a periodic ring on branchy FSM / SWAR ref kernels.
            use_lcg_slot = true;
            slot_decl = Some(
                "rng = rng.wrapping_mul(6364136223846793005u64).wrapping_add(1442695040888963407u64); let slot = (rng >> 56) as usize;".to_string(),
            );
        }
        for (idx, (pname, pty)) in sig.params.iter().enumerate() {
            extern_params.push(format!("p{idx}: {pty}"));
            match bench_param_setup_and_arg_preset(bench_preset, entry, idx, pname, pty, "slot") {
                Ok((setup, arg)) => {
                    if let Some(s) = setup {
                        setups.push(s);
                    }
                    arg_exprs.push(arg);
                }
                Err(reason) => {
                    return Ok(HostBenchResult::skipped(format!(
                        "host microbenchmark skipped: {reason}"
                    )));
                }
            }
        }
    }

    let call_expr = format!("unsafe {{ {entry}({}) }}", arg_exprs.join(", "));
    let mix_stmt = match bench_ret_mix(&sig.ret_ty, &call_expr) {
        Ok(s) => s,
        Err(reason) => {
            return Ok(HostBenchResult::skipped(format!(
                "host microbenchmark skipped: {reason}"
            )));
        }
    };

    let ret_decl = if sig.ret_ty.trim().is_empty() || sig.ret_ty.trim() == "()" {
        String::new()
    } else {
        format!(" -> {}", sig.ret_ty.trim())
    };

    let mut harness = String::new();
    let _ = writeln!(harness, "extern \"C\" {{");
    let _ = writeln!(harness, "    fn {entry}({}){ret_decl};", extern_params.join(", "));
    let _ = writeln!(harness, "}}");
    let _ = writeln!(harness, "fn main() {{");
    for s in &setups {
        let _ = writeln!(harness, "    {s}");
    }
    let _ = writeln!(harness, "    let mut acc: u64 = 1;");
    if use_lcg_slot {
        let _ = writeln!(harness, "    let mut rng: u64 = 0x243f_6a88_85a3_08d3;");
    }
    let _ = writeln!(harness, "    for i in 0..{BENCH_WARMUP_ITERS}u64 {{");
    if let Some(ref sd) = slot_decl {
        let _ = writeln!(harness, "        {sd}");
        if use_lcg_slot {
            let _ = writeln!(harness, "        let _ = i;");
        }
    } else if sig.params.is_empty() || bench_inputs.is_some_and(|t| t.len() == 1) {
        let _ = writeln!(harness, "        let _ = i;");
    }
    let _ = writeln!(harness, "        {mix_stmt}");
    let _ = writeln!(harness, "    }}");
    let _ = writeln!(harness, "    let mut best_ns = f64::INFINITY;");
    let _ = writeln!(harness, "    for _trial in 0..3 {{");
    if use_lcg_slot {
        let _ = writeln!(harness, "        rng = 0x243f_6a88_85a3_08d3;");
    }
    let _ = writeln!(harness, "        let t0 = std::time::Instant::now();");
    let _ = writeln!(harness, "        for i in 0..{BENCH_TIMED_ITERS}u64 {{");
    if let Some(ref sd) = slot_decl {
        let _ = writeln!(harness, "            {sd}");
        if use_lcg_slot {
            let _ = writeln!(harness, "            let _ = i;");
        }
    } else if sig.params.is_empty() || bench_inputs.is_some_and(|t| t.len() == 1) {
        let _ = writeln!(harness, "            let _ = i;");
    }
    let _ = writeln!(harness, "            {mix_stmt}");
    let _ = writeln!(harness, "        }}");
    let _ = writeln!(harness, "        let ns = t0.elapsed().as_nanos() as f64 / {BENCH_TIMED_ITERS}.0;");
    let _ = writeln!(harness, "        if ns < best_ns {{ best_ns = ns; }}");
    let _ = writeln!(harness, "    }}");
    let _ = writeln!(harness, "    std::hint::black_box(acc);");
    let _ = writeln!(harness, "    println!(\"{{:.6}}\", best_ns);");
    let _ = writeln!(harness, "}}");

    let tmp = match TempDirGuard::new("gnomon_bench") {
        Ok(t) => t,
        Err(e) => {
            return Ok(HostBenchResult::skipped(format!(
                "host microbenchmark temp dir failed: {e}"
            )));
        }
    };
    let (sanitized, _) = sanitize_for_native_asm(&loaded.src);
    let bench_src = strip_panic_handler(&sanitized);
    let staged_lib = match stage_rust_file(
        &tmp,
        "bench_target.rs",
        &bench_src,
        loaded.path.as_deref(),
        fallback_strata_rs,
    ) {
        Ok(p) => p,
        Err(e) => {
            return Ok(HostBenchResult::skipped(format!(
                "host microbenchmark staging failed: {e}"
            )));
        }
    };
    let obj_path = tmp.path().join("target.o");
    let harness_path = tmp.path().join("harness.rs");
    let bin_path = tmp.path().join("bench_bin");
    if let Err(e) = std::fs::write(&harness_path, &harness) {
        return Ok(HostBenchResult::skipped(format!(
            "host microbenchmark harness write failed: {e}"
        )));
    }

    let rustc = find_rustc_binary();
    let obj_out = match Command::new(&rustc)
        .args([
            "--edition=2021",
            "--crate-type=lib",
            "-C",
            "opt-level=3",
            "-C",
            "panic=abort",
            "-C",
            &format!("target-cpu={x64_cpu}"),
            "--emit=obj",
        ])
        .arg(&staged_lib)
        .arg("-o")
        .arg(&obj_path)
        .output()
    {
        Ok(o) => o,
        Err(e) => {
            return Ok(HostBenchResult::skipped(format!(
                "host microbenchmark obj compile failed: {e}"
            )));
        }
    };
    if !obj_out.status.success() {
        return Ok(HostBenchResult::skipped(format!(
            "host microbenchmark object build skipped: {}",
            format_cmd_error("rustc --emit=obj", &obj_out)
        )));
    }

    let bin_out = match Command::new(&rustc)
        .args([
            "--edition=2021",
            "-C",
            "opt-level=3",
            "-C",
            "panic=abort",
            "-C",
            "link-arg=-Wl,--gc-sections",
        ])
        .arg("-C")
        .arg(format!("link-arg={}", obj_path.display()))
        .arg(&harness_path)
        .arg("-o")
        .arg(&bin_path)
        .output()
    {
        Ok(o) => o,
        Err(e) => {
            return Ok(HostBenchResult::skipped(format!(
                "host microbenchmark link failed: {e}"
            )));
        }
    };
    if !bin_out.status.success() {
        return Ok(HostBenchResult::skipped(format!(
            "host microbenchmark link skipped: {}",
            format_cmd_error("rustc bench bin", &bin_out)
        )));
    }

    let run_out = match Command::new(&bin_path).output() {
        Ok(o) => o,
        Err(e) => {
            return Ok(HostBenchResult::skipped(format!(
                "host microbenchmark execution failed: {e}"
            )));
        }
    };
    if !run_out.status.success() {
        return Ok(HostBenchResult::skipped(format!(
            "host microbenchmark exited abnormally ({}); target may dereference non-host pointers",
            run_out.status
        )));
    }
    let stdout = String::from_utf8_lossy(&run_out.stdout);
    match stdout.trim().parse::<f64>() {
        Ok(ns) if ns.is_finite() && ns > 0.0 => Ok(HostBenchResult {
            ns_per_op: Some((ns * 10_000.0).round() / 10_000.0),
            note: None,
            mode: Some(bench_mode),
        }),
        _ => Ok(HostBenchResult::skipped(format!(
            "host microbenchmark returned non-numeric output: '{}'",
            stdout.trim()
        ))),
    }
}

#[allow(clippy::too_many_arguments)]
fn build_function_profile(
    loaded: &LoadedSource,
    entry: &str,
    compiled: &[CompiledTarget],
    x64_cpu: &str,
    bench: bool,
    bench_inputs: Option<&[Vec<serde_json::Value>]>,
    bench_preset: BenchPreset,
    fallback_strata_rs: Option<&str>,
) -> Result<FunctionProfile, GnomonError> {
    let mut target_profiles = Vec::with_capacity(compiled.len());
    for ct in compiled {
        let fn_asm = extract_function_asm(&ct.asm, entry)?;
        let stat = analyze_function_asm(ct.arch, &fn_asm);
        let (mca, mca_note) = run_llvm_mca(ct.arch, &ct.cpu, &fn_asm);
        let mut notes = ct.notes.clone();
        if let Some(n) = mca_note {
            notes.push(n);
        }
        target_profiles.push(TargetProfile {
            arch: ct.arch,
            triple: ct.arch.triple().to_string(),
            cpu: ct.cpu.clone(),
            lowering_backend: ct.backend.clone(),
            entry: entry.to_string(),
            instruction_count: stat.instruction_count,
            branch_count: stat.branch_count,
            div_count: stat.div_count,
            simd_count: stat.simd_count,
            stack_frame_bytes: stat.stack_frame_bytes,
            register_spills: stat.register_spills,
            register_reloads: stat.register_reloads,
            total_cycles: mca.total_cycles,
            cycles_per_iter: mca.cycles_per_iter,
            block_rthroughput: mca.block_rthroughput,
            ipc: mca.ipc,
            uops_per_cycle: mca.uops_per_cycle,
            raw_mca_summary: mca.raw_mca_summary,
            assembly: fn_asm,
            notes,
        });
    }

    let mut fn_notes = Vec::new();
    let (host_ns_per_op, bench_mode) = if bench {
        let res = run_host_microbench(
            loaded,
            entry,
            x64_cpu,
            bench_inputs,
            bench_preset,
            fallback_strata_rs,
        )?;
        if let Some(n) = res.note {
            fn_notes.push(n);
        }
        (res.ns_per_op, res.mode)
    } else {
        (None, None)
    };

    Ok(FunctionProfile {
        entry: entry.to_string(),
        source_path: loaded.path.as_ref().map(|p| p.display().to_string()),
        targets: target_profiles,
        host_ns_per_op,
        bench_mode,
        notes: fn_notes,
    })
}

fn ratio_speedup(ref_val: Option<f64>, opt_val: Option<f64>) -> Option<f64> {
    let (r, o) = (ref_val?, opt_val?);
    if r.is_finite() && o.is_finite() && o > 0.0 {
        Some((r / o * 10_000.0).round() / 10_000.0)
    } else {
        None
    }
}

fn compute_comparison(ref_p: &FunctionProfile, opt_p: &FunctionProfile) -> ProfileComparison {
    let mut target_deltas = Vec::new();
    for rt in &ref_p.targets {
        if let Some(ot) = opt_p.targets.iter().find(|t| t.arch == rt.arch) {
            target_deltas.push(TargetDelta {
                arch: rt.arch,
                cpu: rt.cpu.clone(),
                ref_instructions: rt.instruction_count,
                opt_instructions: ot.instruction_count,
                instruction_delta: ot.instruction_count as i64 - rt.instruction_count as i64,
                branch_delta: ot.branch_count as i64 - rt.branch_count as i64,
                div_delta: ot.div_count as i64 - rt.div_count as i64,
                simd_delta: ot.simd_count as i64 - rt.simd_count as i64,
                stack_frame_delta: ot.stack_frame_bytes as i64 - rt.stack_frame_bytes as i64,
                spill_delta: ot.register_spills as i64 - rt.register_spills as i64,
                reload_delta: ot.register_reloads as i64 - rt.register_reloads as i64,
                cycle_speedup: ratio_speedup(rt.total_cycles, ot.total_cycles),
                rthroughput_speedup: ratio_speedup(rt.block_rthroughput, ot.block_rthroughput),
            });
        }
    }
    ProfileComparison {
        ref_entry: ref_p.entry.clone(),
        opt_entry: opt_p.entry.clone(),
        target_deltas,
        host_speedup: ratio_speedup(ref_p.host_ns_per_op, opt_p.host_ns_per_op),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_strip_panic_handler_and_target_ir() {
        let src = r#"#![no_std]
#[cfg(target_arch = "wasm32")]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
#[no_mangle]
pub extern "C" fn f(x: i32) -> i32 { x + 1 }
"#;
        let stripped = strip_panic_handler(src);
        assert!(!stripped.contains("#[panic_handler]"));
        assert!(stripped.contains("#[cfg(target_arch = \"wasm32\")]\n#[cfg(any())]\nfn panic"));
        assert!(stripped.contains("pub extern \"C\" fn f"));

        let ir = "target datalayout = \"e-m:e\"\ntarget triple = \"x86_64-unknown-linux-gnu\"\nattributes #0 = { nounwind \"target-cpu\"=\"x86-64\" \"target-features\"=\"+sse2\" }\n";
        let cleaned = strip_target_ir_metadata(ir);
        assert!(!cleaned.contains("target datalayout"));
        assert!(!cleaned.contains("target triple"));
        assert!(!cleaned.contains("target-cpu"));
        assert!(!cleaned.contains("target-features"));
        assert!(cleaned.contains("nounwind"));
    }

    #[test]
    fn test_parse_llvm_mca_summary() {
        let sample = "\
Iterations:        100
Instructions:      18100
Total Cycles:      3688
Total uOps:        20700

Dispatch Width:    6
uOps Per Cycle:    5.61
IPC:               4.91
Block RThroughput: 34.5


Instruction Info:
[1]: #uOps
";
        let m = parse_llvm_mca_output(sample);
        assert_eq!(m.total_cycles, Some(3688.0));
        assert_eq!(m.cycles_per_iter, Some(36.88));
        assert_eq!(m.block_rthroughput, Some(34.5));
        assert_eq!(m.ipc, Some(4.91));
        assert_eq!(m.uops_per_cycle, Some(5.61));
        assert!(m.raw_mca_summary.contains("Block RThroughput: 34.5"));
    }

    #[test]
    fn test_static_asm_metrics_x64_and_arm64() {
        let x64_asm = "\
foo:
\t.cfi_startproc
\tsub\trsp, 48
\ttest\tesi, esi
\tje\t.LBB0_1
\tmov\tqword ptr [rsp - 16], r8 # 8-byte Spill
\tmov\trax, qword ptr [rsp - 16] # 8-byte Reload
\tdiv\trsi
\tvmulps\txmm0, xmm0, xmm1
\tret
.LBB0_1:
\txor\teax, eax
\tret
";
        let mx = analyze_function_asm(ProfileArch::X64, x64_asm);
        assert_eq!(mx.instruction_count, 10);
        assert_eq!(mx.branch_count, 1);
        assert_eq!(mx.div_count, 1);
        assert_eq!(mx.simd_count, 1);
        assert_eq!(mx.stack_frame_bytes, 48);
        assert_eq!(mx.register_spills, 1);
        assert_eq!(mx.register_reloads, 1);

        let arm_asm = "\
bar:
\t.cfi_startproc
\tstp\tx24, x23, [sp, #-32]!           // 16-byte Folded Spill
\t.cfi_offset w23, -8
\t.cfi_offset w24, -16
\tcbz\tw1, .LBB0_1
\tudiv\tx8, x0, x1
\tfmul\tv0.4s, v0.4s, v1.4s
\tldr\tq2, [x0]
\tldp\tx24, x23, [sp], #32             // 16-byte Folded Reload
\t.cfi_restore w23
\t.cfi_restore w24
\tret
.LBB0_1:
\tmov\tw0, wzr
\tret
";
        let ma = analyze_function_asm(ProfileArch::Arm64, arm_asm);
        assert_eq!(ma.instruction_count, 9);
        assert_eq!(ma.branch_count, 1);
        assert_eq!(ma.div_count, 1);
        assert_eq!(ma.simd_count, 2);
        assert_eq!(ma.stack_frame_bytes, 32);
        assert_eq!(ma.register_spills, 0);
        assert_eq!(ma.register_reloads, 0);
    }
}
