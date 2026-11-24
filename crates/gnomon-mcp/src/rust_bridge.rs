//! Strict `#![no_std]` Rust -> Wasm -> GnomonIR Strata bridge.
//!
//! Provides zero-TCB-churn compilation of strict `#![no_std]` Rust sources to
//! `wasm32-unknown-unknown`, binding of Wasm `import "stratum" "<op>"` calls to
//! `CallTarget::Stratum(id)`, auto-generation of `#![no_std]` `strata.rs` bindings,
//! and transitive standalone lowering of `CallTarget::Stratum` to local `FuncDef`s.

use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

use gnomon_kernel::{
    CallTarget, EffectOp, FuncDef, FuncId, HostCallId, HostContract, MemId, MemoryDef, Module, Op,
    Region, RegionBuilder, RegionNode, RegionRef, Stmt, StratumId, StratumOp, StratumRegistry,
    ValType,
};

use crate::GnomonError;

static TEMP_DIR_COUNTER: AtomicU64 = AtomicU64::new(0);

/// RAII temporary directory guard that deletes its directory on drop.
struct TempDirGuard {
    path: PathBuf,
}

impl TempDirGuard {
    fn new(prefix: &str) -> Result<Self, GnomonError> {
        let pid = std::process::id();
        let seq = TEMP_DIR_COUNTER.fetch_add(1, Ordering::Relaxed);
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0);
        let path = std::env::temp_dir().join(format!("{prefix}_{pid}_{seq}_{nanos}"));
        std::fs::create_dir_all(&path).map_err(|e| {
            GnomonError::Io(format!(
                "failed creating temp dir '{}': {e}",
                path.display()
            ))
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

/// Heuristic detector for inline strict `#![no_std]` Rust source snippets.
///
/// Rejects JSON documents (starting with `{`) so `.ir` JSON containing Rust-like
/// docstrings is never misclassified as Rust source.
pub fn looks_like_rust_source(src: &str) -> bool {
    let trimmed = src.trim_start();
    if trimmed.is_empty() || trimmed.starts_with('{') {
        return false;
    }
    trimmed.contains("#![no_std]")
        || trimmed.contains("pub extern \"C\" fn")
        || trimmed.contains("pub unsafe extern \"C\" fn")
        || trimmed.contains("#[unsafe(no_mangle)]")
        || trimmed.contains("#[no_mangle]")
        || trimmed.contains("#[panic_handler]")
        || trimmed.contains("wasm_import_module")
}

/// Resolves the `rustc` binary path (`PATH`, `RUSTC` env, or `$HOME/.cargo/bin/rustc`).
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

/// Compiles strict `#![no_std]` Rust source into `wasm32-unknown-unknown` `.wasm` bytes.
///
/// - Uses `--edition=2021 --target wasm32-unknown-unknown --crate-type=cdylib -O -C panic=abort`,
///   which compiles both Rust 2021 (`#[no_mangle]`, `extern "C"`) and Rust 2024
///   (`#[unsafe(no_mangle)]`, `unsafe extern "C"`) syntax, matching `examples/oms_strata/*.rs`.
/// - When `source_path` is provided and exists on disk, `rustc` is invoked directly on
///   `source_path` (with `-o <temp>/out.wasm`) so sibling modules such as `mod strata;` resolve
///   naturally. If `strata_dir` supplies a `strata.rs` and `source_path`'s directory does not,
///   a temporary copy alongside `strata.rs` is compiled instead.
/// - When compiling inline `src` (`source_path == None`), `src` is written to `<temp>/lib.rs`
///   and any `strata.rs` in `strata_dir` is copied alongside it.
/// - All temporary files are cleaned up automatically on drop.
pub fn compile_rust_to_wasm(
    src: &str,
    source_path: Option<&Path>,
    strata_dir: Option<&Path>,
) -> Result<Vec<u8>, GnomonError> {
    let strata_rs_contents = match strata_dir {
        Some(dir) => {
            let candidate = dir.join("strata.rs");
            if candidate.is_file() {
                Some(std::fs::read_to_string(&candidate).map_err(|e| {
                    GnomonError::Io(format!(
                        "failed reading '{}': {e}",
                        candidate.display()
                    ))
                })?)
            } else {
                None
            }
        }
        None => None,
    };
    compile_rust_internal(src, source_path, strata_rs_contents.as_deref())
}

/// Compiles strict `#![no_std]` Rust source to `.wasm`, synthesizing `strata.rs` from
/// `registry` when compiling inline source (or a file missing a sibling `strata.rs`).
pub fn compile_rust_to_wasm_with_registry(
    src: &str,
    source_path: Option<&Path>,
    registry: Option<&StratumRegistry>,
) -> Result<Vec<u8>, GnomonError> {
    let generated_strata = registry.map(|reg| generate_strata_rs(reg, true));
    compile_rust_internal(src, source_path, generated_strata.as_deref())
}

fn compile_rust_internal(
    src: &str,
    source_path: Option<&Path>,
    fallback_strata_rs: Option<&str>,
) -> Result<Vec<u8>, GnomonError> {
    let tmp = TempDirGuard::new("gnomon_rustc")?;
    let out_wasm = tmp.path().join("out.wasm");

    let input_rs: PathBuf = match source_path {
        Some(p) if p.is_file() => {
            let sibling_strata_exists = p
                .parent()
                .map(|dir| dir.join("strata.rs").is_file())
                .unwrap_or(false);
            if !sibling_strata_exists
                && src.contains("mod strata")
                && let Some(strata_code) = fallback_strata_rs
            {
                let staged_rs = tmp.path().join("lib.rs");
                std::fs::write(&staged_rs, src).map_err(|e| {
                    GnomonError::Io(format!(
                        "failed writing staged rust source '{}': {e}",
                        staged_rs.display()
                    ))
                })?;
                let staged_strata = tmp.path().join("strata.rs");
                std::fs::write(&staged_strata, strata_code).map_err(|e| {
                    GnomonError::Io(format!(
                        "failed writing staged strata.rs '{}': {e}",
                        staged_strata.display()
                    ))
                })?;
                staged_rs
            } else {
                p.to_path_buf()
            }
        }
        _ => {
            let staged_rs = tmp.path().join("lib.rs");
            std::fs::write(&staged_rs, src).map_err(|e| {
                GnomonError::Io(format!(
                    "failed writing inline rust source '{}': {e}",
                    staged_rs.display()
                ))
            })?;
            if let Some(strata_code) = fallback_strata_rs {
                let staged_strata = tmp.path().join("strata.rs");
                std::fs::write(&staged_strata, strata_code).map_err(|e| {
                    GnomonError::Io(format!(
                        "failed writing inline strata.rs '{}': {e}",
                        staged_strata.display()
                    ))
                })?;
            }
            staged_rs
        }
    };

    let rustc = find_rustc_binary();
    let output = Command::new(&rustc)
        .args([
            "--edition=2021",
            "--target",
            "wasm32-unknown-unknown",
            "--crate-type=cdylib",
            "-O",
            "-C",
            "panic=abort",
        ])
        .arg(&input_rs)
        .arg("-o")
        .arg(&out_wasm)
        .output()
        .map_err(|e| {
            GnomonError::InvalidInput(format!(
                "failed to invoke rustc ('{}'): {e}",
                rustc.display()
            ))
        })?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr).trim().to_string();
        let stdout = String::from_utf8_lossy(&output.stdout).trim().to_string();
        let diag = if !stderr.is_empty() {
            stderr
        } else if !stdout.is_empty() {
            stdout
        } else {
            format!("exit status {}", output.status)
        };
        return Err(GnomonError::InvalidInput(format!(
            "rustc compilation failed:\n{diag}"
        )));
    }

    std::fs::read(&out_wasm).map_err(|e| {
        GnomonError::Io(format!(
            "failed reading compiled wasm '{}': {e}",
            out_wasm.display()
        ))
    })
}

/// Returns `true` if `module` declares any Wasm import from the `"stratum"` module.
pub fn module_has_stratum_imports(module: &Module) -> bool {
    module
        .host_contracts
        .iter()
        .any(|hc| hc.module_name == "stratum")
}

/// Returns `true` if any function in `module` contains a `CallTarget::Stratum(_)` call.
pub fn module_has_stratum_calls(module: &Module) -> bool {
    let mut found = false;
    for f in &module.funcs {
        visit_region_call_targets(&f.body, &mut |t| {
            if matches!(t, CallTarget::Stratum(_)) {
                found = true;
            }
        });
        if found {
            return true;
        }
    }
    false
}

/// Looks up a registered `StratumOp` by name, preferring promoted Strata over candidates.
fn lookup_stratum_by_name<'a>(
    registry: &'a StratumRegistry,
    name: &str,
) -> Option<&'a StratumOp> {
    if let Some(st) = registry.promoted().iter().find(|s| s.op.name == name) {
        return Some(&st.op);
    }
    registry.candidates().iter().find(|c| c.name == name)
}

/// Rewrites Wasm `import "stratum" "<op>"` `HostContract` entries into `CallTarget::Stratum(id)`.
///
/// - Every `HostContract` with `module_name == "stratum"` is resolved against `registry`
///   (promoted first, then candidates) and validated for exact `(params, results)` type equality.
/// - Remaining non-`"stratum"` `HostContract`s (e.g. `gnomon::gnomon_assume`, `gnomon::gnomon_assert`)
///   are compacted with dense `HostCallId(0..)` indices and all `CallTarget::Host(old_id)`
///   references are rewritten across every `FuncDef.body` and retained `HostContract` region.
pub fn bind_stratum_imports(
    mut module: Module,
    registry: &StratumRegistry,
) -> Result<Module, GnomonError> {
    if !module_has_stratum_imports(&module) {
        return Ok(module);
    }

    let mut remap: HashMap<HostCallId, CallTarget> =
        HashMap::with_capacity(module.host_contracts.len());
    let mut new_host_contracts: Vec<HostContract> = Vec::new();

    for hc in module.host_contracts {
        if hc.module_name == "stratum" {
            let op = lookup_stratum_by_name(registry, &hc.field_name).ok_or_else(|| {
                GnomonError::Registry(format!(
                    "unknown stratum import '{}' (not registered in promoted or candidate strata)",
                    hc.field_name
                ))
            })?;
            let hc_param_tys: Vec<ValType> = hc.params.iter().map(|&(_, ty)| ty).collect();
            let op_param_tys: Vec<ValType> = op.params.iter().map(|&(_, ty)| ty).collect();
            let hc_result_tys: Vec<ValType> = hc.results.iter().map(|&(_, ty)| ty).collect();
            if hc_param_tys != op_param_tys || hc_result_tys != op.results {
                return Err(GnomonError::Registry(format!(
                    "stratum import '{}' signature mismatch: wasm imports ({:?}) -> ({:?}), \
                     but registered stratum '{}' (id={}) has ({:?}) -> ({:?})",
                    hc.field_name,
                    hc_param_tys,
                    hc_result_tys,
                    op.name,
                    op.id.0,
                    op_param_tys,
                    op.results
                )));
            }
            remap.insert(hc.id, CallTarget::Stratum(op.id));
        } else {
            let new_id = HostCallId(u32::try_from(new_host_contracts.len()).map_err(|_| {
                GnomonError::InvalidInput("too many host contracts".into())
            })?);
            remap.insert(hc.id, CallTarget::Host(new_id));
            let mut updated = hc;
            updated.id = new_id;
            new_host_contracts.push(updated);
        }
    }

    let mut map_target = |target: CallTarget| -> Result<CallTarget, GnomonError> {
        match target {
            CallTarget::Host(old_id) => remap.get(&old_id).copied().ok_or_else(|| {
                GnomonError::InvalidInput(format!(
                    "dangling host call target HostCallId({}) during stratum import binding",
                    old_id.0
                ))
            }),
            other => Ok(other),
        }
    };

    for f in &mut module.funcs {
        f.body = rewrite_region_call_targets(&f.body, &mut map_target)?;
    }

    for hc in &mut new_host_contracts {
        hc.precondition = rewrite_region_call_targets(&hc.precondition, &mut map_target)?;
        hc.postcondition = rewrite_region_call_targets(&hc.postcondition, &mut map_target)?;
        if let Some(ref sim) = hc.sim_body {
            hc.sim_body = Some(rewrite_region_call_targets(sim, &mut map_target)?);
        }
    }

    module.host_contracts = new_host_contracts;
    Ok(module)
}

/// Transitively materializes every `CallTarget::Stratum(sid)` referenced by `module`
/// (and transitively by those Strata's bodies) as internal `FuncDef`s, returning a
/// 100% standalone, zero-`"stratum"`-import `Module` ready for `gnomon_wasm::emit_wasm`.
pub fn lower_module_strata(
    module: &Module,
    registry: &StratumRegistry,
) -> Result<Module, GnomonError> {
    let mut out = if module_has_stratum_imports(module) {
        bind_stratum_imports(module.clone(), registry)?
    } else {
        module.clone()
    };

    let mut initial_strata: BTreeSet<StratumId> = BTreeSet::new();
    for f in &out.funcs {
        collect_stratum_ids_in_region(&f.body, &mut initial_strata);
    }
    for hc in &out.host_contracts {
        collect_stratum_ids_in_region(&hc.precondition, &mut initial_strata);
        collect_stratum_ids_in_region(&hc.postcondition, &mut initial_strata);
        if let Some(ref sim) = hc.sim_body {
            collect_stratum_ids_in_region(sim, &mut initial_strata);
        }
    }

    if initial_strata.is_empty() {
        return Ok(out);
    }

    // Transitive DAG closure over Stratum dependencies.
    let mut visited: HashSet<StratumId> = HashSet::new();
    let mut worklist: VecDeque<StratumId> = initial_strata.into_iter().collect();
    let mut ops: Vec<&StratumOp> = Vec::new();

    while let Some(sid) = worklist.pop_front() {
        if !visited.insert(sid) {
            continue;
        }
        let op = registry.get_op(sid).ok_or_else(|| {
            GnomonError::Registry(format!(
                "cannot lower unknown stratum id {} (not registered in promoted or candidate strata)",
                sid.0
            ))
        })?;
        let mut deps = BTreeSet::new();
        collect_stratum_ids_in_region(&op.body, &mut deps);
        for dep in deps {
            if !visited.contains(&dep) {
                worklist.push_back(dep);
            }
        }
        ops.push(op);
    }

    // Deterministic ordering by ascending (layer, id).
    ops.sort_by_key(|op| (op.layer, op.id.0));

    let base_func_id = out
        .funcs
        .iter()
        .map(|f| f.id.0)
        .max()
        .map_or(0u32, |m| m.saturating_add(1));

    let mut stratum_to_func: HashMap<StratumId, FuncId> = HashMap::with_capacity(ops.len());
    for (idx, op) in ops.iter().enumerate() {
        let offset = u32::try_from(idx)
            .map_err(|_| GnomonError::Internal("too many lowered stratum functions".into()))?;
        let fid = base_func_id
            .checked_add(offset)
            .ok_or_else(|| GnomonError::Internal("FuncId overflow during stratum lowering".into()))?;
        stratum_to_func.insert(op.id, FuncId(fid));
    }

    let mut map_target = |target: CallTarget| -> Result<CallTarget, GnomonError> {
        match target {
            CallTarget::Stratum(sid) => {
                let fid = *stratum_to_func.get(&sid).ok_or_else(|| {
                    GnomonError::Registry(format!(
                        "stratum id {} missing from lowering map",
                        sid.0
                    ))
                })?;
                Ok(CallTarget::Func(fid))
            }
            other => Ok(other),
        }
    };

    for f in &mut out.funcs {
        f.body = rewrite_region_call_targets(&f.body, &mut map_target)?;
    }
    for hc in &mut out.host_contracts {
        hc.precondition = rewrite_region_call_targets(&hc.precondition, &mut map_target)?;
        hc.postcondition = rewrite_region_call_targets(&hc.postcondition, &mut map_target)?;
        if let Some(ref sim) = hc.sim_body {
            hc.sim_body = Some(rewrite_region_call_targets(sim, &mut map_target)?);
        }
    }

    // Ensure any MemId referenced by materialized stratum bodies is declared on the module.
    let mut max_mem: Option<u16> = None;
    for op in &ops {
        if let Some(mx) = max_mem_id_in_region(&op.body) {
            max_mem = Some(max_mem.map_or(mx, |cur| cur.max(mx)));
        }
    }
    if let Some(mx) = max_mem {
        for id in 0..=mx {
            if !out.memories.iter().any(|m| m.id == MemId(id)) {
                out.memories.push(MemoryDef {
                    id: MemId(id),
                    min_pages: 1,
                    max_pages: Some(1),
                    init_data: Vec::new(),
                });
            }
        }
    }

    // Append materialized internal FuncDefs (`export_name: None`).
    for op in ops {
        let fid = stratum_to_func[&op.id];
        let lowered_body = rewrite_region_call_targets(&op.body, &mut map_target)?;
        out.funcs.push(FuncDef {
            id: fid,
            name: format!("__stratum_{}_{}", op.id.0, op.name),
            export_name: None,
            params: op.params.clone(),
            results: op.results.clone(),
            body: lowered_body,
        });
    }

    Ok(out)
}

/// Sanitizes an arbitrary Stratum name into a valid, non-keyword Rust identifier.
pub fn sanitize_rust_ident(raw: &str) -> String {
    let mut ident = String::with_capacity(raw.len());
    for ch in raw.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            ident.push(ch);
        } else {
            ident.push('_');
        }
    }
    if ident.is_empty() || ident.as_bytes()[0].is_ascii_digit() || ident == "_" {
        ident.insert_str(0, "op_");
    }
    if is_rust_keyword(&ident) {
        ident.push_str("_op");
    }
    ident
}

fn is_rust_keyword(s: &str) -> bool {
    matches!(
        s,
        "as" | "async"
            | "await"
            | "break"
            | "const"
            | "continue"
            | "crate"
            | "dyn"
            | "else"
            | "enum"
            | "extern"
            | "false"
            | "fn"
            | "for"
            | "gen"
            | "if"
            | "impl"
            | "in"
            | "let"
            | "loop"
            | "match"
            | "mod"
            | "move"
            | "mut"
            | "pub"
            | "ref"
            | "return"
            | "self"
            | "Self"
            | "static"
            | "struct"
            | "super"
            | "trait"
            | "true"
            | "type"
            | "unsafe"
            | "use"
            | "where"
            | "while"
            | "abstract"
            | "become"
            | "box"
            | "do"
            | "final"
            | "macro"
            | "override"
            | "priv"
            | "try"
            | "typeof"
            | "unsized"
            | "virtual"
            | "yield"
    )
}

fn rust_val_type(ty: ValType) -> &'static str {
    match ty {
        ValType::I32 => "i32",
        ValType::I64 => "i64",
    }
}

/// Generates a clean, `#![no_std]`-compatible `strata.rs` module providing safe wrappers
/// for `gnomon_assume`, `gnomon_assert`, and every registered Stratum op.
pub fn generate_strata_rs(registry: &StratumRegistry, include_candidates: bool) -> String {
    struct Entry<'a> {
        op: &'a StratumOp,
        promoted: bool,
        law_names: Vec<&'a str>,
    }

    let mut entries: Vec<Entry<'_>> = Vec::new();
    let mut seen_ids: HashSet<StratumId> = HashSet::new();

    for st in registry.promoted() {
        seen_ids.insert(st.op.id);
        entries.push(Entry {
            op: &st.op,
            promoted: true,
            law_names: st.laws.iter().map(|l| l.name.as_str()).collect(),
        });
    }
    if include_candidates {
        for cand in registry.candidates() {
            if seen_ids.insert(cand.id) {
                entries.push(Entry {
                    op: cand,
                    promoted: false,
                    law_names: Vec::new(),
                });
            }
        }
    }
    entries.sort_by_key(|e| (e.op.layer, e.op.id.0));

    let mut out = String::new();
    out.push_str("#![allow(dead_code)]\n");
    out.push_str("//! Auto-generated Gnomon Strata bindings (`#![no_std]` compatible).\n\n");
    out.push_str("mod __gnomon_host {\n");
    out.push_str("    #[link(wasm_import_module = \"gnomon\")]\n");
    out.push_str("    unsafe extern \"C\" {\n");
    out.push_str("        pub(super) fn gnomon_assume(cond: i32);\n");
    out.push_str("        pub(super) fn gnomon_assert(cond: i32);\n");
    out.push_str("    }\n");
    out.push_str("}\n\n");
    out.push_str("/// Assume a path condition for symbolic verification.\n");
    out.push_str("#[inline(always)]\n");
    out.push_str("pub fn gnomon_assume(cond: bool) {\n");
    out.push_str("    unsafe {\n");
    out.push_str("        __gnomon_host::gnomon_assume(if cond { 1 } else { 0 });\n");
    out.push_str("    }\n");
    out.push_str("}\n\n");
    out.push_str("/// Assert a verification property on the current path.\n");
    out.push_str("#[inline(always)]\n");
    out.push_str("pub fn gnomon_assert(cond: bool) {\n");
    out.push_str("    unsafe {\n");
    out.push_str("        __gnomon_host::gnomon_assert(if cond { 1 } else { 0 });\n");
    out.push_str("    }\n");
    out.push_str("}\n");

    let mut used_idents: HashSet<String> = HashSet::from([
        "gnomon_assume".to_string(),
        "gnomon_assert".to_string(),
    ]);

    let mut ffi_decls = String::new();
    let mut wrappers = String::new();
    let mut skipped_notes = String::new();

    for entry in entries {
        let op = entry.op;
        if op.results.len() > 1 {
            let _ = writeln!(
                skipped_notes,
                "// Skipped Layer {} stratum '{}' (id={}): multi-value return ({} results) is not representable via extern \"C\".",
                op.layer,
                op.name,
                op.id.0,
                op.results.len()
            );
            continue;
        }

        let base_ident = sanitize_rust_ident(&op.name);
        let ident = if used_idents.insert(base_ident.clone()) {
            base_ident
        } else {
            let disambig = format!("{base_ident}_{}", op.id.0);
            used_idents.insert(disambig.clone());
            disambig
        };

        let mut param_sig = String::new();
        let mut arg_list = String::new();
        for (idx, &(_, ty)) in op.params.iter().enumerate() {
            if idx > 0 {
                param_sig.push_str(", ");
                arg_list.push_str(", ");
            }
            let _ = write!(param_sig, "arg{idx}: {}", rust_val_type(ty));
            let _ = write!(arg_list, "arg{idx}");
        }

        let ret_sig = match op.results.as_slice() {
            [] => String::new(),
            [ty] => format!(" -> {}", rust_val_type(*ty)),
            _ => unreachable!(),
        };

        if ident != op.name {
            let _ = writeln!(ffi_decls, "        #[link_name = {:?}]", op.name);
        }
        let _ = writeln!(ffi_decls, "        pub(super) fn {ident}({param_sig}){ret_sig};");

        let status = if entry.promoted { "promoted" } else { "candidate" };
        let _ = writeln!(
            wrappers,
            "\n/// Layer {} Stratum `{}` (id={}, {status})",
            op.layer, op.name, op.id.0
        );
        if !op.docstring.is_empty() {
            for line in op.docstring.lines() {
                let _ = writeln!(wrappers, "/// {line}");
            }
        }
        if !entry.law_names.is_empty() {
            let _ = writeln!(wrappers, "/// Proved laws: {}", entry.law_names.join(", "));
        }
        let _ = writeln!(wrappers, "#[inline(always)]");
        let _ = writeln!(wrappers, "pub fn {ident}({param_sig}){ret_sig} {{");
        let _ = writeln!(wrappers, "    unsafe {{ __gnomon_stratum::{ident}({arg_list}) }}");
        let _ = writeln!(wrappers, "}}");
    }

    if !ffi_decls.is_empty() {
        out.push_str("\nmod __gnomon_stratum {\n");
        out.push_str("    #[link(wasm_import_module = \"stratum\")]\n");
        out.push_str("    unsafe extern \"C\" {\n");
        out.push_str(&ffi_decls);
        out.push_str("    }\n");
        out.push_str("}\n");
        out.push_str(&wrappers);
    }
    if !skipped_notes.is_empty() {
        out.push('\n');
        out.push_str(&skipped_notes);
    }

    out
}

// ===========================================================================
// Exhaustive Region-SSA CallTarget Traversal & Rewriting
// ===========================================================================

fn visit_region_call_targets(region: &Region, visit: &mut impl FnMut(CallTarget)) {
    fn walk(r: RegionRef<'_>, visit: &mut impl FnMut(CallTarget)) {
        match r.node {
            RegionNode::Block(span) => {
                for i in 0..span.len {
                    if let Some(stmt) = r.region.try_stmt(span, i) {
                        match stmt {
                            Stmt::Call { target, .. } => visit(target),
                            Stmt::Region { region, .. } => {
                                if let Some(child) = r.child(region) {
                                    walk(child, visit);
                                }
                            }
                            Stmt::Let { .. }
                            | Stmt::Effect(_)
                            | Stmt::Yield(_)
                            | Stmt::Break { .. }
                            | Stmt::Continue { .. }
                            | Stmt::Return(_) => {}
                        }
                    }
                }
            }
            RegionNode::IfElse { then_region, else_region, .. } => {
                if let Some(t) = r.child(then_region) {
                    walk(t, visit);
                }
                if let Some(e) = r.child(else_region) {
                    walk(e, visit);
                }
            }
            RegionNode::BoundedLoop { body, .. } => {
                if let Some(b) = r.child(body) {
                    walk(b, visit);
                }
            }
            RegionNode::InvariantLoop { cond, invariant_pred, fuel_measure, body, .. } => {
                for id in [cond, invariant_pred, fuel_measure, body] {
                    if let Some(sub) = r.child(id) {
                        walk(sub, visit);
                    }
                }
            }
        }
    }
    walk(region.as_ref(), visit);
}

fn collect_stratum_ids_in_region(region: &Region, out: &mut BTreeSet<StratumId>) {
    visit_region_call_targets(region, &mut |t| {
        if let CallTarget::Stratum(sid) = t {
            out.insert(sid);
        }
    });
}

pub(crate) fn rewrite_region_call_targets(
    region: &Region,
    map_target: &mut impl FnMut(CallTarget) -> Result<CallTarget, GnomonError>,
) -> Result<Region, GnomonError> {
    fn walk(
        r: RegionRef<'_>,
        map_target: &mut impl FnMut(CallTarget) -> Result<CallTarget, GnomonError>,
    ) -> Result<Region, GnomonError> {
        match r.node {
            RegionNode::Block(span) => {
                let mut b = RegionBuilder::new();
                for i in 0..span.len {
                    let stmt = r.region.try_stmt(span, i).ok_or_else(|| {
                        GnomonError::Internal(format!("invalid stmt slot at block index {i}"))
                    })?;
                    match stmt {
                        Stmt::Let { dst, ty, op } => b.push_let(dst, ty, op),
                        Stmt::Effect(eff) => b.push_effect(eff),
                        Stmt::Region { results, region } => {
                            let res_vars = r.region.vars_vec(results);
                            let child = r.child(region).ok_or_else(|| {
                                GnomonError::Internal(format!("missing child region {region:?}"))
                            })?;
                            let rewritten = walk(child, map_target)?;
                            b.push_subregion(&res_vars, &rewritten);
                        }
                        Stmt::Call { results, target, args } => {
                            let res_vars = r.region.vars_vec(results);
                            let arg_vals = r.region.vals_vec(args);
                            let new_target = map_target(target)?;
                            b.push_call(&res_vars, new_target, &arg_vals);
                        }
                        Stmt::Yield(vals) => {
                            let vs = r.region.vals_vec(vals);
                            b.push_yield(&vs);
                        }
                        Stmt::Break { depth, cond, values } => {
                            let vs = r.region.vals_vec(values);
                            b.push_break(depth, cond, &vs);
                        }
                        Stmt::Continue { depth, cond, values } => {
                            let vs = r.region.vals_vec(values);
                            b.push_continue(depth, cond, &vs);
                        }
                        Stmt::Return(vals) => {
                            let vs = r.region.vals_vec(vals);
                            b.push_return(&vs);
                        }
                    }
                }
                Ok(b.finish())
            }
            RegionNode::IfElse { cond, then_region, else_region, results } => {
                let then_child = r.child(then_region).ok_or_else(|| {
                    GnomonError::Internal(format!("missing then region {then_region:?}"))
                })?;
                let else_child = r.child(else_region).ok_or_else(|| {
                    GnomonError::Internal(format!("missing else region {else_region:?}"))
                })?;
                let new_then = walk(then_child, map_target)?;
                let new_else = walk(else_child, map_target)?;
                let res_tys = r.region.tys_vec(results);
                Ok(Region::if_else(cond, &new_then, &new_else, &res_tys))
            }
            RegionNode::BoundedLoop { max_iters, init_vars, state_vars, body } => {
                let body_child = r.child(body).ok_or_else(|| {
                    GnomonError::Internal(format!("missing bounded_loop body {body:?}"))
                })?;
                let new_body = walk(body_child, map_target)?;
                let inits = r.region.vals_vec(init_vars);
                let states = r.region.vars_vec(state_vars);
                Ok(Region::bounded_loop(max_iters, &inits, &states, &new_body))
            }
            RegionNode::InvariantLoop {
                init_vars,
                state_vars,
                cond,
                invariant_pred,
                fuel_measure,
                body,
            } => {
                let cond_child = r.child(cond).ok_or_else(|| {
                    GnomonError::Internal(format!("missing invariant_loop cond {cond:?}"))
                })?;
                let inv_child = r.child(invariant_pred).ok_or_else(|| {
                    GnomonError::Internal(format!("missing invariant_loop inv {invariant_pred:?}"))
                })?;
                let fuel_child = r.child(fuel_measure).ok_or_else(|| {
                    GnomonError::Internal(format!("missing invariant_loop fuel {fuel_measure:?}"))
                })?;
                let body_child = r.child(body).ok_or_else(|| {
                    GnomonError::Internal(format!("missing invariant_loop body {body:?}"))
                })?;
                let new_cond = walk(cond_child, map_target)?;
                let new_inv = walk(inv_child, map_target)?;
                let new_fuel = walk(fuel_child, map_target)?;
                let new_body = walk(body_child, map_target)?;
                let inits = r.region.vals_vec(init_vars);
                let states = r.region.vars_vec(state_vars);
                Ok(Region::invariant_loop(
                    &inits, &states, &new_cond, &new_inv, &new_fuel, &new_body,
                ))
            }
        }
    }
    walk(region.as_ref(), map_target)
}

/// Rewrites nested `Stmt::Return(vals)` inside a `Block`-rooted Stratum body into
/// equivalent `Stmt::Break { depth, cond: None, values: vals }` targeting the root `Block`.
///
/// Why: `rustc`/`LLVM` frequently lowers early returns (`if c { return v; }`) inside a
/// `#![no_std]` Rust function into Wasm `(block (br_if 0 !c) (return v))`, which lifts as a
/// void `Stmt::Region { results: [], region: Block([..., Return(v)]) }`. Frozen
/// `gnomon-kernel::StratumRegistry` checks `Return` against its immediately enclosing block's
/// result types (rejecting `Return(v)` inside a void sub-block with `TypeMismatch`), while
/// `Break { depth >= 1 }` targeting the root `Block` has identical semantics across
/// `eval`, `smt_ir`, `emit_wasm`, and `lower_region_to_layer0`!
pub fn normalize_nested_returns_for_stratum(region: &Region) -> Result<Region, GnomonError> {
    if !matches!(region.root, RegionNode::Block(_)) || !has_nested_return(region) {
        return Ok(region.clone());
    }

    fn walk(
        r: RegionRef<'_>,
        break_depth: u32,
        is_root: bool,
        as_loop_body: bool,
    ) -> Result<Region, GnomonError> {
        match r.node {
            RegionNode::Block(span) => {
                let cur_depth = if is_root || as_loop_body {
                    break_depth
                } else {
                    break_depth + 1
                };
                let mut b = RegionBuilder::new();
                for i in 0..span.len {
                    let stmt = r.region.try_stmt(span, i).ok_or_else(|| {
                        GnomonError::Internal(format!("invalid stmt slot at block index {i}"))
                    })?;
                    match stmt {
                        Stmt::Let { dst, ty, op } => b.push_let(dst, ty, op),
                        Stmt::Effect(eff) => b.push_effect(eff),
                        Stmt::Region { results, region } => {
                            let res_vars = r.region.vars_vec(results);
                            let child = r.child(region).ok_or_else(|| {
                                GnomonError::Internal(format!("missing child region {region:?}"))
                            })?;
                            let rewritten = walk(child, cur_depth, false, false)?;
                            b.push_subregion(&res_vars, &rewritten);
                        }
                        Stmt::Call { results, target, args } => {
                            let res_vars = r.region.vars_vec(results);
                            let arg_vals = r.region.vals_vec(args);
                            b.push_call(&res_vars, target, &arg_vals);
                        }
                        Stmt::Yield(vals) => {
                            let vs = r.region.vals_vec(vals);
                            b.push_yield(&vs);
                        }
                        Stmt::Break { depth, cond, values } => {
                            let vs = r.region.vals_vec(values);
                            b.push_break(depth, cond, &vs);
                        }
                        Stmt::Continue { depth, cond, values } => {
                            let vs = r.region.vals_vec(values);
                            b.push_continue(depth, cond, &vs);
                        }
                        Stmt::Return(vals) => {
                            let vs = r.region.vals_vec(vals);
                            if cur_depth >= 1 {
                                b.push_break(cur_depth, None, &vs);
                            } else {
                                b.push_return(&vs);
                            }
                        }
                    }
                }
                Ok(b.finish())
            }
            RegionNode::IfElse { cond, then_region, else_region, results } => {
                let then_child = r.child(then_region).ok_or_else(|| {
                    GnomonError::Internal(format!("missing then region {then_region:?}"))
                })?;
                let else_child = r.child(else_region).ok_or_else(|| {
                    GnomonError::Internal(format!("missing else region {else_region:?}"))
                })?;
                let new_then = walk(then_child, break_depth, false, false)?;
                let new_else = walk(else_child, break_depth, false, false)?;
                let res_tys = r.region.tys_vec(results);
                Ok(Region::if_else(cond, &new_then, &new_else, &res_tys))
            }
            RegionNode::BoundedLoop { max_iters, init_vars, state_vars, body } => {
                let body_child = r.child(body).ok_or_else(|| {
                    GnomonError::Internal(format!("missing bounded_loop body {body:?}"))
                })?;
                let new_body = walk(body_child, break_depth + 1, false, true)?;
                let inits = r.region.vals_vec(init_vars);
                let states = r.region.vars_vec(state_vars);
                Ok(Region::bounded_loop(max_iters, &inits, &states, &new_body))
            }
            RegionNode::InvariantLoop { .. } => Ok(r.to_owned_region()),
        }
    }

    walk(region.as_ref(), 0, true, false)
}

fn has_nested_return(region: &Region) -> bool {
    fn walk(r: RegionRef<'_>, nested: bool) -> bool {
        match r.node {
            RegionNode::Block(span) => {
                for i in 0..span.len {
                    if let Some(stmt) = r.region.try_stmt(span, i) {
                        match stmt {
                            Stmt::Return(_) if nested => return true,
                            Stmt::Region { region, .. } => {
                                if let Some(child) = r.child(region)
                                    && walk(child, true)
                                {
                                    return true;
                                }
                            }
                            _ => {}
                        }
                    }
                }
                false
            }
            RegionNode::IfElse { then_region, else_region, .. } => {
                r.child(then_region).is_some_and(|c| walk(c, true))
                    || r.child(else_region).is_some_and(|c| walk(c, true))
            }
            RegionNode::BoundedLoop { body, .. } => r.child(body).is_some_and(|c| walk(c, true)),
            RegionNode::InvariantLoop { .. } => false,
        }
    }
    walk(region.as_ref(), false)
}

fn max_mem_id_in_region(region: &Region) -> Option<u16> {
    fn walk(r: RegionRef<'_>) -> Option<u16> {
        let mut mx: Option<u16> = None;
        let bump = |mx: &mut Option<u16>, id: u16| {
            *mx = Some(mx.map_or(id, |cur| cur.max(id)));
        };
        match r.node {
            RegionNode::Block(span) => {
                for i in 0..span.len {
                    if let Some(stmt) = r.region.try_stmt(span, i) {
                        match stmt {
                            Stmt::Let {
                                op:
                                    Op::Load { mem, .. }
                                    | Op::MemorySize(mem)
                                    | Op::MemoryGrow { mem, .. },
                                ..
                            } => bump(&mut mx, mem.0),
                            Stmt::Effect(
                                EffectOp::Store { mem, .. } | EffectOp::MemoryFill { mem, .. },
                            ) => bump(&mut mx, mem.0),
                            Stmt::Effect(EffectOp::MemoryCopy { dst_mem, src_mem, .. }) => {
                                bump(&mut mx, dst_mem.0);
                                bump(&mut mx, src_mem.0);
                            }
                            Stmt::Region { region, .. } => {
                                if let Some(sub) = r.child(region)
                                    && let Some(sub_mx) = walk(sub)
                                {
                                    bump(&mut mx, sub_mx);
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }
            RegionNode::IfElse { then_region, else_region, .. } => {
                for id in [then_region, else_region] {
                    if let Some(sub) = r.child(id)
                        && let Some(sub_mx) = walk(sub)
                    {
                        bump(&mut mx, sub_mx);
                    }
                }
            }
            RegionNode::BoundedLoop { body, .. } => {
                if let Some(sub) = r.child(body)
                    && let Some(sub_mx) = walk(sub)
                {
                    bump(&mut mx, sub_mx);
                }
            }
            RegionNode::InvariantLoop { cond, invariant_pred, fuel_measure, body, .. } => {
                for id in [cond, invariant_pred, fuel_measure, body] {
                    if let Some(sub) = r.child(id)
                        && let Some(sub_mx) = walk(sub)
                    {
                        bump(&mut mx, sub_mx);
                    }
                }
            }
        }
        mx
    }
    walk(region.as_ref())
}
