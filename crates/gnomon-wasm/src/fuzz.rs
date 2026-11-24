//! Microsecond Stage-1 `wasmtime` equivalence falsifier and differential runner.

use std::collections::{HashMap, HashSet};
use std::sync::OnceLock;
use std::time::Instant;

use gnomon_kernel::{
    FuncId, HeapState, StratumRegistry, TrapCode, Val, ValType, eval_func,
};
use wasm_encoder::{ExportKind, ExportSection, Module as WasmModule, RawSection};
use wasmparser::{
    CompositeInnerType, DataKind, ExternalKind, Operator, Parser, Payload, TypeRef,
    ValType as WValType, Validator, WasmFeatures,
};
use wasmtime::{
    Config, Engine, Func, Global, Linker, Memory, Module as WtModule, OptLevel, Store, Trap,
    TypedFunc, V128 as WtV128, Val as WtVal,
};

use crate::{Counterexample, ExecOutcome, FuzzConfig, FuzzOutcome, WasmError, emit_wasm, lift_wasm};

const INTERNAL_ENTRY_EXPORT: &str = "__gnomon_fuzz_entry";

fn shared_engine() -> Result<&'static Engine, WasmError> {
    static ENGINE: OnceLock<Result<Engine, String>> = OnceLock::new();
    let res = ENGINE.get_or_init(|| {
        let mut cfg = Config::new();
        cfg.consume_fuel(true)
            .wasm_multi_memory(true)
            .wasm_bulk_memory(true)
            .wasm_multi_value(true)
            .wasm_simd(true)
            .cranelift_nan_canonicalization(true)
            .wasm_backtrace_max_frames(None)
            .generate_address_map(false)
            .parallel_compilation(false)
            .cranelift_opt_level(OptLevel::None);
        Engine::new(&cfg).map_err(|e| e.to_string())
    });
    match res {
        Ok(e) => Ok(e),
        Err(msg) => Err(WasmError::ValidationError(msg.clone())),
    }
}

#[derive(Clone)]
struct FuncSig {
    params: Vec<ValType>,
    results: Vec<ValType>,
}

struct MemInitInfo {
    fuzz_export_name: String,
    init_image: Vec<u8>,
}

struct GlobalInitInfo {
    mutable: bool,
    init: Val,
    fuzz_export_name: Option<String>,
}

struct HostImportInfo {
    module: String,
    field: String,
    sig: FuncSig,
}

struct PreparedModule {
    wasm_bytes: Vec<u8>,
    entry_export: String,
    sig: FuncSig,
    host_imports: Vec<HostImportInfo>,
    memories: Vec<MemInitInfo>,
    exported_mem_names: Vec<String>,
    exported_global_names: Vec<String>,
    globals: Vec<GlobalInitInfo>,
    has_mem_writes: bool,
    has_global_sets: bool,
}

enum EntryTarget<'a> {
    FuncId(FuncId),
    ExportName(&'a str),
}

fn convert_wval_type(ty: WValType) -> Result<ValType, WasmError> {
    match ty {
        WValType::I32 => Ok(ValType::I32),
        WValType::I64 => Ok(ValType::I64),
        WValType::F32 => Ok(ValType::F32),
        WValType::F64 => Ok(ValType::F64),
        WValType::V128 => Ok(ValType::V128),
        other => Err(WasmError::UnsupportedFeature(format!(
            "unsupported wasm value type: {other:?}"
        ))),
    }
}

fn eval_simple_const_expr(
    expr: &wasmparser::ConstExpr<'_>,
    globals: &[GlobalInitInfo],
) -> Result<Val, WasmError> {
    let mut stack = Vec::new();
    let mut ops = expr.get_operators_reader();
    while !ops.eof() {
        match ops.read().map_err(|e| WasmError::ParseError(e.to_string()))? {
            Operator::I32Const { value } => stack.push(Val::I32(value)),
            Operator::I64Const { value } => stack.push(Val::I64(value)),
            Operator::F32Const { value } => stack.push(Val::F32(value.bits())),
            Operator::F64Const { value } => stack.push(Val::F64(value.bits())),
            Operator::V128Const { value } => stack.push(Val::V128(value.i128() as u128)),
            Operator::GlobalGet { global_index } => {
                let g = globals.get(global_index as usize).ok_or_else(|| {
                    WasmError::ValidationError("const expr unknown global".into())
                })?;
                stack.push(g.init);
            }
            Operator::I32Add => match (stack.pop(), stack.pop()) {
                (Some(Val::I32(b)), Some(Val::I32(a))) => stack.push(Val::I32(a.wrapping_add(b))),
                _ => return Err(WasmError::ValidationError("invalid const i32.add".into())),
            },
            Operator::I32Sub => match (stack.pop(), stack.pop()) {
                (Some(Val::I32(b)), Some(Val::I32(a))) => stack.push(Val::I32(a.wrapping_sub(b))),
                _ => return Err(WasmError::ValidationError("invalid const i32.sub".into())),
            },
            Operator::I32Mul => match (stack.pop(), stack.pop()) {
                (Some(Val::I32(b)), Some(Val::I32(a))) => stack.push(Val::I32(a.wrapping_mul(b))),
                _ => return Err(WasmError::ValidationError("invalid const i32.mul".into())),
            },
            Operator::I64Add => match (stack.pop(), stack.pop()) {
                (Some(Val::I64(b)), Some(Val::I64(a))) => stack.push(Val::I64(a.wrapping_add(b))),
                _ => return Err(WasmError::ValidationError("invalid const i64.add".into())),
            },
            Operator::I64Sub => match (stack.pop(), stack.pop()) {
                (Some(Val::I64(b)), Some(Val::I64(a))) => stack.push(Val::I64(a.wrapping_sub(b))),
                _ => return Err(WasmError::ValidationError("invalid const i64.sub".into())),
            },
            Operator::I64Mul => match (stack.pop(), stack.pop()) {
                (Some(Val::I64(b)), Some(Val::I64(a))) => stack.push(Val::I64(a.wrapping_mul(b))),
                _ => return Err(WasmError::ValidationError("invalid const i64.mul".into())),
            },
            Operator::End => break,
            other => {
                return Err(WasmError::UnsupportedFeature(format!(
                    "unsupported const expr op: {other:?}"
                )));
            }
        }
    }
    stack
        .pop()
        .filter(|_| stack.is_empty())
        .ok_or_else(|| WasmError::ValidationError("invalid const expr".into()))
}

fn prepare_module(bytes: &[u8], target: EntryTarget<'_>) -> Result<PreparedModule, WasmError> {
    let mut validator = Validator::new_with_features(WasmFeatures::default());
    validator
        .validate_all(bytes)
        .map_err(|e| WasmError::ValidationError(e.to_string()))?;

    let mut types: Vec<Option<FuncSig>> = Vec::new();
    let mut host_imports: Vec<HostImportInfo> = Vec::new();
    let mut defined_type_idxs: Vec<u32> = Vec::new();
    let mut mem_sizes: Vec<u32> = Vec::new();
    let mut data_segments: Vec<(usize, u32, Vec<u8>)> = Vec::new();
    let mut globals: Vec<GlobalInitInfo> = Vec::new();

    let mut existing_exports: Vec<(String, ExternalKind, u32)> = Vec::new();
    let mut func_export_map: HashMap<u32, String> = HashMap::new();
    let mut name_to_func_idx: HashMap<String, u32> = HashMap::new();
    let mut mem_export_map: HashMap<u32, String> = HashMap::new();
    let mut global_export_map: HashMap<u32, String> = HashMap::new();
    let mut has_mem_writes = false;
    let mut has_global_sets = false;

    for payload in Parser::new(0).parse_all(bytes) {
        let payload = payload.map_err(|e| WasmError::ParseError(e.to_string()))?;
        match payload {
            Payload::TypeSection(reader) => {
                for rec in reader {
                    let rec = rec.map_err(|e| WasmError::ParseError(e.to_string()))?;
                    for sub in rec.into_types() {
                        match sub.composite_type.inner {
                            CompositeInnerType::Func(ft) => {
                                let p = ft
                                    .params()
                                    .iter()
                                    .copied()
                                    .map(convert_wval_type)
                                    .collect::<Result<Vec<_>, _>>();
                                let r = ft
                                    .results()
                                    .iter()
                                    .copied()
                                    .map(convert_wval_type)
                                    .collect::<Result<Vec<_>, _>>();
                                types.push(match (p, r) {
                                    (Ok(params), Ok(results)) => Some(FuncSig { params, results }),
                                    _ => None,
                                });
                            }
                            _ => types.push(None),
                        }
                    }
                }
            }
            Payload::ImportSection(reader) => {
                for imp in reader.into_imports() {
                    let imp = imp.map_err(|e| WasmError::ParseError(e.to_string()))?;
                    match imp.ty {
                        TypeRef::Func(type_idx) => {
                            let sig = types
                                .get(type_idx as usize)
                                .and_then(|o| o.as_ref())
                                .cloned()
                                .ok_or_else(|| {
                                    WasmError::UnsupportedFeature(
                                        "host import uses unsupported value type signature".into(),
                                    )
                                })?;
                            host_imports.push(HostImportInfo {
                                module: imp.module.to_owned(),
                                field: imp.name.to_owned(),
                                sig,
                            });
                        }
                        other => {
                            return Err(WasmError::UnsupportedFeature(format!(
                                "unsupported import type: {other:?}"
                            )));
                        }
                    }
                }
            }
            Payload::FunctionSection(reader) => {
                for type_idx in reader {
                    defined_type_idxs
                        .push(type_idx.map_err(|e| WasmError::ParseError(e.to_string()))?);
                }
            }
            Payload::MemorySection(reader) => {
                for m in reader {
                    let m = m.map_err(|e| WasmError::ParseError(e.to_string()))?;
                    if m.memory64 || m.shared {
                        return Err(WasmError::UnsupportedFeature(
                            "memory64 and shared memories are not supported".into(),
                        ));
                    }
                    mem_sizes.push(u32::try_from(m.initial).map_err(|_| {
                        WasmError::UnsupportedFeature("memory pages exceed u32".into())
                    })?);
                }
            }
            Payload::GlobalSection(reader) => {
                for g in reader {
                    let g = g.map_err(|e| WasmError::ParseError(e.to_string()))?;
                    let init = eval_simple_const_expr(&g.init_expr, &globals)?;
                    globals.push(GlobalInitInfo {
                        mutable: g.ty.mutable,
                        init,
                        fuzz_export_name: None,
                    });
                }
            }
            Payload::ExportSection(reader) => {
                for e in reader {
                    let e = e.map_err(|e| WasmError::ParseError(e.to_string()))?;
                    existing_exports.push((e.name.to_owned(), e.kind, e.index));
                    match e.kind {
                        ExternalKind::Func => {
                            func_export_map
                                .entry(e.index)
                                .or_insert_with(|| e.name.to_owned());
                            name_to_func_idx.insert(e.name.to_owned(), e.index);
                        }
                        ExternalKind::Memory => {
                            mem_export_map
                                .entry(e.index)
                                .or_insert_with(|| e.name.to_owned());
                        }
                        ExternalKind::Global => {
                            global_export_map
                                .entry(e.index)
                                .or_insert_with(|| e.name.to_owned());
                        }
                        _ => {}
                    }
                }
            }
            Payload::CodeSectionEntry(body) => {
                let mut ops = body
                    .get_operators_reader()
                    .map_err(|e| WasmError::ParseError(e.to_string()))?;
                while !ops.eof() {
                    match ops.read().map_err(|e| WasmError::ParseError(e.to_string()))? {
                        Operator::I32Store { .. }
                        | Operator::I64Store { .. }
                        | Operator::F32Store { .. }
                        | Operator::F64Store { .. }
                        | Operator::V128Store { .. }
                        | Operator::V128Store8Lane { .. }
                        | Operator::V128Store16Lane { .. }
                        | Operator::V128Store32Lane { .. }
                        | Operator::V128Store64Lane { .. }
                        | Operator::I32Store8 { .. }
                        | Operator::I32Store16 { .. }
                        | Operator::I64Store8 { .. }
                        | Operator::I64Store16 { .. }
                        | Operator::I64Store32 { .. }
                        | Operator::MemoryCopy { .. }
                        | Operator::MemoryFill { .. }
                        | Operator::MemoryInit { .. }
                        | Operator::MemoryGrow { .. } => {
                            has_mem_writes = true;
                        }
                        Operator::GlobalSet { .. } => {
                            has_global_sets = true;
                        }
                        _ => {}
                    }
                }
            }
            Payload::DataSection(reader) => {
                for seg in reader {
                    let seg = seg.map_err(|e| WasmError::ParseError(e.to_string()))?;
                    if let DataKind::Active {
                        memory_index,
                        offset_expr,
                    } = seg.kind
                    {
                        let off = match eval_simple_const_expr(&offset_expr, &globals)? {
                            Val::I32(v) => v as u32,
                            _ => {
                                return Err(WasmError::UnsupportedFeature(
                                    "non-i32 data offset not supported".into(),
                                ));
                            }
                        };
                        data_segments.push((memory_index as usize, off, seg.data.to_vec()));
                    }
                }
            }
            _ => {}
        }
    }

    let num_imported = host_imports.len();
    let wasm_func_idx = match target {
        EntryTarget::FuncId(fid) => {
            if (fid.0 as usize) >= defined_type_idxs.len() {
                return Err(WasmError::ValidationError(format!(
                    "entry {:?} out of range (defined funcs: {})",
                    fid,
                    defined_type_idxs.len()
                )));
            }
            (num_imported + fid.0 as usize) as u32
        }
        EntryTarget::ExportName(name) => *name_to_func_idx.get(name).ok_or_else(|| {
            WasmError::ValidationError(format!("exported function '{name}' not found"))
        })?,
    };

    let def_idx = (wasm_func_idx as usize)
        .checked_sub(num_imported)
        .ok_or_else(|| {
            WasmError::UnsupportedFeature("cannot use imported host function as entry".into())
        })?;
    let type_idx = defined_type_idxs[def_idx];
    let sig = types
        .get(type_idx as usize)
        .and_then(|o| o.as_ref())
        .cloned()
        .ok_or_else(|| {
            WasmError::UnsupportedFeature("entry function uses unsupported value types".into())
        })?;

    let mut used_names: HashSet<String> =
        existing_exports.iter().map(|(n, _, _)| n.clone()).collect();
    let alloc_export_name =
        |used: &mut HashSet<String>, prefix: &str, idx: usize| -> String {
            let mut candidate = format!("{prefix}_{idx}");
            let mut bump = 0usize;
            while !used.insert(candidate.clone()) {
                bump += 1;
                candidate = format!("{prefix}_{idx}_{bump}");
            }
            candidate
        };

    let mut extra_exports: Vec<(String, ExportKind, u32)> = Vec::new();
    let entry_export = match target {
        EntryTarget::ExportName(name) => name.to_owned(),
        EntryTarget::FuncId(_) => {
            if let Some(name) = func_export_map.get(&wasm_func_idx) {
                name.clone()
            } else {
                let name = if used_names.insert(INTERNAL_ENTRY_EXPORT.to_owned()) {
                    INTERNAL_ENTRY_EXPORT.to_owned()
                } else {
                    alloc_export_name(&mut used_names, INTERNAL_ENTRY_EXPORT, wasm_func_idx as usize)
                };
                extra_exports.push((name.clone(), ExportKind::Func, wasm_func_idx));
                name
            }
        }
    };

    // Build initial memory byte images and ensure writable memories are exported for fast reset.
    let mut mem_images: Vec<Vec<u8>> = mem_sizes
        .iter()
        .map(|&pages| vec![0u8; (pages as usize) * 65_536])
        .collect();
    for (midx, off, data) in data_segments {
        let img = mem_images.get_mut(midx).ok_or_else(|| {
            WasmError::ValidationError("data segment memory index out of range".into())
        })?;
        let start = off as usize;
        let end = start
            .checked_add(data.len())
            .ok_or_else(|| WasmError::ValidationError("data segment offset overflow".into()))?;
        if end > img.len() {
            return Err(WasmError::ValidationError(
                "data segment exceeds initial memory size".into(),
            ));
        }
        img[start..end].copy_from_slice(&data);
    }

    let mut memories = Vec::with_capacity(mem_images.len());
    for (idx, init_image) in mem_images.into_iter().enumerate() {
        let orig_export_name = mem_export_map.get(&(idx as u32)).cloned();
        let fuzz_export_name = if let Some(ref orig) = orig_export_name {
            orig.clone()
        } else if has_mem_writes {
            let name = alloc_export_name(&mut used_names, "__gnomon_fuzz_m", idx);
            extra_exports.push((name.clone(), ExportKind::Memory, idx as u32));
            name
        } else {
            String::new()
        };
        memories.push(MemInitInfo {
            fuzz_export_name,
            init_image,
        });
    }
    let exported_mem_names: Vec<String> = existing_exports
        .iter()
        .filter(|(_, k, _)| *k == ExternalKind::Memory)
        .map(|(n, _, _)| n.clone())
        .collect();
    let exported_global_names: Vec<String> = existing_exports
        .iter()
        .filter(|(_, k, _)| *k == ExternalKind::Global)
        .map(|(n, _, _)| n.clone())
        .collect();

    // Ensure mutable globals are exported when global.set exists so we can reset in nanoseconds.
    if has_global_sets {
        for (idx, g) in globals.iter_mut().enumerate() {
            if g.mutable {
                if let Some(orig) = global_export_map.get(&(idx as u32)) {
                    g.fuzz_export_name = Some(orig.clone());
                } else {
                    let name = alloc_export_name(&mut used_names, "__gnomon_fuzz_g", idx);
                    extra_exports.push((name.clone(), ExportKind::Global, idx as u32));
                    g.fuzz_export_name = Some(name);
                }
            }
        }
    }

    let wasm_bytes = if extra_exports.is_empty() {
        bytes.to_vec()
    } else {
        inject_extra_exports(bytes, &existing_exports, &extra_exports)?
    };

    Ok(PreparedModule {
        wasm_bytes,
        entry_export,
        sig,
        host_imports,
        memories,
        exported_mem_names,
        exported_global_names,
        globals,
        has_mem_writes,
        has_global_sets,
    })
}

fn to_enc_export_kind(k: ExternalKind) -> Result<ExportKind, WasmError> {
    match k {
        ExternalKind::Func => Ok(ExportKind::Func),
        ExternalKind::Table => Ok(ExportKind::Table),
        ExternalKind::Memory => Ok(ExportKind::Memory),
        ExternalKind::Global => Ok(ExportKind::Global),
        ExternalKind::Tag => Ok(ExportKind::Tag),
        ExternalKind::FuncExact => Err(WasmError::UnsupportedFeature(
            "FuncExact export not supported".into(),
        )),
    }
}

fn inject_extra_exports(
    bytes: &[u8],
    existing_exports: &[(String, ExternalKind, u32)],
    extra_exports: &[(String, ExportKind, u32)],
) -> Result<Vec<u8>, WasmError> {
    let mut new_exports = ExportSection::new();
    for (name, kind, idx) in existing_exports {
        new_exports.export(name, to_enc_export_kind(*kind)?, *idx);
    }
    for (name, kind, idx) in extra_exports {
        new_exports.export(name, *kind, *idx);
    }

    let mut out = WasmModule::new();
    let mut wrote_exports = false;
    for payload in Parser::new(0).parse_all(bytes) {
        let payload = payload.map_err(|e| WasmError::ParseError(e.to_string()))?;
        if let Some((id, range)) = payload.as_section() {
            if id == 7 {
                out.section(&new_exports);
                wrote_exports = true;
            } else {
                // Export section (id 7) must precede Start(8), Elem(9), Code(10), Data(11), DataCount(12).
                if !wrote_exports && matches!(id, 8..=12) {
                    out.section(&new_exports);
                    wrote_exports = true;
                }
                out.section(&RawSection {
                    id,
                    data: &bytes[range.start as usize..range.end as usize],
                });
            }
        }
    }
    if !wrote_exports {
        out.section(&new_exports);
    }
    Ok(out.finish())
}

enum FastRunner {
    UnitToUnit(TypedFunc<(), ()>),
    UnitToI32(TypedFunc<(), i32>),
    UnitToI64(TypedFunc<(), i64>),
    I32ToUnit(TypedFunc<i32, ()>),
    I32ToI32(TypedFunc<i32, i32>),
    I32x2ToUnit(TypedFunc<(i32, i32), ()>),
    I32x2ToI32(TypedFunc<(i32, i32), i32>),
    I32x3ToI32(TypedFunc<(i32, i32, i32), i32>),
    I32x4ToI32(TypedFunc<(i32, i32, i32, i32), i32>),
    I64ToI64(TypedFunc<i64, i64>),
    I64x2ToI64(TypedFunc<(i64, i64), i64>),
    I64x3ToI64(TypedFunc<(i64, i64, i64), i64>),
    I32ToI64(TypedFunc<i32, i64>),
    I32x2ToI64(TypedFunc<(i32, i32), i64>),
    I32x3ToI64(TypedFunc<(i32, i32, i32), i64>),
    I64ToI32(TypedFunc<i64, i32>),
    I32I64ToI32(TypedFunc<(i32, i64), i32>),
    I64I32ToI32(TypedFunc<(i64, i32), i32>),
    Generic(Func),
}

struct CompiledInstance {
    module: WtModule,
    store: Store<()>,
    runner: FastRunner,
    reset_memories: Vec<(usize, Memory)>,
    exported_memories: Vec<Memory>,
    exported_globals: Vec<Global>,
    reset_globals: Vec<(Global, WtVal)>,
    params_buf: Vec<WtVal>,
    results_buf: Vec<WtVal>,
    out_vals_buf: Vec<Val>,
}

fn to_wt_val(v: Val) -> WtVal {
    match v {
        Val::I32(x) => WtVal::I32(x),
        Val::I64(x) => WtVal::I64(x),
        Val::F32(b) => WtVal::F32(b),
        Val::F64(b) => WtVal::F64(b),
        Val::V128(b) => WtVal::V128(WtV128::from(b)),
    }
}

fn from_wt_val(v: &WtVal) -> Result<Val, WasmError> {
    match v {
        WtVal::I32(x) => Ok(Val::I32(*x)),
        WtVal::I64(x) => Ok(Val::I64(*x)),
        WtVal::F32(b) => Ok(Val::F32(*b)),
        WtVal::F64(b) => Ok(Val::F64(*b)),
        WtVal::V128(b) => Ok(Val::V128(b.as_u128())),
        other => Err(WasmError::UnsupportedFeature(format!(
            "unsupported wasmtime result value: {other:?}"
        ))),
    }
}

fn to_wt_val_type(t: ValType) -> wasmtime::ValType {
    match t {
        ValType::I32 => wasmtime::ValType::I32,
        ValType::I64 => wasmtime::ValType::I64,
        ValType::F32 => wasmtime::ValType::F32,
        ValType::F64 => wasmtime::ValType::F64,
        ValType::V128 => wasmtime::ValType::V128,
    }
}

fn map_wasmtime_trap(err: &wasmtime::Error) -> TrapCode {
    if let Some(trap) = err.downcast_ref::<Trap>() {
        match trap {
            Trap::IntegerDivisionByZero => TrapCode::DivByZero,
            Trap::IntegerOverflow | Trap::BadConversionToInteger => TrapCode::IntOverflow,
            Trap::MemoryOutOfBounds => TrapCode::OutOfBoundsMem,
            Trap::OutOfFuel | Trap::StackOverflow => TrapCode::OutOfFuel,
            Trap::UnreachableCodeReached => TrapCode::Unreachable,
            _ => TrapCode::Unreachable,
        }
    } else {
        TrapCode::HostContractViolation
    }
}

fn make_runner(store: &mut Store<()>, func: Func, sig: &FuncSig) -> FastRunner {
    use ValType::{I32, I64};
    match (sig.params.as_slice(), sig.results.as_slice()) {
        ([], []) => func.typed::<(), ()>(&mut *store).map(FastRunner::UnitToUnit).unwrap_or(FastRunner::Generic(func)),
        ([], [I32]) => func.typed::<(), i32>(&mut *store).map(FastRunner::UnitToI32).unwrap_or(FastRunner::Generic(func)),
        ([], [I64]) => func.typed::<(), i64>(&mut *store).map(FastRunner::UnitToI64).unwrap_or(FastRunner::Generic(func)),
        ([I32], []) => func.typed::<i32, ()>(&mut *store).map(FastRunner::I32ToUnit).unwrap_or(FastRunner::Generic(func)),
        ([I32], [I32]) => func.typed::<i32, i32>(&mut *store).map(FastRunner::I32ToI32).unwrap_or(FastRunner::Generic(func)),
        ([I32, I32], []) => func.typed::<(i32, i32), ()>(&mut *store).map(FastRunner::I32x2ToUnit).unwrap_or(FastRunner::Generic(func)),
        ([I32, I32], [I32]) => func.typed::<(i32, i32), i32>(&mut *store).map(FastRunner::I32x2ToI32).unwrap_or(FastRunner::Generic(func)),
        ([I32, I32, I32], [I32]) => func.typed::<(i32, i32, i32), i32>(&mut *store).map(FastRunner::I32x3ToI32).unwrap_or(FastRunner::Generic(func)),
        ([I32, I32, I32, I32], [I32]) => func.typed::<(i32, i32, i32, i32), i32>(&mut *store).map(FastRunner::I32x4ToI32).unwrap_or(FastRunner::Generic(func)),
        ([I64], [I64]) => func.typed::<i64, i64>(&mut *store).map(FastRunner::I64ToI64).unwrap_or(FastRunner::Generic(func)),
        ([I64, I64], [I64]) => func.typed::<(i64, i64), i64>(&mut *store).map(FastRunner::I64x2ToI64).unwrap_or(FastRunner::Generic(func)),
        ([I64, I64, I64], [I64]) => func.typed::<(i64, i64, i64), i64>(&mut *store).map(FastRunner::I64x3ToI64).unwrap_or(FastRunner::Generic(func)),
        ([I32], [I64]) => func.typed::<i32, i64>(&mut *store).map(FastRunner::I32ToI64).unwrap_or(FastRunner::Generic(func)),
        ([I32, I32], [I64]) => func.typed::<(i32, i32), i64>(&mut *store).map(FastRunner::I32x2ToI64).unwrap_or(FastRunner::Generic(func)),
        ([I32, I32, I32], [I64]) => func.typed::<(i32, i32, i32), i64>(&mut *store).map(FastRunner::I32x3ToI64).unwrap_or(FastRunner::Generic(func)),
        ([I64], [I32]) => func.typed::<i64, i32>(&mut *store).map(FastRunner::I64ToI32).unwrap_or(FastRunner::Generic(func)),
        ([I32, I64], [I32]) => func.typed::<(i32, i64), i32>(&mut *store).map(FastRunner::I32I64ToI32).unwrap_or(FastRunner::Generic(func)),
        ([I64, I32], [I32]) => func.typed::<(i64, i32), i32>(&mut *store).map(FastRunner::I64I32ToI32).unwrap_or(FastRunner::Generic(func)),
        _ => FastRunner::Generic(func),
    }
}

fn instantiate_compiled(engine: &Engine, prep: &PreparedModule, wt_mod: WtModule) -> Result<CompiledInstance, WasmError> {
    let mut store = Store::new(engine, ());
    let mut linker: Linker<()> = Linker::new(engine);
    let mut seen_imports = HashSet::new();
    for hi in &prep.host_imports {
        if !seen_imports.insert((hi.module.as_str(), hi.field.as_str())) {
            continue;
        }
        let wt_params: Vec<wasmtime::ValType> =
            hi.sig.params.iter().copied().map(to_wt_val_type).collect();
        let wt_results: Vec<wasmtime::ValType> =
            hi.sig.results.iter().copied().map(to_wt_val_type).collect();
        let func_ty = wasmtime::FuncType::new(engine, wt_params, wt_results.clone());
        linker
            .func_new(&hi.module, &hi.field, func_ty, move |_caller, _args, results| {
                for (slot, ty) in results.iter_mut().zip(&wt_results) {
                    *slot = match ty {
                        wasmtime::ValType::I32 => WtVal::I32(0),
                        wasmtime::ValType::I64 => WtVal::I64(0),
                        wasmtime::ValType::F32 => WtVal::F32(0),
                        wasmtime::ValType::F64 => WtVal::F64(0),
                        wasmtime::ValType::V128 => WtVal::V128(WtV128::from(0)),
                        _ => WtVal::I32(0),
                    };
                }
                Ok(())
            })
            .map_err(|e| WasmError::ValidationError(e.to_string()))?;
    }

    let instance = linker
        .instantiate(&mut store, &wt_mod)
        .map_err(|e| WasmError::ValidationError(e.to_string()))?;

    let func = instance
        .get_func(&mut store, &prep.entry_export)
        .ok_or_else(|| {
            WasmError::ValidationError(format!(
                "missing entry function '{}'",
                prep.entry_export
            ))
        })?;
    let runner = make_runner(&mut store, func, &prep.sig);

    let mut reset_memories = Vec::new();
    if prep.has_mem_writes {
        for (idx, m) in prep.memories.iter().enumerate() {
            if !m.fuzz_export_name.is_empty() {
                let mem = instance
                    .get_memory(&mut store, &m.fuzz_export_name)
                    .ok_or_else(|| WasmError::ValidationError("missing fuzz memory export".into()))?;
                reset_memories.push((idx, mem));
            }
        }
    }
    let mut exported_memories = Vec::with_capacity(prep.exported_mem_names.len());
    for name in &prep.exported_mem_names {
        let mem = instance
            .get_memory(&mut store, name)
            .ok_or_else(|| WasmError::ValidationError(format!("missing exported memory '{name}'")))?;
        exported_memories.push(mem);
    }
    let mut exported_globals = Vec::with_capacity(prep.exported_global_names.len());
    for name in &prep.exported_global_names {
        let glob = instance
            .get_global(&mut store, name)
            .ok_or_else(|| WasmError::ValidationError(format!("missing exported global '{name}'")))?;
        exported_globals.push(glob);
    }

    let mut reset_globals = Vec::new();
    if prep.has_global_sets {
        for g in &prep.globals {
            if let Some(ref gname) = g.fuzz_export_name {
                let glob = instance
                    .get_global(&mut store, gname)
                    .ok_or_else(|| WasmError::ValidationError("missing fuzz global export".into()))?;
                reset_globals.push((glob, to_wt_val(g.init)));
            }
        }
    }

    let params_buf: Vec<WtVal> = prep
        .sig
        .params
        .iter()
        .copied()
        .map(|t| to_wt_val(Val::default_for(t)))
        .collect();
    let results_buf: Vec<WtVal> = prep
        .sig
        .results
        .iter()
        .copied()
        .map(|t| to_wt_val(Val::default_for(t)))
        .collect();
    let out_vals_buf: Vec<Val> = prep
        .sig
        .results
        .iter()
        .copied()
        .map(Val::default_for)
        .collect();

    Ok(CompiledInstance {
        module: wt_mod,
        store,
        runner,
        reset_memories,
        exported_memories,
        exported_globals,
        reset_globals,
        params_buf,
        results_buf,
        out_vals_buf,
    })
}

impl CompiledInstance {
    fn compile(prep: &PreparedModule) -> Result<Self, WasmError> {
        let engine = shared_engine()?;
        let wt_mod = WtModule::new(engine, &prep.wasm_bytes)
            .map_err(|e| WasmError::ValidationError(e.to_string()))?;
        instantiate_compiled(engine, prep, wt_mod)
    }

    fn reset_state(&mut self, prep: &PreparedModule, fuel: u64) -> Result<(), WasmError> {
        // Check if any writable memory grew beyond initial page size; if so, re-instantiate.
        if prep.has_mem_writes {
            let mut grew = false;
            for &(idx, mem) in &self.reset_memories {
                if mem.data(&self.store).len() != prep.memories[idx].init_image.len() {
                    grew = true;
                    break;
                }
            }
            if grew {
                let engine = shared_engine()?;
                let fresh = instantiate_compiled(engine, prep, self.module.clone())?;
                *self = fresh;
                self.store
                    .set_fuel(fuel)
                    .map_err(|e| WasmError::ValidationError(e.to_string()))?;
                return Ok(());
            }
            for &(idx, mem) in &self.reset_memories {
                let data = mem.data_mut(&mut self.store);
                let init = &prep.memories[idx].init_image;
                for (dst_chunk, src_chunk) in data.chunks_mut(4096).zip(init.chunks(4096)) {
                    if dst_chunk != src_chunk {
                        dst_chunk.copy_from_slice(src_chunk);
                    }
                }
            }
        }
        for &(glob, val) in &self.reset_globals {
            glob.set(&mut self.store, val)
                .map_err(|e| WasmError::ValidationError(e.to_string()))?;
        }
        self.store
            .set_fuel(fuel)
            .map_err(|e| WasmError::ValidationError(e.to_string()))?;
        Ok(())
    }

    /// Executes `args` without heap allocation on fast paths.
    /// Returns `Ok(())` on success (results stored in `self.out_vals_buf`),
    /// or `Err(TrapCode)` on trap.
    fn call_fast(&mut self, args: &[Val]) -> Result<(), TrapCode> {
        let out = &mut self.out_vals_buf;
        let res = match &self.runner {
            FastRunner::UnitToUnit(f) => f.call(&mut self.store, ()),
            FastRunner::UnitToI32(f) => f.call(&mut self.store, ()).map(|r| out[0] = Val::I32(r)),
            FastRunner::UnitToI64(f) => f.call(&mut self.store, ()).map(|r| out[0] = Val::I64(r)),
            FastRunner::I32ToUnit(f) => {
                f.call(&mut self.store, args[0].as_i32().unwrap())
            }
            FastRunner::I32ToI32(f) => f
                .call(&mut self.store, args[0].as_i32().unwrap())
                .map(|r| out[0] = Val::I32(r)),
            FastRunner::I32x2ToUnit(f) => f.call(
                &mut self.store,
                (args[0].as_i32().unwrap(), args[1].as_i32().unwrap()),
            ),
            FastRunner::I32x2ToI32(f) => f
                .call(
                    &mut self.store,
                    (args[0].as_i32().unwrap(), args[1].as_i32().unwrap()),
                )
                .map(|r| out[0] = Val::I32(r)),
            FastRunner::I32x3ToI32(f) => f
                .call(
                    &mut self.store,
                    (
                        args[0].as_i32().unwrap(),
                        args[1].as_i32().unwrap(),
                        args[2].as_i32().unwrap(),
                    ),
                )
                .map(|r| out[0] = Val::I32(r)),
            FastRunner::I32x4ToI32(f) => f
                .call(
                    &mut self.store,
                    (
                        args[0].as_i32().unwrap(),
                        args[1].as_i32().unwrap(),
                        args[2].as_i32().unwrap(),
                        args[3].as_i32().unwrap(),
                    ),
                )
                .map(|r| out[0] = Val::I32(r)),
            FastRunner::I64ToI64(f) => f
                .call(&mut self.store, args[0].as_i64().unwrap())
                .map(|r| out[0] = Val::I64(r)),
            FastRunner::I64x2ToI64(f) => f
                .call(
                    &mut self.store,
                    (args[0].as_i64().unwrap(), args[1].as_i64().unwrap()),
                )
                .map(|r| out[0] = Val::I64(r)),
            FastRunner::I64x3ToI64(f) => f
                .call(
                    &mut self.store,
                    (
                        args[0].as_i64().unwrap(),
                        args[1].as_i64().unwrap(),
                        args[2].as_i64().unwrap(),
                    ),
                )
                .map(|r| out[0] = Val::I64(r)),
            FastRunner::I32ToI64(f) => f
                .call(&mut self.store, args[0].as_i32().unwrap())
                .map(|r| out[0] = Val::I64(r)),
            FastRunner::I32x2ToI64(f) => f
                .call(
                    &mut self.store,
                    (args[0].as_i32().unwrap(), args[1].as_i32().unwrap()),
                )
                .map(|r| out[0] = Val::I64(r)),
            FastRunner::I32x3ToI64(f) => f
                .call(
                    &mut self.store,
                    (
                        args[0].as_i32().unwrap(),
                        args[1].as_i32().unwrap(),
                        args[2].as_i32().unwrap(),
                    ),
                )
                .map(|r| out[0] = Val::I64(r)),
            FastRunner::I64ToI32(f) => f
                .call(&mut self.store, args[0].as_i64().unwrap())
                .map(|r| out[0] = Val::I32(r)),
            FastRunner::I32I64ToI32(f) => f
                .call(
                    &mut self.store,
                    (args[0].as_i32().unwrap(), args[1].as_i64().unwrap()),
                )
                .map(|r| out[0] = Val::I32(r)),
            FastRunner::I64I32ToI32(f) => f
                .call(
                    &mut self.store,
                    (args[0].as_i64().unwrap(), args[1].as_i32().unwrap()),
                )
                .map(|r| out[0] = Val::I32(r)),
            FastRunner::Generic(f) => {
                for (dst, &src) in self.params_buf.iter_mut().zip(args) {
                    *dst = to_wt_val(src);
                }
                match f.call(&mut self.store, &self.params_buf, &mut self.results_buf) {
                    Ok(()) => {
                        for (dst, src) in out.iter_mut().zip(&self.results_buf) {
                            *dst = from_wt_val(src).map_err(|_| TrapCode::Unreachable)?;
                        }
                        Ok(())
                    }
                    Err(e) => Err(e),
                }
            }
        };
        res.map_err(|e| map_wasmtime_trap(&e))
    }

    fn snapshot_exported_memories(&self) -> Vec<Vec<u8>> {
        self.exported_memories
            .iter()
            .map(|m| m.data(&self.store).to_vec())
            .collect()
    }

    fn snapshot_exported_globals(&mut self) -> Result<Vec<Val>, WasmError> {
        let mut vals = Vec::with_capacity(self.exported_globals.len());
        for &g in &self.exported_globals {
            vals.push(from_wt_val(&g.get(&mut self.store))?);
        }
        Ok(vals)
    }
}

struct SplitMix64(u64);
impl SplitMix64 {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
}

const I32_BOUNDARIES: &[i32] = &[
    0,
    1,
    -1,
    2,
    -2,
    3,
    4,
    7,
    8,
    15,
    16,
    31,
    32,
    63,
    64,
    127,
    128,
    255,
    256,
    512,
    1024,
    4095,
    4096,
    4097,
    32767,
    32768,
    65535,
    65536,
    65537,
    65532,
    65533,
    65534,
    131071,
    131072,
    1048575,
    1048576,
    i32::MAX,
    i32::MAX - 1,
    i32::MIN,
    i32::MIN + 1,
    -4,
    -8,
    -16,
    -32,
    -64,
    -128,
    -256,
    -65536,
    0x5555_5555,
    -0x5555_5556,
    0x00FF_FFFF,
    -0x0100_0000,
    0x4000_0000,
    -0x4000_0000,
];

const I64_BOUNDARIES: &[i64] = &[
    0,
    1,
    -1,
    2,
    -2,
    3,
    4,
    7,
    8,
    15,
    16,
    31,
    32,
    63,
    64,
    127,
    128,
    255,
    256,
    4096,
    65535,
    65536,
    65537,
    i32::MAX as i64,
    i32::MIN as i64,
    u32::MAX as i64,
    (u32::MAX as i64) + 1,
    i64::MAX,
    i64::MAX - 1,
    i64::MIN,
    i64::MIN + 1,
    -4,
    -8,
    -64,
    -65536,
    0x5555_5555_5555_5555,
    -0x5555_5555_5555_5556,
    1i64 << 31,
    1i64 << 32,
    1i64 << 48,
    1i64 << 62,
    -(1i64 << 62),
];

const F32_BOUNDARIES: &[u32] = &[
    0x0000_0000, // +0.0
    0x8000_0000, // -0.0
    0x0000_0001, // +subnormal_min
    0x8000_0001, // -subnormal_min
    0x007f_ffff, // +subnormal_max
    0x807f_ffff, // -subnormal_max
    0x0080_0000, // +normal_min
    0x8080_0000, // -normal_min
    0x3e80_0000, // +0.25
    0xbe80_0000, // -0.25
    0x3f00_0000, // +0.5
    0xbf00_0000, // -0.5
    0x3f40_0000, // +0.75
    0xbf40_0000, // -0.75
    0x3f7f_ffff, // next_down(1.0)
    0xbf7f_ffff, // next_up(-1.0)
    0x3f80_0000, // +1.0
    0xbf80_0000, // -1.0
    0x3fc0_0000, // +1.5
    0xbfc0_0000, // -1.5
    0x4000_0000, // +2.0
    0xc000_0000, // -2.0
    0x4020_0000, // +2.5
    0xc020_0000, // -2.5
    0x4060_0000, // +3.5
    0xc060_0000, // -3.5
    0x4b00_0000, // +2^23
    0xcb00_0000, // -2^23
    0x4eff_ffff, // largest f32 < 2^31 (2147483520.0)
    0x4f00_0000, // +2^31 (2147483648.0)
    0xcf00_0000, // -2^31 (i32::MIN as f32)
    0xcf00_0001, // next_down(-2^31)
    0x4f7f_ffff, // largest f32 < 2^32 (4294967040.0)
    0x4f80_0000, // +2^32 (4294967296.0)
    0x5eff_ffff, // largest f32 < 2^63
    0x5f00_0000, // +2^63
    0xdf00_0000, // -2^63 (i64::MIN as f32)
    0xdf00_0001, // next_down(-2^63)
    0x5f7f_ffff, // largest f32 < 2^64
    0x5f80_0000, // +2^64
    0x7f7f_ffff, // +f32::MAX
    0xff7f_ffff, // -f32::MAX
    0x7f80_0000, // +Inf
    0xff80_0000, // -Inf
    0x7fc0_0000, // canonical qNaN
    0xffc0_0000, // negative canonical qNaN
    0x7fc0_0001, // non-canonical qNaN
    0xffc0_1234, // negative non-canonical qNaN
    0x7f80_0001, // positive sNaN
    0xff80_0001, // negative sNaN
];

const F64_BOUNDARIES: &[u64] = &[
    0x0000_0000_0000_0000, // +0.0
    0x8000_0000_0000_0000, // -0.0
    0x0000_0000_0000_0001, // +subnormal_min
    0x8000_0000_0000_0001, // -subnormal_min
    0x000f_ffff_ffff_ffff, // +subnormal_max
    0x800f_ffff_ffff_ffff, // -subnormal_max
    0x0010_0000_0000_0000, // +normal_min
    0x8010_0000_0000_0000, // -normal_min
    0x3fe0_0000_0000_0000, // +0.5
    0xbfe0_0000_0000_0000, // -0.5
    0x3fef_ffff_ffff_ffff, // next_down(1.0)
    0xbfef_ffff_ffff_ffff, // next_up(-1.0)
    0x3ff0_0000_0000_0000, // +1.0
    0xbff0_0000_0000_0000, // -1.0
    0x3ff8_0000_0000_0000, // +1.5
    0xbff8_0000_0000_0000, // -1.5
    0x4000_0000_0000_0000, // +2.0
    0xc000_0000_0000_0000, // -2.0
    0x4004_0000_0000_0000, // +2.5
    0xc004_0000_0000_0000, // -2.5
    0x41df_ffff_ffc0_0000, // i32::MAX as f64 (2147483647.0)
    0x41df_ffff_ffff_ffff, // next_down(2^31) (2147483647.9999998)
    0x41e0_0000_0000_0000, // +2^31 (2147483648.0)
    0xc1e0_0000_0000_0000, // -2^31 (-2147483648.0)
    0xc1e0_0000_001c_cccc, // ~-2147483648.9 (valid for i32.trunc_f64_s!)
    0xc1e0_0000_0020_0000, // -2^31 - 1 (-2147483649.0, traps i32.trunc_f64_s!)
    0x41ef_ffff_ffe0_0000, // u32::MAX as f64
    0x41ef_ffff_ffff_ffff, // next_down(2^32)
    0x41f0_0000_0000_0000, // +2^32
    0x4330_0000_0000_0000, // +2^52
    0xc330_0000_0000_0000, // -2^52
    0x43df_ffff_ffff_ffff, // largest f64 < 2^63
    0x43e0_0000_0000_0000, // +2^63
    0xc3e0_0000_0000_0000, // -2^63 (i64::MIN as f64)
    0xc3e0_0000_0000_0001, // next_down(-2^63)
    0x43ef_ffff_ffff_ffff, // largest f64 < 2^64
    0x43f0_0000_0000_0000, // +2^64
    0x47ef_ffff_e000_0000, // +f32::MAX as f64
    0xc7ef_ffff_e000_0000, // -f32::MAX as f64
    0x7fef_ffff_ffff_ffff, // +f64::MAX
    0xffef_ffff_ffff_ffff, // -f64::MAX
    0x7ff0_0000_0000_0000, // +Inf
    0xfff0_0000_0000_0000, // -Inf
    0x7ff8_0000_0000_0000, // canonical qNaN
    0xfff8_0000_0000_0000, // negative canonical qNaN
    0x7ff8_0000_0000_0001, // non-canonical qNaN
    0xfff8_1234_5678_9abc, // negative non-canonical qNaN
    0x7ff0_0000_0000_0001, // positive sNaN
    0xfff0_0000_0000_0001, // negative sNaN
];

const fn pack_u32x4(a: u32, b: u32, c: u32, d: u32) -> u128 {
    (a as u128) | ((b as u128) << 32) | ((c as u128) << 64) | ((d as u128) << 96)
}

const fn pack_u64x2(a: u64, b: u64) -> u128 {
    (a as u128) | ((b as u128) << 64)
}

const V128_BOUNDARIES: &[u128] = &[
    0u128,
    u128::MAX,
    0x5555_5555_5555_5555_5555_5555_5555_5555u128,
    0xAAAA_AAAA_AAAA_AAAA_AAAA_AAAA_AAAA_AAAAu128,
    u128::from_le_bytes([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]),
    u128::from_le_bytes([15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]),
    u128::from_le_bytes([0, 15, 16, 17, 31, 32, 127, 128, 255, 1, 2, 3, 14, 15, 16, 200]),
    pack_u32x4(0, 1, u32::MAX, 0x8000_0000),
    pack_u32x4(0x7fff_ffff, 0x8000_0000, u32::MAX, 0),
    pack_u32x4(0x8000_0000, 0x8000_0000, 0x7fff_ffff, 0x7fff_ffff),
    pack_u64x2(0, u64::MAX),
    pack_u64x2(0x8000_0000_0000_0000, 0x7fff_ffff_ffff_ffff),
    pack_u64x2(0x7fff_ffff_ffff_ffff, 0x8000_0000_0000_0000),
    // f32x4 edge patterns
    pack_u32x4(0x0000_0000, 0x8000_0000, 0x3f80_0000, 0xbf80_0000), // [+0.0, -0.0, +1.0, -1.0]
    pack_u32x4(0x8000_0000, 0x0000_0000, 0xbf80_0000, 0x3f80_0000), // [-0.0, +0.0, -1.0, +1.0]
    pack_u32x4(0x7f80_0000, 0xff80_0000, 0x7fc0_0000, 0x7f80_0001), // [+Inf, -Inf, qNaN, sNaN]
    pack_u32x4(0x7fc0_0001, 0xffc0_1234, 0xff80_0001, 0x3f00_0000), // [non-canon qNaNs, -sNaN, +0.5]
    pack_u32x4(0x0000_0001, 0x8000_0001, 0x7f7f_ffff, 0xff7f_ffff), // [±subnormal_min, ±f32::MAX]
    pack_u32x4(0xbf00_0000, 0x3f00_0000, 0x3fc0_0000, 0x4020_0000), // [-0.5, +0.5, +1.5, +2.5]
    pack_u32x4(0xcf00_0000, 0x4f00_0000, 0xbf80_0000, 0x4f80_0000), // [-2^31, 2^31, -1.0, 2^32]
    // f64x2 edge patterns
    pack_u64x2(0x0000_0000_0000_0000, 0x8000_0000_0000_0000), // [+0.0, -0.0]
    pack_u64x2(0x8000_0000_0000_0000, 0x0000_0000_0000_0000), // [-0.0, +0.0]
    pack_u64x2(0x7ff0_0000_0000_0000, 0xfff0_0000_0000_0000), // [+Inf, -Inf]
    pack_u64x2(0x7ff8_0000_0000_0000, 0x7ff0_0000_0000_0001), // [qNaN, sNaN]
    pack_u64x2(0x7ff8_0000_0000_0001, 0xfff8_1234_5678_9abc), // [non-canon qNaNs]
    pack_u64x2(0x0000_0000_0000_0001, 0x8000_0000_0000_0001), // [±subnormal_min]
    pack_u64x2(0xbfe0_0000_0000_0000, 0x4004_0000_0000_0000), // [-0.5, +2.5]
    pack_u64x2(0x7fef_ffff_ffff_ffff, 0xffef_ffff_ffff_ffff), // [±f64::MAX]
];

struct VectorGen<'a> {
    params: &'a [ValType],
    total: usize,
    emitted: usize,
    rng: SplitMix64,
    phase: usize,
    idx_a: usize,
    idx_b: usize,
}

impl<'a> VectorGen<'a> {
    fn new(params: &'a [ValType], cfg: &FuzzConfig) -> Self {
        let total = if params.is_empty() {
            cfg.total_vectors.min(1)
        } else {
            cfg.total_vectors
        };
        Self {
            params,
            total,
            emitted: 0,
            rng: SplitMix64(cfg.seed),
            phase: 0,
            idx_a: 0,
            idx_b: 0,
        }
    }

    fn boundary_val(ty: ValType, idx: usize) -> Val {
        match ty {
            ValType::I32 => Val::I32(I32_BOUNDARIES[idx % I32_BOUNDARIES.len()]),
            ValType::I64 => Val::I64(I64_BOUNDARIES[idx % I64_BOUNDARIES.len()]),
            ValType::F32 => Val::F32(F32_BOUNDARIES[idx % F32_BOUNDARIES.len()]),
            ValType::F64 => Val::F64(F64_BOUNDARIES[idx % F64_BOUNDARIES.len()]),
            ValType::V128 => Val::V128(V128_BOUNDARIES[idx % V128_BOUNDARIES.len()]),
        }
    }

    fn rand_val(&mut self, ty: ValType) -> Val {
        let r = self.rng.next();
        match ty {
            ValType::I32 => {
                if (r & 7) == 0 {
                    Self::boundary_val(ValType::I32, (r >> 8) as usize)
                } else {
                    Val::I32((r ^ (r >> 32)) as i32)
                }
            }
            ValType::I64 => {
                if (r & 7) == 0 {
                    Self::boundary_val(ValType::I64, (r >> 8) as usize)
                } else {
                    Val::I64(r as i64)
                }
            }
            ValType::F32 => match r & 3 {
                0 => Self::boundary_val(ValType::F32, (r >> 8) as usize),
                1 => {
                    // Structured finite / subnormal / special float bit pattern
                    let sign = ((r >> 2) as u32 & 1) << 31;
                    let exp = match (r >> 3) & 3 {
                        0 => 0u32,                              // subnormal / zero
                        1 => 127u32.wrapping_add(((r >> 8) & 15) as u32).wrapping_sub(7), // near 1.0
                        2 => 0xff,                              // Inf / NaN
                        _ => ((r >> 8) as u32) & 0xff,
                    };
                    let frac = ((r >> 16) as u32) & 0x007f_ffff;
                    Val::F32(sign | (exp << 23) | frac)
                }
                _ => Val::F32((r ^ (r >> 32)) as u32),
            },
            ValType::F64 => match r & 3 {
                0 => Self::boundary_val(ValType::F64, (r >> 8) as usize),
                1 => {
                    let sign = ((r >> 2) & 1) << 63;
                    let exp = match (r >> 3) & 3 {
                        0 => 0u64,
                        1 => 1023u64.wrapping_add((r >> 8) & 31).wrapping_sub(15),
                        2 => 0x7ff,
                        _ => (r >> 8) & 0x7ff,
                    };
                    let frac = self.rng.next() & 0x000f_ffff_ffff_ffff;
                    Val::F64(sign | (exp << 52) | frac)
                }
                _ => Val::F64(r),
            },
            ValType::V128 => match r & 3 {
                0 => Self::boundary_val(ValType::V128, (r >> 8) as usize),
                1 => {
                    // Compose 4 f32/i32 edge lanes or 2 f64 edge lanes
                    let r2 = self.rng.next();
                    if (r & 4) == 0 {
                        let a = F32_BOUNDARIES[(r >> 8) as usize % F32_BOUNDARIES.len()];
                        let b = F32_BOUNDARIES[(r >> 24) as usize % F32_BOUNDARIES.len()];
                        let c = F32_BOUNDARIES[(r2 >> 8) as usize % F32_BOUNDARIES.len()];
                        let d = F32_BOUNDARIES[(r2 >> 24) as usize % F32_BOUNDARIES.len()];
                        Val::V128(pack_u32x4(a, b, c, d))
                    } else {
                        let a = F64_BOUNDARIES[(r >> 8) as usize % F64_BOUNDARIES.len()];
                        let b = F64_BOUNDARIES[(r2 >> 8) as usize % F64_BOUNDARIES.len()];
                        Val::V128(pack_u64x2(a, b))
                    }
                }
                _ => {
                    let hi = self.rng.next();
                    Val::V128((r as u128) | ((hi as u128) << 64))
                }
            },
        }
    }

    fn next_into(&mut self, out: &mut [Val]) -> bool {
        if self.emitted >= self.total {
            return false;
        }
        self.emitted += 1;

        let n = self.params.len();
        if n == 0 {
            return true;
        }
        if n == 1 {
            let max_b = match self.params[0] {
                ValType::I32 => I32_BOUNDARIES.len(),
                ValType::I64 => I64_BOUNDARIES.len(),
                ValType::F32 => F32_BOUNDARIES.len(),
                ValType::F64 => F64_BOUNDARIES.len(),
                ValType::V128 => V128_BOUNDARIES.len(),
            };
            if self.idx_a < max_b {
                out[0] = Self::boundary_val(self.params[0], self.idx_a);
                self.idx_a += 1;
            } else {
                out[0] = self.rand_val(self.params[0]);
            }
            return true;
        }

        // Phase 0: diagonal boundary vectors (b, b, ..., b)
        if self.phase == 0 {
            for (slot, &ty) in out.iter_mut().zip(self.params) {
                *slot = Self::boundary_val(ty, self.idx_a);
            }
            self.idx_a += 1;
            let max_diag = I32_BOUNDARIES
                .len()
                .max(I64_BOUNDARIES.len())
                .max(F32_BOUNDARIES.len())
                .max(F64_BOUNDARIES.len())
                .max(V128_BOUNDARIES.len());
            if self.idx_a >= max_diag {
                self.phase = 1;
                self.idx_a = 0;
                self.idx_b = 0;
            }
            return true;
        }

        // Phase 1: pairwise core boundaries across first 2 params (holding rest at 0/1/-1)
        const CORE_LEN: usize = 22;
        if self.phase == 1 {
            out[0] = Self::boundary_val(self.params[0], self.idx_a);
            out[1] = Self::boundary_val(self.params[1], self.idx_b);
            for slot_idx in 2..n {
                out[slot_idx] = Self::boundary_val(self.params[slot_idx], self.idx_a + slot_idx);
            }
            self.idx_b += 1;
            if self.idx_b >= CORE_LEN {
                self.idx_b = 0;
                self.idx_a += 1;
                if self.idx_a >= CORE_LEN {
                    self.phase = 2;
                }
            }
            return true;
        }

        // Phase 2: PRNG with boundary injection
        for i in 0..n {
            out[i] = self.rand_val(self.params[i]);
        }
        true
    }
}

/// Fuzzes equivalence between two `.wasm` modules at `entry` using pre-compiled,
/// pre-instantiated `wasmtime` instances.
pub fn fuzz_equivalence(
    lhs_wasm: &[u8],
    rhs_wasm: &[u8],
    entry: FuncId,
    cfg: &FuzzConfig,
) -> Result<FuzzOutcome, WasmError> {
    let lhs_prep = prepare_module(lhs_wasm, EntryTarget::FuncId(entry))?;
    let rhs_prep = prepare_module(rhs_wasm, EntryTarget::FuncId(entry))?;
    fuzz_prepared(&lhs_prep, &rhs_prep, cfg)
}

/// Fuzzes equivalence between two `.wasm` modules by exported function name.
pub fn fuzz_equivalence_by_name(
    lhs_wasm: &[u8],
    rhs_wasm: &[u8],
    export_name: &str,
    cfg: &FuzzConfig,
) -> Result<FuzzOutcome, WasmError> {
    let lhs_prep = prepare_module(lhs_wasm, EntryTarget::ExportName(export_name))?;
    let rhs_prep = prepare_module(rhs_wasm, EntryTarget::ExportName(export_name))?;
    fuzz_prepared(&lhs_prep, &rhs_prep, cfg)
}

fn fuzz_prepared(
    lhs_prep: &PreparedModule,
    rhs_prep: &PreparedModule,
    cfg: &FuzzConfig,
) -> Result<FuzzOutcome, WasmError> {
    if lhs_prep.sig.params != rhs_prep.sig.params || lhs_prep.sig.results != rhs_prep.sig.results {
        return Err(WasmError::ValidationError(format!(
            "entry function signature mismatch: LHS ({:?}) -> ({:?}) vs RHS ({:?}) -> ({:?})",
            lhs_prep.sig.params,
            lhs_prep.sig.results,
            rhs_prep.sig.params,
            rhs_prep.sig.results
        )));
    }

    let mut lhs = CompiledInstance::compile(lhs_prep)?;
    let mut rhs = CompiledInstance::compile(rhs_prep)?;

    // Fast check if memories differ in count or cannot change at runtime.
    let mut initial_mem_diff = lhs.exported_memories.len() != rhs.exported_memories.len();
    if !initial_mem_diff {
        for (lm, rm) in lhs.exported_memories.iter().zip(&rhs.exported_memories) {
            if lm.data(&lhs.store) != rm.data(&rhs.store) {
                initial_mem_diff = true;
                break;
            }
        }
    }

    let check_mems_every_run =
        lhs_prep.has_mem_writes || rhs_prep.has_mem_writes || initial_mem_diff;
    let check_globals_every_run = !lhs.exported_globals.is_empty()
        || !rhs.exported_globals.is_empty();

    let start = Instant::now();
    let mut vec_gen = VectorGen::new(&lhs_prep.sig.params, cfg);
    let mut inputs: Vec<Val> = lhs_prep
        .sig
        .params
        .iter()
        .copied()
        .map(Val::default_for)
        .collect();
    let mut tested = 0usize;

    while vec_gen.next_into(&mut inputs) {
        if tested == 0 {
            lhs.store
                .set_fuel(cfg.fuel_per_run)
                .map_err(|e| WasmError::ValidationError(e.to_string()))?;
            rhs.store
                .set_fuel(cfg.fuel_per_run)
                .map_err(|e| WasmError::ValidationError(e.to_string()))?;
        } else {
            lhs.reset_state(lhs_prep, cfg.fuel_per_run)?;
            rhs.reset_state(rhs_prep, cfg.fuel_per_run)?;
        }
        tested += 1;

        let lhs_res = lhs.call_fast(&inputs);
        let rhs_res = rhs.call_fast(&inputs);

        let outcomes_match = match (&lhs_res, &rhs_res) {
            (Ok(()), Ok(())) => lhs.out_vals_buf == rhs.out_vals_buf,
            (Err(lt), Err(rt)) => lt == rt,
            _ => false,
        };

        let mems_match = if !outcomes_match {
            false
        } else if !check_mems_every_run || lhs_res.is_err() {
            true
        } else {
            lhs.exported_memories.len() == rhs.exported_memories.len()
                && lhs
                    .exported_memories
                    .iter()
                    .zip(&rhs.exported_memories)
                    .all(|(lm, rm)| lm.data(&lhs.store) == rm.data(&rhs.store))
        };

        let globals_match = if !outcomes_match || !mems_match {
            false
        } else if !check_globals_every_run || lhs_res.is_err() {
            true
        } else {
            lhs.snapshot_exported_globals()? == rhs.snapshot_exported_globals()?
        };

        if !outcomes_match || !mems_match || !globals_match {
            let lhs_outcome = match lhs_res {
                Ok(()) => ExecOutcome::Values(lhs.out_vals_buf.clone()),
                Err(t) => ExecOutcome::Trap(t),
            };
            let rhs_outcome = match rhs_res {
                Ok(()) => ExecOutcome::Values(rhs.out_vals_buf.clone()),
                Err(t) => ExecOutcome::Trap(t),
            };
            let memory_snapshots = if !lhs.exported_memories.is_empty() {
                lhs.snapshot_exported_memories()
            } else {
                rhs.snapshot_exported_memories()
            };
            return Ok(FuzzOutcome::Falsified(Counterexample {
                inputs,
                memory_snapshots,
                lhs_outcome,
                rhs_outcome,
            }));
        }
    }

    Ok(FuzzOutcome::NoCounterexample {
        vectors_tested: tested,
        elapsed_micros: start.elapsed().as_micros() as u64,
    })
}

/// Runs a single exported Wasm function under `wasmtime` with explicit fuel,
/// returning its `ExecOutcome` and snapshots of all exported linear memories.
pub fn run_wasmtime_func(
    wasm_bytes: &[u8],
    func_name: &str,
    args: &[Val],
    fuel: u64,
) -> Result<(ExecOutcome, Vec<Vec<u8>>), WasmError> {
    let prep = prepare_module(wasm_bytes, EntryTarget::ExportName(func_name))?;
    if args.len() != prep.sig.params.len()
        || args
            .iter()
            .zip(&prep.sig.params)
            .any(|(a, &t)| a.val_type() != t)
    {
        return Err(WasmError::ValidationError(
            "argument count or types do not match target function".into(),
        ));
    }
    let mut inst = CompiledInstance::compile(&prep)?;
    inst.store
        .set_fuel(fuel)
        .map_err(|e| WasmError::ValidationError(e.to_string()))?;
    let outcome = match inst.call_fast(args) {
        Ok(()) => ExecOutcome::Values(inst.out_vals_buf.clone()),
        Err(t) => ExecOutcome::Trap(t),
    };
    let mems = inst.snapshot_exported_memories();
    Ok((outcome, mems))
}

/// Verifies `wasm_bytes` <-> `lift_wasm` -> `emit_wasm` round-trip equivalence via Stage-1 fuzzing.
pub fn verify_round_trip(
    wasm_bytes: &[u8],
    entry: FuncId,
    cfg: &FuzzConfig,
) -> Result<FuzzOutcome, WasmError> {
    let module = lift_wasm(wasm_bytes)?;
    let reemitted = emit_wasm(&module)?;
    fuzz_equivalence(wasm_bytes, &reemitted, entry, cfg)
}

/// Runs 3-way differential verification on `inputs`:
/// `gnomon_kernel::eval_func(lift_wasm(w))` === `wasmtime(w)` === `wasmtime(emit_wasm(lift_wasm(w)))`
/// checking values, trap codes, and exported linear memory bytes on every vector.
pub fn differential_check(
    wasm_bytes: &[u8],
    entry: FuncId,
    inputs: &[Vec<Val>],
    fuel: u64,
) -> Result<(), WasmError> {
    let module = lift_wasm(wasm_bytes)?;
    let reemitted = emit_wasm(&module)?;
    let registry = StratumRegistry::new();

    let orig_prep = prepare_module(wasm_bytes, EntryTarget::FuncId(entry))?;
    let reemit_prep = prepare_module(&reemitted, EntryTarget::FuncId(entry))?;
    let mut orig_inst = CompiledInstance::compile(&orig_prep)?;
    let mut reemit_inst = CompiledInstance::compile(&reemit_prep)?;

    for (vec_idx, args) in inputs.iter().enumerate() {
        if args.len() != orig_prep.sig.params.len()
            || args
                .iter()
                .zip(&orig_prep.sig.params)
                .any(|(a, &t)| a.val_type() != t)
        {
            return Err(WasmError::ValidationError(format!(
                "differential_check vector {vec_idx} args do not match function signature"
            )));
        }
        if vec_idx == 0 {
            orig_inst
                .store
                .set_fuel(fuel)
                .map_err(|e| WasmError::ValidationError(e.to_string()))?;
            reemit_inst
                .store
                .set_fuel(fuel)
                .map_err(|e| WasmError::ValidationError(e.to_string()))?;
        } else {
            orig_inst.reset_state(&orig_prep, fuel)?;
            reemit_inst.reset_state(&reemit_prep, fuel)?;
        }

        let orig_res = orig_inst.call_fast(args);
        let reemit_res = reemit_inst.call_fast(args);

        let orig_outcome = match orig_res {
            Ok(()) => ExecOutcome::Values(orig_inst.out_vals_buf.clone()),
            Err(t) => ExecOutcome::Trap(t),
        };
        let reemit_outcome = match reemit_res {
            Ok(()) => ExecOutcome::Values(reemit_inst.out_vals_buf.clone()),
            Err(t) => ExecOutcome::Trap(t),
        };

        let init_heap = HeapState::from_module(&module, fuel).map_err(|t| {
            WasmError::ValidationError(format!("failed to initialize kernel HeapState: {t:?}"))
        })?;
        let kernel_eval = eval_func(&module, &registry, entry, args, init_heap);
        let kernel_outcome = match &kernel_eval {
            Ok((vals, _)) => ExecOutcome::Values(vals.clone()),
            Err(t) => ExecOutcome::Trap(*t),
        };

        if kernel_outcome != orig_outcome || orig_outcome != reemit_outcome {
            return Err(WasmError::ValidationError(format!(
                "differential outcome mismatch at vector {vec_idx} ({args:?}): \
                 kernel={kernel_outcome:?}, orig_wasmtime={orig_outcome:?}, roundtrip_wasmtime={reemit_outcome:?}"
            )));
        }

        if let Ok((_, heap)) = kernel_eval {
            let orig_mems = orig_inst.snapshot_exported_memories();
            let reemit_mems = reemit_inst.snapshot_exported_memories();
            let kernel_mems: Vec<Vec<u8>> = module
                .memory_exports
                .iter()
                .map(|(_, mid)| {
                    heap.memory(*mid)
                        .map(|m| m.bytes.clone())
                        .map_err(|t| WasmError::ValidationError(format!("missing mem: {t:?}")))
                })
                .collect::<Result<Vec<_>, _>>()?;

            if kernel_mems != orig_mems || orig_mems != reemit_mems {
                return Err(WasmError::ValidationError(format!(
                    "differential memory mismatch at vector {vec_idx} ({args:?})"
                )));
            }

            if !module.global_exports.is_empty() {
                let orig_globs = orig_inst.snapshot_exported_globals()?;
                let reemit_globs = reemit_inst.snapshot_exported_globals()?;
                let kernel_globs: Vec<Val> = module
                    .global_exports
                    .iter()
                    .map(|(_, gid)| {
                        heap.globals
                            .get(gid.0 as usize)
                            .copied()
                            .ok_or_else(|| WasmError::ValidationError(format!("missing global {gid:?}")))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                if kernel_globs != orig_globs || orig_globs != reemit_globs {
                    return Err(WasmError::ValidationError(format!(
                        "differential exported global mismatch at vector {vec_idx} ({args:?})"
                    )));
                }
            }
        }
    }

    Ok(())
}
