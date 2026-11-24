//! Lossless deterministic `wasm32` -> `GnomonIR` lifter powered by `wasmparser`.

use std::collections::{BTreeSet, HashMap};

use gnomon_kernel::{
    BinOp, CallTarget, EffectOp, FuncDef, FuncId, GlobalDef, GlobalId, HostCallId, HostContract,
    LaneKind, MemId, MemWidth, MemoryDef, Module, Op, Region, RegionBuilder, RegionNode, Stmt,
    TrapCode, UnOp, Val, ValId, ValType,
};
use wasmparser::{
    BlockType, CompositeInnerType, ConstExpr, DataKind, ExternalKind, FuncType, FunctionBody,
    MemArg, MemArgTarget, Operator, Parser, Payload, TypeRef, ValType as WValType, Validator,
    WasmFeatures,
};

use crate::WasmError;

#[derive(Clone, Debug)]
struct FuncSig {
    params: Vec<ValType>,
    results: Vec<ValType>,
}

/// Lifts a deterministic `wasm32` binary module into `gnomon_kernel::Module`.
pub fn lift_wasm(bytes: &[u8]) -> Result<Module, WasmError> {
    let mut validator = Validator::new_with_features(WasmFeatures::default());
    validator
        .validate_all(bytes)
        .map_err(|e| WasmError::ValidationError(e.to_string()))?;

    let mut types: Vec<Option<FuncSig>> = Vec::new();
    let mut imported_funcs: Vec<(String, String, u32)> = Vec::new();
    let mut defined_func_type_idxs: Vec<u32> = Vec::new();
    let mut memories: Vec<MemoryDef> = Vec::new();
    let mut globals: Vec<GlobalDef> = Vec::new();
    let mut func_exports: HashMap<u32, String> = HashMap::new();
    let mut memory_exports: Vec<(String, MemId)> = Vec::new();
    let mut global_exports: Vec<(String, GlobalId)> = Vec::new();
    let mut bodies: Vec<FunctionBody<'_>> = Vec::new();
    let mut has_non_empty_elements = false;

    for payload in Parser::new(0).parse_all(bytes) {
        let payload = payload.map_err(|e| WasmError::ParseError(e.to_string()))?;
        match payload {
            Payload::Version { encoding, .. } => {
                if encoding != wasmparser::Encoding::Module {
                    return Err(WasmError::UnsupportedFeature(
                        "WebAssembly components are not supported".into(),
                    ));
                }
            }
            Payload::TypeSection(reader) => {
                for rec in reader {
                    let rec = rec.map_err(|e| WasmError::ParseError(e.to_string()))?;
                    for sub in rec.into_types() {
                        if sub.composite_type.shared {
                            return Err(WasmError::UnsupportedFeature(
                                "shared composite types are not supported".into(),
                            ));
                        }
                        match sub.composite_type.inner {
                            CompositeInnerType::Func(ft) => {
                                types.push(try_convert_func_type(&ft).ok());
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
                            imported_funcs.push((
                                imp.module.to_owned(),
                                imp.name.to_owned(),
                                type_idx,
                            ));
                        }
                        TypeRef::FuncExact(_) => {
                            return Err(WasmError::UnsupportedFeature(
                                "exact function imports are not supported".into(),
                            ));
                        }
                        TypeRef::Memory(_) => {
                            return Err(WasmError::UnsupportedFeature(
                                "imported linear memories are not supported".into(),
                            ));
                        }
                        TypeRef::Global(_) => {
                            return Err(WasmError::UnsupportedFeature(
                                "imported globals are not supported".into(),
                            ));
                        }
                        TypeRef::Table(_) => {
                            return Err(WasmError::UnsupportedFeature(
                                "imported tables are not supported".into(),
                            ));
                        }
                        TypeRef::Tag(_) => {
                            return Err(WasmError::UnsupportedFeature(
                                "exception tags are not supported".into(),
                            ));
                        }
                    }
                }
            }
            Payload::FunctionSection(reader) => {
                for type_idx in reader {
                    let type_idx = type_idx.map_err(|e| WasmError::ParseError(e.to_string()))?;
                    defined_func_type_idxs.push(type_idx);
                }
            }
            Payload::TableSection(_) => {
                // `rustc` often emits an unused funcref table; actual table ops or
                // non-empty element initializers are rejected below.
            }
            Payload::MemorySection(reader) => {
                for mem in reader {
                    let mem = mem.map_err(|e| WasmError::ParseError(e.to_string()))?;
                    if mem.memory64 {
                        return Err(WasmError::UnsupportedFeature(
                            "memory64 is not supported; only wasm32 is supported".into(),
                        ));
                    }
                    if mem.shared {
                        return Err(WasmError::UnsupportedFeature(
                            "shared memories are not supported".into(),
                        ));
                    }
                    if mem.page_size_log2.is_some_and(|p| p != 16) {
                        return Err(WasmError::UnsupportedFeature(
                            "custom page sizes are not supported".into(),
                        ));
                    }
                    let id_u16 = u16::try_from(memories.len()).map_err(|_| {
                        WasmError::UnsupportedFeature("too many memories for MemId(u16)".into())
                    })?;
                    let min_pages = u32::try_from(mem.initial).map_err(|_| {
                        WasmError::UnsupportedFeature("memory initial size exceeds u32".into())
                    })?;
                    let max_pages = mem
                        .maximum
                        .map(u32::try_from)
                        .transpose()
                        .map_err(|_| {
                            WasmError::UnsupportedFeature("memory maximum size exceeds u32".into())
                        })?;
                    memories.push(MemoryDef {
                        id: MemId(id_u16),
                        min_pages,
                        max_pages,
                        init_data: Vec::new(),
                    });
                }
            }
            Payload::TagSection(_) => {
                return Err(WasmError::UnsupportedFeature(
                    "exception handling tags are not supported".into(),
                ));
            }
            Payload::GlobalSection(reader) => {
                for glob in reader {
                    let glob = glob.map_err(|e| WasmError::ParseError(e.to_string()))?;
                    if glob.ty.shared {
                        return Err(WasmError::UnsupportedFeature(
                            "shared globals are not supported".into(),
                        ));
                    }
                    let ty = convert_val_type(glob.ty.content_type)?;
                    let init = eval_const_expr(&glob.init_expr, &globals)?;
                    if init.val_type() != ty {
                        return Err(WasmError::ValidationError(
                            "global init type mismatch".into(),
                        ));
                    }
                    let gid = GlobalId(u32::try_from(globals.len()).map_err(|_| {
                        WasmError::UnsupportedFeature("too many globals".into())
                    })?);
                    globals.push(GlobalDef {
                        id: gid,
                        ty,
                        mutable: glob.ty.mutable,
                        init,
                    });
                }
            }
            Payload::ExportSection(reader) => {
                for exp in reader {
                    let exp = exp.map_err(|e| WasmError::ParseError(e.to_string()))?;
                    match exp.kind {
                        ExternalKind::Func => {
                            func_exports.entry(exp.index).or_insert_with(|| exp.name.to_owned());
                        }
                        ExternalKind::Memory => {
                            let idx = u16::try_from(exp.index).map_err(|_| {
                                WasmError::UnsupportedFeature("exported memory index > u16".into())
                            })?;
                            memory_exports.push((exp.name.to_owned(), MemId(idx)));
                        }
                        ExternalKind::Global => {
                            global_exports.push((exp.name.to_owned(), GlobalId(exp.index)));
                        }
                        ExternalKind::Table => {
                            // Ignore unused exported tables unless table ops/elements exist.
                        }
                        ExternalKind::Tag | ExternalKind::FuncExact => {
                            return Err(WasmError::UnsupportedFeature(format!(
                                "unsupported export kind: {:?}",
                                exp.kind
                            )));
                        }
                    }
                }
            }
            Payload::StartSection { .. } => {
                return Err(WasmError::UnsupportedFeature(
                    "start sections are not supported".into(),
                ));
            }
            Payload::ElementSection(reader) => {
                for elem in reader {
                    let elem = elem.map_err(|e| WasmError::ParseError(e.to_string()))?;
                    if !matches!(elem.kind, wasmparser::ElementKind::Declared) {
                        has_non_empty_elements = true;
                    }
                }
            }
            Payload::DataCountSection { .. } => {}
            Payload::CodeSectionStart { .. } => {}
            Payload::CodeSectionEntry(body) => {
                bodies.push(body);
            }
            Payload::DataSection(reader) => {
                for seg in reader {
                    let seg = seg.map_err(|e| WasmError::ParseError(e.to_string()))?;
                    match seg.kind {
                        DataKind::Passive => {
                            return Err(WasmError::UnsupportedFeature(
                                "passive data segments are not supported".into(),
                            ));
                        }
                        DataKind::Active {
                            memory_index,
                            offset_expr,
                        } => {
                            let mem = memories.get_mut(memory_index as usize).ok_or_else(|| {
                                WasmError::ValidationError(format!(
                                    "data segment references unknown memory {memory_index}"
                                ))
                            })?;
                            let offset = match eval_const_expr(&offset_expr, &globals)? {
                                Val::I32(v) => v as u32,
                                _ => {
                                    return Err(WasmError::UnsupportedFeature(
                                        "non-i32 data segment offset is not supported".into(),
                                    ));
                                }
                            };
                            mem.init_data.push((offset, seg.data.to_vec()));
                        }
                    }
                }
            }
            Payload::CustomSection(_) => {}
            Payload::End(_) => {}
            other => {
                return Err(WasmError::UnsupportedFeature(format!(
                    "unsupported section payload: {other:?}"
                )));
            }
        }
    }

    if has_non_empty_elements {
        return Err(WasmError::UnsupportedFeature(
            "non-empty element segments (function tables) are not supported".into(),
        ));
    }

    if bodies.len() != defined_func_type_idxs.len() {
        return Err(WasmError::ValidationError(
            "function section and code section length mismatch".into(),
        ));
    }

    let lookup_sig = |type_idx: u32| -> Result<&FuncSig, WasmError> {
        types
            .get(type_idx as usize)
            .and_then(|o| o.as_ref())
            .ok_or_else(|| {
                WasmError::UnsupportedFeature(format!(
                    "type index {type_idx} uses unsupported value or non-function types"
                ))
            })
    };

    let num_imported = imported_funcs.len();
    let mut host_contracts = Vec::with_capacity(num_imported);
    let mut all_func_sigs: Vec<FuncSig> = Vec::with_capacity(num_imported + bodies.len());

    for (i, (mod_name, field_name, type_idx)) in imported_funcs.into_iter().enumerate() {
        let sig = lookup_sig(type_idx)?.clone();
        let params: Vec<(ValId, ValType)> = sig
            .params
            .iter()
            .enumerate()
            .map(|(k, &ty)| (ValId(k as u32), ty))
            .collect();
        let base = params.len() as u32;
        let results: Vec<(ValId, ValType)> = sig
            .results
            .iter()
            .enumerate()
            .map(|(k, &ty)| (ValId(base + k as u32), ty))
            .collect();
        let true_pred = || {
            Region::build(|b| {
                b.push_let(ValId(0), ValType::I32, Op::ConstI32(1));
                b.push_yield(&[ValId(0)]);
            })
        };
        host_contracts.push(HostContract {
            id: HostCallId(i as u32),
            module_name: mod_name,
            field_name,
            params,
            results,
            precondition: true_pred(),
            read_footprints: Vec::new(),
            write_footprints: Vec::new(),
            postcondition: true_pred(),
            sim_body: None,
        });
        all_func_sigs.push(sig);
    }

    for &type_idx in &defined_func_type_idxs {
        all_func_sigs.push(lookup_sig(type_idx)?.clone());
    }

    let mut funcs = Vec::with_capacity(bodies.len());
    for (def_idx, body) in bodies.iter().enumerate() {
        let wasm_func_idx = (num_imported + def_idx) as u32;
        let sig = &all_func_sigs[wasm_func_idx as usize];
        let export_name = func_exports.get(&wasm_func_idx).cloned();
        let name = export_name
            .clone()
            .unwrap_or_else(|| format!("func_{def_idx}"));

        let ctx = LiftModuleCtx {
            types: &types,
            all_func_sigs: &all_func_sigs,
            num_imported,
            num_memories: memories.len(),
            globals: &globals,
        };
        let (params, lifted_body) = lift_function(&ctx, sig, body)?;
        funcs.push(FuncDef {
            id: FuncId(def_idx as u32),
            name,
            export_name,
            params,
            results: sig.results.clone(),
            body: lifted_body,
        });
    }

    Ok(Module {
        memories,
        globals,
        host_contracts,
        funcs,
        memory_exports,
        global_exports,
    })
}

fn convert_val_type(ty: WValType) -> Result<ValType, WasmError> {
    match ty {
        WValType::I32 => Ok(ValType::I32),
        WValType::I64 => Ok(ValType::I64),
        WValType::F32 => Ok(ValType::F32),
        WValType::F64 => Ok(ValType::F64),
        WValType::V128 => Ok(ValType::V128),
        other => Err(WasmError::UnsupportedFeature(format!(
            "unsupported value type: {other:?}"
        ))),
    }
}

fn try_convert_func_type(ft: &FuncType) -> Result<FuncSig, WasmError> {
    let params = ft
        .params()
        .iter()
        .copied()
        .map(convert_val_type)
        .collect::<Result<Vec<_>, _>>()?;
    let results = ft
        .results()
        .iter()
        .copied()
        .map(convert_val_type)
        .collect::<Result<Vec<_>, _>>()?;
    Ok(FuncSig { params, results })
}

fn eval_const_expr(expr: &ConstExpr<'_>, globals: &[GlobalDef]) -> Result<Val, WasmError> {
    let mut stack: Vec<Val> = Vec::new();
    let mut reader = expr.get_operators_reader();
    while !reader.eof() {
        let op = reader
            .read()
            .map_err(|e| WasmError::ParseError(e.to_string()))?;
        match op {
            Operator::I32Const { value } => stack.push(Val::I32(value)),
            Operator::I64Const { value } => stack.push(Val::I64(value)),
            Operator::F32Const { value } => stack.push(Val::F32(value.bits())),
            Operator::F64Const { value } => stack.push(Val::F64(value.bits())),
            Operator::V128Const { value } => stack.push(Val::V128(value.i128() as u128)),
            Operator::GlobalGet { global_index } => {
                let g = globals.get(global_index as usize).ok_or_else(|| {
                    WasmError::ValidationError(format!(
                        "const expr references unknown global {global_index}"
                    ))
                })?;
                if g.mutable {
                    return Err(WasmError::ValidationError(
                        "const expr cannot reference mutable global".into(),
                    ));
                }
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
                    "unsupported const expr operator: {other:?}"
                )));
            }
        }
    }
    if stack.len() != 1 {
        return Err(WasmError::ValidationError(
            "const expr did not produce a single value".into(),
        ));
    }
    Ok(stack[0])
}

struct LiftModuleCtx<'a> {
    types: &'a [Option<FuncSig>],
    all_func_sigs: &'a [FuncSig],
    num_imported: usize,
    num_memories: usize,
    globals: &'a [GlobalDef],
}

impl<'a> LiftModuleCtx<'a> {
    fn block_sig(&self, bt: BlockType) -> Result<(Vec<ValType>, Vec<ValType>), WasmError> {
        match bt {
            BlockType::Empty => Ok((Vec::new(), Vec::new())),
            BlockType::Type(wt) => Ok((Vec::new(), vec![convert_val_type(wt)?])),
            BlockType::FuncType(idx) => {
                let sig = self
                    .types
                    .get(idx as usize)
                    .and_then(|o| o.as_ref())
                    .ok_or_else(|| {
                        WasmError::UnsupportedFeature(format!(
                            "block uses unsupported type index {idx}"
                        ))
                    })?;
                Ok((sig.params.clone(), sig.results.clone()))
            }
        }
    }

    fn check_memarg(&self, memarg: MemArg) -> Result<(MemId, u32), WasmError> {
        if memarg.ordering.is_some() {
            return Err(WasmError::UnsupportedFeature(
                "atomic memory ordering is not supported".into(),
            ));
        }
        let mem_idx = match memarg.target {
            MemArgTarget::Memory(idx) => idx,
            MemArgTarget::Array(_) => {
                return Err(WasmError::UnsupportedFeature(
                    "GC array memory operations are not supported".into(),
                ));
            }
        };
        if (mem_idx as usize) >= self.num_memories {
            return Err(WasmError::ValidationError(format!(
                "memory index {mem_idx} out of range"
            )));
        }
        let mem_id = u16::try_from(mem_idx)
            .map(MemId)
            .map_err(|_| WasmError::UnsupportedFeature("memory index exceeds u16".into()))?;
        let offset = u32::try_from(memarg.offset).map_err(|_| {
            WasmError::UnsupportedFeature("memory offset exceeds u32 (wasm64)".into())
        })?;
        Ok((mem_id, offset))
    }

    fn check_mem_idx(&self, mem_idx: u32) -> Result<MemId, WasmError> {
        if (mem_idx as usize) >= self.num_memories {
            return Err(WasmError::ValidationError(format!(
                "memory index {mem_idx} out of range"
            )));
        }
        u16::try_from(mem_idx)
            .map(MemId)
            .map_err(|_| WasmError::UnsupportedFeature("memory index exceeds u16".into()))
    }
}

/// Pre-scans all nested structured blocks in `body` to collect the sorted list of
/// Wasm local indices that may be written (`local.set`/`local.tee`) inside each frame.
/// Index 0 is the function root frame (always empty `mut_locals`), and `1..` follow
/// preorder traversal of `Block`, `Loop`, `If`.
fn prescan_mut_locals(body: &FunctionBody<'_>) -> Result<Vec<Vec<u32>>, WasmError> {
    let mut result: Vec<Vec<u32>> = vec![Vec::new()];
    let mut stack: Vec<(usize, BTreeSet<u32>)> = vec![(0, BTreeSet::new())];
    let mut ops = body
        .get_operators_reader()
        .map_err(|e| WasmError::ParseError(e.to_string()))?;

    while !ops.eof() {
        let op = ops
            .read()
            .map_err(|e| WasmError::ParseError(e.to_string()))?;
        match op {
            Operator::Block { .. } | Operator::Loop { .. } | Operator::If { .. } => {
                let fid = result.len();
                result.push(Vec::new());
                stack.push((fid, BTreeSet::new()));
            }
            Operator::LocalSet { local_index } | Operator::LocalTee { local_index } => {
                if stack.len() > 1
                    && let Some((_, set)) = stack.last_mut()
                {
                    set.insert(local_index);
                }
            }
            Operator::End => {
                if stack.len() > 1 {
                    let (fid, set) = stack.pop().expect("non-empty stack");
                    result[fid] = set.iter().copied().collect();
                    if stack.len() > 1
                        && let Some((_, parent_set)) = stack.last_mut()
                    {
                        parent_set.extend(set);
                    }
                } else {
                    break;
                }
            }
            _ => {}
        }
    }
    Ok(result)
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum FrameKind {
    Func,
    Block,
    Loop,
    If,
}

struct ControlFrame {
    kind: FrameKind,
    params: Vec<ValType>,
    results: Vec<ValType>,
    mut_locals: Vec<u32>,
    stmts: Vec<Stmt>,
    stack: Vec<(ValId, ValType)>,
    local_env: Vec<ValId>,
    entry_reachable: bool,
    reachable: bool,
    // `If` fields:
    entry_params: Vec<(ValId, ValType)>,
    entry_locals: Vec<ValId>,
    seen_else: bool,
    then_stmts: Vec<Stmt>,
    if_cond: Option<ValId>,
    // `Loop` fields:
    loop_init_vars: Vec<ValId>,
    loop_state_vars: Vec<(ValId, ValType)>,
}

impl ControlFrame {
    fn label_arity(&self) -> usize {
        match self.kind {
            FrameKind::Loop => self.params.len(),
            FrameKind::Func | FrameKind::Block | FrameKind::If => self.results.len(),
        }
    }

    fn mut_local_vals(&self, current_locals: &[ValId]) -> Vec<ValId> {
        self.mut_locals.iter().map(|&l| current_locals[l as usize]).collect()
    }
}

struct ValAlloc(u32);
impl ValAlloc {
    fn fresh(&mut self) -> ValId {
        let id = ValId(self.0);
        self.0 += 1;
        id
    }
}

fn lift_function(
    ctx: &LiftModuleCtx<'_>,
    sig: &FuncSig,
    body: &FunctionBody<'_>,
) -> Result<(Vec<(ValId, ValType)>, Region), WasmError> {
    let mut alloc = ValAlloc(0);
    let mut local_types: Vec<ValType> = sig.params.clone();
    let mut init_stmts: Vec<Stmt> = Vec::new();

    let func_params: Vec<(ValId, ValType)> = sig
        .params
        .iter()
        .map(|&ty| (alloc.fresh(), ty))
        .collect();
    let mut init_local_env: Vec<ValId> = func_params.iter().map(|&(id, _)| id).collect();

    let mut locals_reader = body
        .get_locals_reader()
        .map_err(|e| WasmError::ParseError(e.to_string()))?;
    let mut zero_i32: Option<ValId> = None;
    let mut zero_i64: Option<ValId> = None;
    let mut zero_f32: Option<ValId> = None;
    let mut zero_f64: Option<ValId> = None;
    let mut zero_v128: Option<ValId> = None;
    for _ in 0..locals_reader.get_count() {
        let (count, wty) = locals_reader
            .read()
            .map_err(|e| WasmError::ParseError(e.to_string()))?;
        let ty = convert_val_type(wty)?;
        let z = match ty {
            ValType::I32 => *zero_i32.get_or_insert_with(|| {
                let id = alloc.fresh();
                init_stmts.push(Stmt::Let {
                    dst: id,
                    ty: ValType::I32,
                    op: Op::ConstI32(0),
                });
                id
            }),
            ValType::I64 => *zero_i64.get_or_insert_with(|| {
                let id = alloc.fresh();
                init_stmts.push(Stmt::Let {
                    dst: id,
                    ty: ValType::I64,
                    op: Op::ConstI64(0),
                });
                id
            }),
            ValType::F32 => *zero_f32.get_or_insert_with(|| {
                let id = alloc.fresh();
                init_stmts.push(Stmt::Let {
                    dst: id,
                    ty: ValType::F32,
                    op: Op::ConstF32(0),
                });
                id
            }),
            ValType::F64 => *zero_f64.get_or_insert_with(|| {
                let id = alloc.fresh();
                init_stmts.push(Stmt::Let {
                    dst: id,
                    ty: ValType::F64,
                    op: Op::ConstF64(0),
                });
                id
            }),
            ValType::V128 => *zero_v128.get_or_insert_with(|| {
                let id = alloc.fresh();
                init_stmts.push(Stmt::Let {
                    dst: id,
                    ty: ValType::V128,
                    op: Op::ConstV128(0),
                });
                id
            }),
        };
        for _ in 0..count {
            local_types.push(ty);
            init_local_env.push(z);
        }
    }

    let mut_locals_table = prescan_mut_locals(body)?;
    let mut next_frame_id = 1usize;
    let mut rb = RegionBuilder::new();

    let mut frames: Vec<ControlFrame> = vec![ControlFrame {
        kind: FrameKind::Func,
        params: Vec::new(),
        results: sig.results.clone(),
        mut_locals: Vec::new(),
        stmts: init_stmts,
        stack: Vec::new(),
        local_env: init_local_env,
        entry_reachable: true,
        reachable: true,
        entry_params: Vec::new(),
        entry_locals: Vec::new(),
        seen_else: false,
        then_stmts: Vec::new(),
        if_cond: None,
        loop_init_vars: Vec::new(),
        loop_state_vars: Vec::new(),
    }];

    let pop_val = |frame: &mut ControlFrame| -> Result<(ValId, ValType), WasmError> {
        frame.stack.pop().ok_or_else(|| {
            WasmError::ValidationError("operand stack underflow during lifting".into())
        })
    };

    let pop_n = |frame: &mut ControlFrame, n: usize| -> Result<Vec<(ValId, ValType)>, WasmError> {
        if frame.stack.len() < n {
            return Err(WasmError::ValidationError(
                "operand stack underflow popping block/call args".into(),
            ));
        }
        let split = frame.stack.len() - n;
        Ok(frame.stack.split_off(split))
    };

    let peek_n = |frame: &ControlFrame, n: usize| -> Result<Vec<ValId>, WasmError> {
        if frame.stack.len() < n {
            return Err(WasmError::ValidationError(
                "operand stack underflow peeking branch args".into(),
            ));
        }
        Ok(frame.stack[frame.stack.len() - n..]
            .iter()
            .map(|&(id, _)| id)
            .collect())
    };

    let mut ops = body
        .get_operators_reader()
        .map_err(|e| WasmError::ParseError(e.to_string()))?;

    while !ops.eof() {
        let op = ops
            .read()
            .map_err(|e| WasmError::ParseError(e.to_string()))?;

        // Track dead code nesting cleanly without emitting IR statements.
        let top_reachable = frames.last().expect("at least root frame").reachable;
        if !top_reachable
            && !matches!(
                op,
                Operator::Block { .. }
                    | Operator::Loop { .. }
                    | Operator::If { .. }
                    | Operator::Else
                    | Operator::End
            )
        {
            // Validate instruction is in supported deterministic subset even in dead code.
            check_supported_op(ctx, &op)?;
            continue;
        }

        match op {
            Operator::Block { blockty } => {
                let fid = next_frame_id;
                next_frame_id += 1;
                let (params, results) = ctx.block_sig(blockty)?;
                let mut_locals = mut_locals_table[fid].clone();
                let parent = frames.last_mut().unwrap();
                let entry_reachable = parent.reachable;
                let entry_params = if entry_reachable {
                    pop_n(parent, params.len())?
                } else {
                    Vec::new()
                };
                let entry_locals = parent.local_env.clone();
                frames.push(ControlFrame {
                    kind: FrameKind::Block,
                    params,
                    results,
                    mut_locals,
                    stmts: Vec::new(),
                    stack: entry_params,
                    local_env: entry_locals,
                    entry_reachable,
                    reachable: entry_reachable,
                    entry_params: Vec::new(),
                    entry_locals: Vec::new(),
                    seen_else: false,
                    then_stmts: Vec::new(),
                    if_cond: None,
                    loop_init_vars: Vec::new(),
                    loop_state_vars: Vec::new(),
                });
            }
            Operator::Loop { blockty } => {
                let fid = next_frame_id;
                next_frame_id += 1;
                let (params, results) = ctx.block_sig(blockty)?;
                let mut_locals = mut_locals_table[fid].clone();
                let parent = frames.last_mut().unwrap();
                let entry_reachable = parent.reachable;
                let (init_vars, state_vars, loop_stack, loop_locals) = if entry_reachable {
                    let arg_vals = pop_n(parent, params.len())?;
                    let mut init_vars: Vec<ValId> = arg_vals.iter().map(|&(id, _)| id).collect();
                    let mut state_vars: Vec<(ValId, ValType)> =
                        Vec::with_capacity(params.len() + mut_locals.len());
                    let mut loop_stack = Vec::with_capacity(params.len());
                    for &ty in &params {
                        let sid = alloc.fresh();
                        state_vars.push((sid, ty));
                        loop_stack.push((sid, ty));
                    }
                    let mut loop_locals = parent.local_env.clone();
                    for &loc in &mut_locals {
                        init_vars.push(parent.local_env[loc as usize]);
                        let sid = alloc.fresh();
                        let lty = local_types[loc as usize];
                        state_vars.push((sid, lty));
                        loop_locals[loc as usize] = sid;
                    }
                    (init_vars, state_vars, loop_stack, loop_locals)
                } else {
                    (Vec::new(), Vec::new(), Vec::new(), parent.local_env.clone())
                };
                frames.push(ControlFrame {
                    kind: FrameKind::Loop,
                    params,
                    results,
                    mut_locals,
                    stmts: Vec::new(),
                    stack: loop_stack,
                    local_env: loop_locals,
                    entry_reachable,
                    reachable: entry_reachable,
                    entry_params: Vec::new(),
                    entry_locals: Vec::new(),
                    seen_else: false,
                    then_stmts: Vec::new(),
                    if_cond: None,
                    loop_init_vars: init_vars,
                    loop_state_vars: state_vars,
                });
            }
            Operator::If { blockty } => {
                let fid = next_frame_id;
                next_frame_id += 1;
                let (params, results) = ctx.block_sig(blockty)?;
                let mut_locals = mut_locals_table[fid].clone();
                let parent = frames.last_mut().unwrap();
                let entry_reachable = parent.reachable;
                let (cond_id, entry_params) = if entry_reachable {
                    let (c, _) = pop_val(parent)?;
                    let p = pop_n(parent, params.len())?;
                    (Some(c), p)
                } else {
                    (None, Vec::new())
                };
                let entry_locals = parent.local_env.clone();
                frames.push(ControlFrame {
                    kind: FrameKind::If,
                    params,
                    results,
                    mut_locals,
                    stmts: Vec::new(),
                    stack: entry_params.clone(),
                    local_env: entry_locals.clone(),
                    entry_reachable,
                    reachable: entry_reachable,
                    entry_params,
                    entry_locals,
                    seen_else: false,
                    then_stmts: Vec::new(),
                    if_cond: cond_id,
                    loop_init_vars: Vec::new(),
                    loop_state_vars: Vec::new(),
                });
            }
            Operator::Else => {
                let f = frames.last_mut().unwrap();
                if f.kind != FrameKind::If {
                    return Err(WasmError::ValidationError("unexpected else".into()));
                }
                if f.reachable {
                    let res_len = f.results.len();
                    let mut yielded: Vec<ValId> = pop_n(f, res_len)?
                        .into_iter()
                        .map(|(id, _)| id)
                        .collect();
                    yielded.extend(f.mut_local_vals(&f.local_env));
                    if !yielded.is_empty() {
                        let span = rb.alloc_vals(&yielded);
                        f.stmts.push(Stmt::Yield(span));
                    }
                }
                f.then_stmts = std::mem::take(&mut f.stmts);
                f.stack = f.entry_params.clone();
                f.local_env = f.entry_locals.clone();
                f.reachable = f.entry_reachable;
                f.seen_else = true;
            }
            Operator::End => {
                if frames.len() == 1 {
                    let root = frames.pop().unwrap();
                    let mut stmts = root.stmts;
                    if root.reachable {
                        let ret_len = root.results.len();
                        let split = root.stack.len().saturating_sub(ret_len);
                        let ret_vals: Vec<ValId> =
                            root.stack[split..].iter().map(|&(id, _)| id).collect();
                        if !ret_vals.is_empty() {
                            let span = rb.alloc_vals(&ret_vals);
                            stmts.push(Stmt::Yield(span));
                        }
                    }
                    let root_span = rb.alloc_stmts(&stmts);
                    return Ok((func_params, rb.finish_node(RegionNode::Block(root_span))));
                }

                let mut f = frames.pop().unwrap();
                if f.reachable {
                    let res_len = f.results.len();
                    let mut yielded: Vec<ValId> = pop_n(&mut f, res_len)?
                        .into_iter()
                        .map(|(id, _)| id)
                        .collect();
                    yielded.extend(f.mut_local_vals(&f.local_env));
                    if !yielded.is_empty() {
                        let span = rb.alloc_vals(&yielded);
                        f.stmts.push(Stmt::Yield(span));
                    }
                }

                if !f.entry_reachable {
                    continue;
                }

                let mut region_results: Vec<(ValId, ValType)> =
                    Vec::with_capacity(f.results.len() + f.mut_locals.len());
                for &ty in &f.results {
                    region_results.push((alloc.fresh(), ty));
                }
                for &loc in &f.mut_locals {
                    region_results.push((alloc.fresh(), local_types[loc as usize]));
                }

                let sub_id = match f.kind {
                    FrameKind::Block => rb.alloc_block(&f.stmts),
                    FrameKind::Loop => {
                        let inits = rb.alloc_vals(&f.loop_init_vars);
                        let states = rb.alloc_vars(&f.loop_state_vars);
                        let body_id = rb.alloc_block(&f.stmts);
                        rb.alloc_node(RegionNode::BoundedLoop {
                            max_iters: u32::MAX,
                            init_vars: inits,
                            state_vars: states,
                            body: body_id,
                        })
                    }
                    FrameKind::If => {
                        let cond = f.if_cond.expect("reachable if has cond");
                        let (then_stmts, else_stmts) = if f.seen_else {
                            (f.then_stmts, f.stmts)
                        } else {
                            let mut implicit_else_vals: Vec<ValId> =
                                f.entry_params.iter().map(|&(id, _)| id).collect();
                            implicit_else_vals.extend(f.mut_local_vals(&f.entry_locals));
                            let else_stmts = if implicit_else_vals.is_empty() {
                                Vec::new()
                            } else {
                                let span = rb.alloc_vals(&implicit_else_vals);
                                vec![Stmt::Yield(span)]
                            };
                            (f.stmts, else_stmts)
                        };
                        let res_tys: Vec<ValType> =
                            region_results.iter().map(|&(_, ty)| ty).collect();
                        let then_id = rb.alloc_block(&then_stmts);
                        let else_id = rb.alloc_block(&else_stmts);
                        let res_span = rb.alloc_tys(&res_tys);
                        rb.alloc_node(RegionNode::IfElse {
                            cond,
                            then_region: then_id,
                            else_region: else_id,
                            results: res_span,
                        })
                    }
                    FrameKind::Func => unreachable!(),
                };

                let parent = frames.last_mut().unwrap();
                for &(id, ty) in &region_results[..f.results.len()] {
                    parent.stack.push((id, ty));
                }
                for (&loc, &(id, _)) in f
                    .mut_locals
                    .iter()
                    .zip(&region_results[f.results.len()..])
                {
                    parent.local_env[loc as usize] = id;
                }
                let res_span = rb.alloc_vars(&region_results);
                parent.stmts.push(Stmt::Region {
                    results: res_span,
                    region: sub_id,
                });
            }
            Operator::Br { relative_depth } => {
                let d = relative_depth as usize;
                let target_idx = frames.len() - 1 - d;
                let arity = frames[target_idx].label_arity();
                let is_loop = frames[target_idx].kind == FrameKind::Loop;
                let mut_locs = frames[target_idx].mut_locals.clone();

                let cur = frames.last_mut().unwrap();
                let mut vals: Vec<ValId> =
                    pop_n(cur, arity)?.into_iter().map(|(id, _)| id).collect();
                for loc in mut_locs {
                    vals.push(cur.local_env[loc as usize]);
                }
                let vs = rb.alloc_vals(&vals);
                cur.stmts.push(if is_loop {
                    Stmt::Continue {
                        depth: relative_depth,
                        cond: None,
                        values: vs,
                    }
                } else {
                    Stmt::Break {
                        depth: relative_depth,
                        cond: None,
                        values: vs,
                    }
                });
                cur.reachable = false;
                cur.stack.clear();
            }
            Operator::BrIf { relative_depth } => {
                let d = relative_depth as usize;
                let target_idx = frames.len() - 1 - d;
                let arity = frames[target_idx].label_arity();
                let is_loop = frames[target_idx].kind == FrameKind::Loop;
                let mut_locs = frames[target_idx].mut_locals.clone();

                let cur = frames.last_mut().unwrap();
                let (cond, _) = pop_val(cur)?;
                let mut vals = peek_n(cur, arity)?;
                for loc in mut_locs {
                    vals.push(cur.local_env[loc as usize]);
                }
                let vs = rb.alloc_vals(&vals);
                cur.stmts.push(if is_loop {
                    Stmt::Continue {
                        depth: relative_depth,
                        cond: Some(cond),
                        values: vs,
                    }
                } else {
                    Stmt::Break {
                        depth: relative_depth,
                        cond: Some(cond),
                        values: vs,
                    }
                });
            }
            Operator::BrTable { targets } => {
                let default_depth = targets.default();
                let default_idx = frames.len() - 1 - (default_depth as usize);
                let arity = frames[default_idx].label_arity();
                let table_depths: Vec<u32> = targets
                    .targets()
                    .collect::<Result<Vec<_>, _>>()
                    .map_err(|e| WasmError::ParseError(e.to_string()))?;

                let cur = frames.last_mut().unwrap();
                let (idx_val, _) = pop_val(cur)?;
                let label_vals: Vec<ValId> =
                    pop_n(cur, arity)?.into_iter().map(|(id, _)| id).collect();
                let cur_locals = cur.local_env.clone();

                let mut arm_stmts = Vec::new();
                for (arm_i, d) in table_depths.into_iter().enumerate() {
                    if d == default_depth {
                        continue;
                    }
                    let tidx = frames.len() - 1 - (d as usize);
                    let tframe = &frames[tidx];
                    let mut vals = label_vals.clone();
                    vals.extend(tframe.mut_local_vals(&cur_locals));
                    let vs = rb.alloc_vals(&vals);
                    let c_const = alloc.fresh();
                    let cond_id = alloc.fresh();
                    arm_stmts.push(Stmt::Let {
                        dst: c_const,
                        ty: ValType::I32,
                        op: Op::ConstI32(arm_i as i32),
                    });
                    arm_stmts.push(Stmt::Let {
                        dst: cond_id,
                        ty: ValType::I32,
                        op: Op::Bin(BinOp::I32Eq, idx_val, c_const),
                    });
                    arm_stmts.push(if tframe.kind == FrameKind::Loop {
                        Stmt::Continue {
                            depth: d,
                            cond: Some(cond_id),
                            values: vs,
                        }
                    } else {
                        Stmt::Break {
                            depth: d,
                            cond: Some(cond_id),
                            values: vs,
                        }
                    });
                }
                let def_frame = &frames[default_idx];
                let mut def_vals = label_vals;
                def_vals.extend(def_frame.mut_local_vals(&cur_locals));
                let def_vs = rb.alloc_vals(&def_vals);
                arm_stmts.push(if def_frame.kind == FrameKind::Loop {
                    Stmt::Continue {
                        depth: default_depth,
                        cond: None,
                        values: def_vs,
                    }
                } else {
                    Stmt::Break {
                        depth: default_depth,
                        cond: None,
                        values: def_vs,
                    }
                });

                let cur = frames.last_mut().unwrap();
                cur.stmts.extend(arm_stmts);
                cur.reachable = false;
                cur.stack.clear();
            }
            Operator::Return => {
                let ret_len = sig.results.len();
                let cur = frames.last_mut().unwrap();
                let ret_vals: Vec<ValId> = pop_n(cur, ret_len)?
                    .into_iter()
                    .map(|(id, _)| id)
                    .collect();
                let vs = rb.alloc_vals(&ret_vals);
                cur.stmts.push(Stmt::Return(vs));
                cur.reachable = false;
                cur.stack.clear();
            }
            Operator::Unreachable => {
                let cur = frames.last_mut().unwrap();
                cur.stmts
                    .push(Stmt::Effect(EffectOp::Trap(TrapCode::Unreachable)));
                cur.reachable = false;
                cur.stack.clear();
            }
            Operator::Nop => {
                frames.last_mut().unwrap().stmts.push(Stmt::Effect(EffectOp::Nop));
            }
            Operator::Drop => {
                pop_val(frames.last_mut().unwrap())?;
            }
            Operator::Select => {
                let cur = frames.last_mut().unwrap();
                let (cond, _) = pop_val(cur)?;
                let (false_val, ty) = pop_val(cur)?;
                let (true_val, _) = pop_val(cur)?;
                let dst = alloc.fresh();
                cur.stmts.push(Stmt::Let {
                    dst,
                    ty,
                    op: Op::Select {
                        cond,
                        true_val,
                        false_val,
                    },
                });
                cur.stack.push((dst, ty));
            }
            Operator::TypedSelect { ty } => {
                let ty = convert_val_type(ty)?;
                let cur = frames.last_mut().unwrap();
                let (cond, _) = pop_val(cur)?;
                let (false_val, _) = pop_val(cur)?;
                let (true_val, _) = pop_val(cur)?;
                let dst = alloc.fresh();
                cur.stmts.push(Stmt::Let {
                    dst,
                    ty,
                    op: Op::Select {
                        cond,
                        true_val,
                        false_val,
                    },
                });
                cur.stack.push((dst, ty));
            }
            Operator::LocalGet { local_index } => {
                let cur = frames.last_mut().unwrap();
                let id = cur.local_env[local_index as usize];
                let ty = local_types[local_index as usize];
                cur.stack.push((id, ty));
            }
            Operator::LocalSet { local_index } => {
                let cur = frames.last_mut().unwrap();
                let (id, _) = pop_val(cur)?;
                cur.local_env[local_index as usize] = id;
            }
            Operator::LocalTee { local_index } => {
                let cur = frames.last_mut().unwrap();
                let &(id, _) = cur.stack.last().ok_or_else(|| {
                    WasmError::ValidationError("stack underflow on local.tee".into())
                })?;
                cur.local_env[local_index as usize] = id;
            }
            Operator::GlobalGet { global_index } => {
                let ty = ctx
                    .globals
                    .get(global_index as usize)
                    .ok_or_else(|| WasmError::ValidationError("invalid global index".into()))?
                    .ty;
                let dst = alloc.fresh();
                let cur = frames.last_mut().unwrap();
                cur.stmts.push(Stmt::Let {
                    dst,
                    ty,
                    op: Op::GlobalGet(GlobalId(global_index)),
                });
                cur.stack.push((dst, ty));
            }
            Operator::GlobalSet { global_index } => {
                let cur = frames.last_mut().unwrap();
                let (val, _) = pop_val(cur)?;
                cur.stmts.push(Stmt::Effect(EffectOp::GlobalSet {
                    id: GlobalId(global_index),
                    val,
                }));
            }
            Operator::Call { function_index } => {
                let callee_sig = ctx
                    .all_func_sigs
                    .get(function_index as usize)
                    .ok_or_else(|| WasmError::ValidationError("invalid call index".into()))?;
                let cur = frames.last_mut().unwrap();
                let args: Vec<ValId> = pop_n(cur, callee_sig.params.len())?
                    .into_iter()
                    .map(|(id, _)| id)
                    .collect();
                let results: Vec<(ValId, ValType)> = callee_sig
                    .results
                    .iter()
                    .map(|&ty| (alloc.fresh(), ty))
                    .collect();
                let target = if (function_index as usize) < ctx.num_imported {
                    CallTarget::Host(HostCallId(function_index))
                } else {
                    CallTarget::Func(FuncId((function_index as usize - ctx.num_imported) as u32))
                };
                for &(id, ty) in &results {
                    cur.stack.push((id, ty));
                }
                let res_span = rb.alloc_vars(&results);
                let arg_span = rb.alloc_vals(&args);
                cur.stmts.push(Stmt::Call {
                    results: res_span,
                    target,
                    args: arg_span,
                });
            }
            Operator::I32Const { value } => {
                let dst = alloc.fresh();
                let cur = frames.last_mut().unwrap();
                cur.stmts.push(Stmt::Let {
                    dst,
                    ty: ValType::I32,
                    op: Op::ConstI32(value),
                });
                cur.stack.push((dst, ValType::I32));
            }
            Operator::I64Const { value } => {
                let dst = alloc.fresh();
                let cur = frames.last_mut().unwrap();
                cur.stmts.push(Stmt::Let {
                    dst,
                    ty: ValType::I64,
                    op: Op::ConstI64(value),
                });
                cur.stack.push((dst, ValType::I64));
            }
            Operator::F32Const { value } => {
                let dst = alloc.fresh();
                let cur = frames.last_mut().unwrap();
                cur.stmts.push(Stmt::Let {
                    dst,
                    ty: ValType::F32,
                    op: Op::ConstF32(value.bits()),
                });
                cur.stack.push((dst, ValType::F32));
            }
            Operator::F64Const { value } => {
                let dst = alloc.fresh();
                let cur = frames.last_mut().unwrap();
                cur.stmts.push(Stmt::Let {
                    dst,
                    ty: ValType::F64,
                    op: Op::ConstF64(value.bits()),
                });
                cur.stack.push((dst, ValType::F64));
            }
            Operator::V128Const { value } => {
                let dst = alloc.fresh();
                let cur = frames.last_mut().unwrap();
                cur.stmts.push(Stmt::Let {
                    dst,
                    ty: ValType::V128,
                    op: Op::ConstV128(value.i128() as u128),
                });
                cur.stack.push((dst, ValType::V128));
            }
            Operator::MemorySize { mem } => {
                let mem_id = ctx.check_mem_idx(mem)?;
                let dst = alloc.fresh();
                let cur = frames.last_mut().unwrap();
                cur.stmts.push(Stmt::Let {
                    dst,
                    ty: ValType::I32,
                    op: Op::MemorySize(mem_id),
                });
                cur.stack.push((dst, ValType::I32));
            }
            Operator::MemoryGrow { mem } => {
                let mem_id = ctx.check_mem_idx(mem)?;
                let cur = frames.last_mut().unwrap();
                let (delta, _) = pop_val(cur)?;
                let dst = alloc.fresh();
                cur.stmts.push(Stmt::Let {
                    dst,
                    ty: ValType::I32,
                    op: Op::MemoryGrow { mem: mem_id, delta },
                });
                cur.stack.push((dst, ValType::I32));
            }
            Operator::MemoryCopy { dst_mem, src_mem } => {
                let dst_mem = ctx.check_mem_idx(dst_mem)?;
                let src_mem = ctx.check_mem_idx(src_mem)?;
                let cur = frames.last_mut().unwrap();
                let (len, _) = pop_val(cur)?;
                let (src, _) = pop_val(cur)?;
                let (dst, _) = pop_val(cur)?;
                cur.stmts.push(Stmt::Effect(EffectOp::MemoryCopy {
                    dst_mem,
                    src_mem,
                    dst,
                    src,
                    len,
                }));
            }
            Operator::MemoryFill { mem } => {
                let mem = ctx.check_mem_idx(mem)?;
                let cur = frames.last_mut().unwrap();
                let (len, _) = pop_val(cur)?;
                let (val, _) = pop_val(cur)?;
                let (dst, _) = pop_val(cur)?;
                cur.stmts.push(Stmt::Effect(EffectOp::MemoryFill {
                    mem,
                    dst,
                    val,
                    len,
                }));
            }
            // Loads
            Operator::I32Load { memarg } => {
                emit_load(ctx, &mut alloc, frames.last_mut().unwrap(), memarg, MemWidth::B4, false, ValType::I32)?;
            }
            Operator::I64Load { memarg } => {
                emit_load(ctx, &mut alloc, frames.last_mut().unwrap(), memarg, MemWidth::B8, false, ValType::I64)?;
            }
            Operator::I32Load8S { memarg } => {
                emit_load(ctx, &mut alloc, frames.last_mut().unwrap(), memarg, MemWidth::B1, true, ValType::I32)?;
            }
            Operator::I32Load8U { memarg } => {
                emit_load(ctx, &mut alloc, frames.last_mut().unwrap(), memarg, MemWidth::B1, false, ValType::I32)?;
            }
            Operator::I32Load16S { memarg } => {
                emit_load(ctx, &mut alloc, frames.last_mut().unwrap(), memarg, MemWidth::B2, true, ValType::I32)?;
            }
            Operator::I32Load16U { memarg } => {
                emit_load(ctx, &mut alloc, frames.last_mut().unwrap(), memarg, MemWidth::B2, false, ValType::I32)?;
            }
            Operator::I64Load8S { memarg } => {
                emit_load(ctx, &mut alloc, frames.last_mut().unwrap(), memarg, MemWidth::B1, true, ValType::I64)?;
            }
            Operator::I64Load8U { memarg } => {
                emit_load(ctx, &mut alloc, frames.last_mut().unwrap(), memarg, MemWidth::B1, false, ValType::I64)?;
            }
            Operator::I64Load16S { memarg } => {
                emit_load(ctx, &mut alloc, frames.last_mut().unwrap(), memarg, MemWidth::B2, true, ValType::I64)?;
            }
            Operator::I64Load16U { memarg } => {
                emit_load(ctx, &mut alloc, frames.last_mut().unwrap(), memarg, MemWidth::B2, false, ValType::I64)?;
            }
            Operator::I64Load32S { memarg } => {
                emit_load(ctx, &mut alloc, frames.last_mut().unwrap(), memarg, MemWidth::B4, true, ValType::I64)?;
            }
            Operator::I64Load32U { memarg } => {
                emit_load(ctx, &mut alloc, frames.last_mut().unwrap(), memarg, MemWidth::B4, false, ValType::I64)?;
            }
            Operator::F32Load { memarg } => {
                emit_load(ctx, &mut alloc, frames.last_mut().unwrap(), memarg, MemWidth::B4, false, ValType::F32)?;
            }
            Operator::F64Load { memarg } => {
                emit_load(ctx, &mut alloc, frames.last_mut().unwrap(), memarg, MemWidth::B8, false, ValType::F64)?;
            }
            Operator::V128Load { memarg } => {
                emit_load(ctx, &mut alloc, frames.last_mut().unwrap(), memarg, MemWidth::B16, false, ValType::V128)?;
            }
            // Stores
            Operator::I32Store { memarg } | Operator::F32Store { memarg } => {
                emit_store(ctx, frames.last_mut().unwrap(), memarg, MemWidth::B4)?;
            }
            Operator::I64Store { memarg } | Operator::F64Store { memarg } => {
                emit_store(ctx, frames.last_mut().unwrap(), memarg, MemWidth::B8)?;
            }
            Operator::V128Store { memarg } => {
                emit_store(ctx, frames.last_mut().unwrap(), memarg, MemWidth::B16)?;
            }
            Operator::I32Store8 { memarg } | Operator::I64Store8 { memarg } => {
                emit_store(ctx, frames.last_mut().unwrap(), memarg, MemWidth::B1)?;
            }
            Operator::I32Store16 { memarg } | Operator::I64Store16 { memarg } => {
                emit_store(ctx, frames.last_mut().unwrap(), memarg, MemWidth::B2)?;
            }
            Operator::I64Store32 { memarg } => {
                emit_store(ctx, frames.last_mut().unwrap(), memarg, MemWidth::B4)?;
            }
            // SIMD lane extract / replace / bitselect / shuffle
            Operator::I8x16ExtractLaneS { lane } => {
                emit_simd_extract(&mut alloc, frames.last_mut().unwrap(), LaneKind::I8x16S, lane)?;
            }
            Operator::I8x16ExtractLaneU { lane } => {
                emit_simd_extract(&mut alloc, frames.last_mut().unwrap(), LaneKind::I8x16U, lane)?;
            }
            Operator::I16x8ExtractLaneS { lane } => {
                emit_simd_extract(&mut alloc, frames.last_mut().unwrap(), LaneKind::I16x8S, lane)?;
            }
            Operator::I16x8ExtractLaneU { lane } => {
                emit_simd_extract(&mut alloc, frames.last_mut().unwrap(), LaneKind::I16x8U, lane)?;
            }
            Operator::I32x4ExtractLane { lane } => {
                emit_simd_extract(&mut alloc, frames.last_mut().unwrap(), LaneKind::I32x4, lane)?;
            }
            Operator::I64x2ExtractLane { lane } => {
                emit_simd_extract(&mut alloc, frames.last_mut().unwrap(), LaneKind::I64x2, lane)?;
            }
            Operator::F32x4ExtractLane { lane } => {
                emit_simd_extract(&mut alloc, frames.last_mut().unwrap(), LaneKind::F32x4, lane)?;
            }
            Operator::F64x2ExtractLane { lane } => {
                emit_simd_extract(&mut alloc, frames.last_mut().unwrap(), LaneKind::F64x2, lane)?;
            }
            Operator::I8x16ReplaceLane { lane } => {
                emit_simd_replace(&mut alloc, frames.last_mut().unwrap(), LaneKind::I8x16U, lane)?;
            }
            Operator::I16x8ReplaceLane { lane } => {
                emit_simd_replace(&mut alloc, frames.last_mut().unwrap(), LaneKind::I16x8U, lane)?;
            }
            Operator::I32x4ReplaceLane { lane } => {
                emit_simd_replace(&mut alloc, frames.last_mut().unwrap(), LaneKind::I32x4, lane)?;
            }
            Operator::I64x2ReplaceLane { lane } => {
                emit_simd_replace(&mut alloc, frames.last_mut().unwrap(), LaneKind::I64x2, lane)?;
            }
            Operator::F32x4ReplaceLane { lane } => {
                emit_simd_replace(&mut alloc, frames.last_mut().unwrap(), LaneKind::F32x4, lane)?;
            }
            Operator::F64x2ReplaceLane { lane } => {
                emit_simd_replace(&mut alloc, frames.last_mut().unwrap(), LaneKind::F64x2, lane)?;
            }
            Operator::V128Bitselect => {
                let cur = frames.last_mut().unwrap();
                let (mask, _) = pop_val(cur)?;
                let (b, _) = pop_val(cur)?;
                let (a, _) = pop_val(cur)?;
                let dst = alloc.fresh();
                cur.stmts.push(Stmt::Let {
                    dst,
                    ty: ValType::V128,
                    op: Op::SimdBitselect { a, b, mask },
                });
                cur.stack.push((dst, ValType::V128));
            }
            Operator::I8x16Shuffle { lanes } => {
                let cur = frames.last_mut().unwrap();
                let (rhs, _) = pop_val(cur)?;
                let (lhs, _) = pop_val(cur)?;
                let dst = alloc.fresh();
                cur.stmts.push(Stmt::Let {
                    dst,
                    ty: ValType::V128,
                    op: Op::SimdShuffle { lhs, rhs, lanes },
                });
                cur.stack.push((dst, ValType::V128));
            }
            other => {
                if let Some(unop) = map_unop(&other) {
                    let cur = frames.last_mut().unwrap();
                    let (a, _) = pop_val(cur)?;
                    let dst = alloc.fresh();
                    let ty = unop.output_ty();
                    cur.stmts.push(Stmt::Let {
                        dst,
                        ty,
                        op: Op::Un(unop, a),
                    });
                    cur.stack.push((dst, ty));
                } else if let Some(binop) = map_binop(&other) {
                    let cur = frames.last_mut().unwrap();
                    let (r, _) = pop_val(cur)?;
                    let (l, _) = pop_val(cur)?;
                    let dst = alloc.fresh();
                    let ty = binop.output_ty();
                    cur.stmts.push(Stmt::Let {
                        dst,
                        ty,
                        op: Op::Bin(binop, l, r),
                    });
                    cur.stack.push((dst, ty));
                } else {
                    return Err(WasmError::UnsupportedFeature(format!(
                        "unsupported Wasm instruction: {other:?}"
                    )));
                }
            }
        }
    }

    Err(WasmError::ValidationError(
        "function body ended without closing End".into(),
    ))
}

fn emit_load(
    ctx: &LiftModuleCtx<'_>,
    alloc: &mut ValAlloc,
    cur: &mut ControlFrame,
    memarg: MemArg,
    width: MemWidth,
    signed: bool,
    result_ty: ValType,
) -> Result<(), WasmError> {
    let (mem, offset) = ctx.check_memarg(memarg)?;
    let addr = cur
        .stack
        .pop()
        .ok_or_else(|| WasmError::ValidationError("stack underflow on load".into()))?
        .0;
    let dst = alloc.fresh();
    cur.stmts.push(Stmt::Let {
        dst,
        ty: result_ty,
        op: Op::Load {
            mem,
            addr,
            offset,
            width,
            signed,
            result_ty,
        },
    });
    cur.stack.push((dst, result_ty));
    Ok(())
}

fn emit_store(
    ctx: &LiftModuleCtx<'_>,
    cur: &mut ControlFrame,
    memarg: MemArg,
    width: MemWidth,
) -> Result<(), WasmError> {
    let (mem, offset) = ctx.check_memarg(memarg)?;
    let val = cur
        .stack
        .pop()
        .ok_or_else(|| WasmError::ValidationError("stack underflow on store val".into()))?
        .0;
    let addr = cur
        .stack
        .pop()
        .ok_or_else(|| WasmError::ValidationError("stack underflow on store addr".into()))?
        .0;
    cur.stmts.push(Stmt::Effect(EffectOp::Store {
        mem,
        addr,
        offset,
        width,
        val,
    }));
    Ok(())
}

fn emit_simd_extract(
    alloc: &mut ValAlloc,
    cur: &mut ControlFrame,
    kind: LaneKind,
    lane: u8,
) -> Result<(), WasmError> {
    if lane >= kind.num_lanes() {
        return Err(WasmError::ValidationError(format!(
            "SIMD extract lane {lane} out of range for {kind:?}"
        )));
    }
    let vec = cur
        .stack
        .pop()
        .ok_or_else(|| WasmError::ValidationError("stack underflow on SIMD extract_lane".into()))?
        .0;
    let dst = alloc.fresh();
    let ty = kind.scalar_ty();
    cur.stmts.push(Stmt::Let {
        dst,
        ty,
        op: Op::SimdExtractLane { kind, lane, vec },
    });
    cur.stack.push((dst, ty));
    Ok(())
}

fn emit_simd_replace(
    alloc: &mut ValAlloc,
    cur: &mut ControlFrame,
    kind: LaneKind,
    lane: u8,
) -> Result<(), WasmError> {
    if lane >= kind.num_lanes() {
        return Err(WasmError::ValidationError(format!(
            "SIMD replace lane {lane} out of range for {kind:?}"
        )));
    }
    let val = cur
        .stack
        .pop()
        .ok_or_else(|| WasmError::ValidationError("stack underflow on SIMD replace_lane val".into()))?
        .0;
    let vec = cur
        .stack
        .pop()
        .ok_or_else(|| WasmError::ValidationError("stack underflow on SIMD replace_lane vec".into()))?
        .0;
    let dst = alloc.fresh();
    cur.stmts.push(Stmt::Let {
        dst,
        ty: ValType::V128,
        op: Op::SimdReplaceLane { kind, lane, vec, val },
    });
    cur.stack.push((dst, ValType::V128));
    Ok(())
}

fn map_unop(op: &Operator<'_>) -> Option<UnOp> {
    Some(match op {
        // Integer unary (0..=15)
        Operator::I32Eqz => UnOp::I32Eqz,
        Operator::I64Eqz => UnOp::I64Eqz,
        Operator::I32Clz => UnOp::I32Clz,
        Operator::I32Ctz => UnOp::I32Ctz,
        Operator::I32Popcnt => UnOp::I32Popcnt,
        Operator::I64Clz => UnOp::I64Clz,
        Operator::I64Ctz => UnOp::I64Ctz,
        Operator::I64Popcnt => UnOp::I64Popcnt,
        Operator::I32WrapI64 => UnOp::I32WrapI64,
        Operator::I64ExtendI32S => UnOp::I64ExtendI32S,
        Operator::I64ExtendI32U => UnOp::I64ExtendI32U,
        Operator::I32Extend8S => UnOp::I32Extend8S,
        Operator::I32Extend16S => UnOp::I32Extend16S,
        Operator::I64Extend8S => UnOp::I64Extend8S,
        Operator::I64Extend16S => UnOp::I64Extend16S,
        Operator::I64Extend32S => UnOp::I64Extend32S,
        // Scalar FP unary (16..=29)
        Operator::F32Abs => UnOp::F32Abs,
        Operator::F32Neg => UnOp::F32Neg,
        Operator::F32Ceil => UnOp::F32Ceil,
        Operator::F32Floor => UnOp::F32Floor,
        Operator::F32Trunc => UnOp::F32Trunc,
        Operator::F32Nearest => UnOp::F32Nearest,
        Operator::F32Sqrt => UnOp::F32Sqrt,
        Operator::F64Abs => UnOp::F64Abs,
        Operator::F64Neg => UnOp::F64Neg,
        Operator::F64Ceil => UnOp::F64Ceil,
        Operator::F64Floor => UnOp::F64Floor,
        Operator::F64Trunc => UnOp::F64Trunc,
        Operator::F64Nearest => UnOp::F64Nearest,
        Operator::F64Sqrt => UnOp::F64Sqrt,
        // Trapping float-to-int truncations (30..=37)
        Operator::I32TruncF32S => UnOp::I32TruncF32S,
        Operator::I32TruncF32U => UnOp::I32TruncF32U,
        Operator::I32TruncF64S => UnOp::I32TruncF64S,
        Operator::I32TruncF64U => UnOp::I32TruncF64U,
        Operator::I64TruncF32S => UnOp::I64TruncF32S,
        Operator::I64TruncF32U => UnOp::I64TruncF32U,
        Operator::I64TruncF64S => UnOp::I64TruncF64S,
        Operator::I64TruncF64U => UnOp::I64TruncF64U,
        // Saturating float-to-int truncations (38..=45)
        Operator::I32TruncSatF32S => UnOp::I32TruncSatF32S,
        Operator::I32TruncSatF32U => UnOp::I32TruncSatF32U,
        Operator::I32TruncSatF64S => UnOp::I32TruncSatF64S,
        Operator::I32TruncSatF64U => UnOp::I32TruncSatF64U,
        Operator::I64TruncSatF32S => UnOp::I64TruncSatF32S,
        Operator::I64TruncSatF32U => UnOp::I64TruncSatF32U,
        Operator::I64TruncSatF64S => UnOp::I64TruncSatF64S,
        Operator::I64TruncSatF64U => UnOp::I64TruncSatF64U,
        // Int-to-float conversions (46..=53)
        Operator::F32ConvertI32S => UnOp::F32ConvertI32S,
        Operator::F32ConvertI32U => UnOp::F32ConvertI32U,
        Operator::F32ConvertI64S => UnOp::F32ConvertI64S,
        Operator::F32ConvertI64U => UnOp::F32ConvertI64U,
        Operator::F64ConvertI32S => UnOp::F64ConvertI32S,
        Operator::F64ConvertI32U => UnOp::F64ConvertI32U,
        Operator::F64ConvertI64S => UnOp::F64ConvertI64S,
        Operator::F64ConvertI64U => UnOp::F64ConvertI64U,
        // Demote / Promote / Reinterpret (54..=59)
        Operator::F32DemoteF64 => UnOp::F32DemoteF64,
        Operator::F64PromoteF32 => UnOp::F64PromoteF32,
        Operator::I32ReinterpretF32 => UnOp::I32ReinterpretF32,
        Operator::I64ReinterpretF64 => UnOp::I64ReinterpretF64,
        Operator::F32ReinterpretI32 => UnOp::F32ReinterpretI32,
        Operator::F64ReinterpretI64 => UnOp::F64ReinterpretI64,
        // v128 unary / splat / bitmask / lane-convert / extend (60..=99)
        Operator::V128Not => UnOp::V128Not,
        Operator::V128AnyTrue => UnOp::V128AnyTrue,
        Operator::I8x16Splat => UnOp::I8x16Splat,
        Operator::I16x8Splat => UnOp::I16x8Splat,
        Operator::I32x4Splat => UnOp::I32x4Splat,
        Operator::I64x2Splat => UnOp::I64x2Splat,
        Operator::F32x4Splat => UnOp::F32x4Splat,
        Operator::F64x2Splat => UnOp::F64x2Splat,
        Operator::I8x16Bitmask => UnOp::I8x16Bitmask,
        Operator::I16x8Bitmask => UnOp::I16x8Bitmask,
        Operator::I32x4Bitmask => UnOp::I32x4Bitmask,
        Operator::I64x2Bitmask => UnOp::I64x2Bitmask,
        Operator::I32x4AllTrue => UnOp::I32x4AllTrue,
        Operator::I64x2AllTrue => UnOp::I64x2AllTrue,
        Operator::I32x4Abs => UnOp::I32x4Abs,
        Operator::I32x4Neg => UnOp::I32x4Neg,
        Operator::I64x2Abs => UnOp::I64x2Abs,
        Operator::I64x2Neg => UnOp::I64x2Neg,
        Operator::F32x4Abs => UnOp::F32x4Abs,
        Operator::F32x4Neg => UnOp::F32x4Neg,
        Operator::F32x4Sqrt => UnOp::F32x4Sqrt,
        Operator::F32x4Ceil => UnOp::F32x4Ceil,
        Operator::F32x4Floor => UnOp::F32x4Floor,
        Operator::F32x4Trunc => UnOp::F32x4Trunc,
        Operator::F32x4Nearest => UnOp::F32x4Nearest,
        Operator::F64x2Abs => UnOp::F64x2Abs,
        Operator::F64x2Neg => UnOp::F64x2Neg,
        Operator::F64x2Sqrt => UnOp::F64x2Sqrt,
        Operator::F64x2Ceil => UnOp::F64x2Ceil,
        Operator::F64x2Floor => UnOp::F64x2Floor,
        Operator::F64x2Trunc => UnOp::F64x2Trunc,
        Operator::F64x2Nearest => UnOp::F64x2Nearest,
        Operator::I32x4TruncSatF32x4S => UnOp::I32x4TruncSatF32x4S,
        Operator::I32x4TruncSatF32x4U => UnOp::I32x4TruncSatF32x4U,
        Operator::F32x4ConvertI32x4S => UnOp::F32x4ConvertI32x4S,
        Operator::F32x4ConvertI32x4U => UnOp::F32x4ConvertI32x4U,
        Operator::I64x2ExtendLowI32x4S => UnOp::I64x2ExtendLowI32x4S,
        Operator::I64x2ExtendLowI32x4U => UnOp::I64x2ExtendLowI32x4U,
        Operator::I64x2ExtendHighI32x4S => UnOp::I64x2ExtendHighI32x4S,
        Operator::I64x2ExtendHighI32x4U => UnOp::I64x2ExtendHighI32x4U,
        _ => return None,
    })
}

fn map_binop(op: &Operator<'_>) -> Option<BinOp> {
    Some(match op {
        // Integer binary (0..=49)
        Operator::I32Eq => BinOp::I32Eq,
        Operator::I32Ne => BinOp::I32Ne,
        Operator::I32LtS => BinOp::I32LtS,
        Operator::I32LtU => BinOp::I32LtU,
        Operator::I32GtS => BinOp::I32GtS,
        Operator::I32GtU => BinOp::I32GtU,
        Operator::I32LeS => BinOp::I32LeS,
        Operator::I32LeU => BinOp::I32LeU,
        Operator::I32GeS => BinOp::I32GeS,
        Operator::I32GeU => BinOp::I32GeU,
        Operator::I64Eq => BinOp::I64Eq,
        Operator::I64Ne => BinOp::I64Ne,
        Operator::I64LtS => BinOp::I64LtS,
        Operator::I64LtU => BinOp::I64LtU,
        Operator::I64GtS => BinOp::I64GtS,
        Operator::I64GtU => BinOp::I64GtU,
        Operator::I64LeS => BinOp::I64LeS,
        Operator::I64LeU => BinOp::I64LeU,
        Operator::I64GeS => BinOp::I64GeS,
        Operator::I64GeU => BinOp::I64GeU,
        Operator::I32Add => BinOp::I32Add,
        Operator::I32Sub => BinOp::I32Sub,
        Operator::I32Mul => BinOp::I32Mul,
        Operator::I32DivS => BinOp::I32DivS,
        Operator::I32DivU => BinOp::I32DivU,
        Operator::I32RemS => BinOp::I32RemS,
        Operator::I32RemU => BinOp::I32RemU,
        Operator::I64Add => BinOp::I64Add,
        Operator::I64Sub => BinOp::I64Sub,
        Operator::I64Mul => BinOp::I64Mul,
        Operator::I64DivS => BinOp::I64DivS,
        Operator::I64DivU => BinOp::I64DivU,
        Operator::I64RemS => BinOp::I64RemS,
        Operator::I64RemU => BinOp::I64RemU,
        Operator::I32And => BinOp::I32And,
        Operator::I32Or => BinOp::I32Or,
        Operator::I32Xor => BinOp::I32Xor,
        Operator::I32Shl => BinOp::I32Shl,
        Operator::I32ShrS => BinOp::I32ShrS,
        Operator::I32ShrU => BinOp::I32ShrU,
        Operator::I32Rotl => BinOp::I32Rotl,
        Operator::I32Rotr => BinOp::I32Rotr,
        Operator::I64And => BinOp::I64And,
        Operator::I64Or => BinOp::I64Or,
        Operator::I64Xor => BinOp::I64Xor,
        Operator::I64Shl => BinOp::I64Shl,
        Operator::I64ShrS => BinOp::I64ShrS,
        Operator::I64ShrU => BinOp::I64ShrU,
        Operator::I64Rotl => BinOp::I64Rotl,
        Operator::I64Rotr => BinOp::I64Rotr,
        // Scalar FP binary (50..=75)
        Operator::F32Add => BinOp::F32Add,
        Operator::F32Sub => BinOp::F32Sub,
        Operator::F32Mul => BinOp::F32Mul,
        Operator::F32Div => BinOp::F32Div,
        Operator::F32Min => BinOp::F32Min,
        Operator::F32Max => BinOp::F32Max,
        Operator::F32Copysign => BinOp::F32Copysign,
        Operator::F32Eq => BinOp::F32Eq,
        Operator::F32Ne => BinOp::F32Ne,
        Operator::F32Lt => BinOp::F32Lt,
        Operator::F32Gt => BinOp::F32Gt,
        Operator::F32Le => BinOp::F32Le,
        Operator::F32Ge => BinOp::F32Ge,
        Operator::F64Add => BinOp::F64Add,
        Operator::F64Sub => BinOp::F64Sub,
        Operator::F64Mul => BinOp::F64Mul,
        Operator::F64Div => BinOp::F64Div,
        Operator::F64Min => BinOp::F64Min,
        Operator::F64Max => BinOp::F64Max,
        Operator::F64Copysign => BinOp::F64Copysign,
        Operator::F64Eq => BinOp::F64Eq,
        Operator::F64Ne => BinOp::F64Ne,
        Operator::F64Lt => BinOp::F64Lt,
        Operator::F64Gt => BinOp::F64Gt,
        Operator::F64Le => BinOp::F64Le,
        Operator::F64Ge => BinOp::F64Ge,
        // v128 bitwise & swizzle (76..=80)
        Operator::V128And => BinOp::V128And,
        Operator::V128AndNot => BinOp::V128AndNot,
        Operator::V128Or => BinOp::V128Or,
        Operator::V128Xor => BinOp::V128Xor,
        Operator::I8x16Swizzle => BinOp::I8x16Swizzle,
        // i32x4 lane binary (81..=100)
        Operator::I32x4Add => BinOp::I32x4Add,
        Operator::I32x4Sub => BinOp::I32x4Sub,
        Operator::I32x4Mul => BinOp::I32x4Mul,
        Operator::I32x4MinS => BinOp::I32x4MinS,
        Operator::I32x4MinU => BinOp::I32x4MinU,
        Operator::I32x4MaxS => BinOp::I32x4MaxS,
        Operator::I32x4MaxU => BinOp::I32x4MaxU,
        Operator::I32x4Eq => BinOp::I32x4Eq,
        Operator::I32x4Ne => BinOp::I32x4Ne,
        Operator::I32x4LtS => BinOp::I32x4LtS,
        Operator::I32x4LtU => BinOp::I32x4LtU,
        Operator::I32x4GtS => BinOp::I32x4GtS,
        Operator::I32x4GtU => BinOp::I32x4GtU,
        Operator::I32x4LeS => BinOp::I32x4LeS,
        Operator::I32x4LeU => BinOp::I32x4LeU,
        Operator::I32x4GeS => BinOp::I32x4GeS,
        Operator::I32x4GeU => BinOp::I32x4GeU,
        Operator::I32x4Shl => BinOp::I32x4Shl,
        Operator::I32x4ShrS => BinOp::I32x4ShrS,
        Operator::I32x4ShrU => BinOp::I32x4ShrU,
        // i64x2 lane binary (101..=112)
        Operator::I64x2Add => BinOp::I64x2Add,
        Operator::I64x2Sub => BinOp::I64x2Sub,
        Operator::I64x2Mul => BinOp::I64x2Mul,
        Operator::I64x2Eq => BinOp::I64x2Eq,
        Operator::I64x2Ne => BinOp::I64x2Ne,
        Operator::I64x2LtS => BinOp::I64x2LtS,
        Operator::I64x2GtS => BinOp::I64x2GtS,
        Operator::I64x2LeS => BinOp::I64x2LeS,
        Operator::I64x2GeS => BinOp::I64x2GeS,
        Operator::I64x2Shl => BinOp::I64x2Shl,
        Operator::I64x2ShrS => BinOp::I64x2ShrS,
        Operator::I64x2ShrU => BinOp::I64x2ShrU,
        // f32x4 lane binary (113..=126)
        Operator::F32x4Add => BinOp::F32x4Add,
        Operator::F32x4Sub => BinOp::F32x4Sub,
        Operator::F32x4Mul => BinOp::F32x4Mul,
        Operator::F32x4Div => BinOp::F32x4Div,
        Operator::F32x4Min => BinOp::F32x4Min,
        Operator::F32x4Max => BinOp::F32x4Max,
        Operator::F32x4PMin => BinOp::F32x4PMin,
        Operator::F32x4PMax => BinOp::F32x4PMax,
        Operator::F32x4Eq => BinOp::F32x4Eq,
        Operator::F32x4Ne => BinOp::F32x4Ne,
        Operator::F32x4Lt => BinOp::F32x4Lt,
        Operator::F32x4Gt => BinOp::F32x4Gt,
        Operator::F32x4Le => BinOp::F32x4Le,
        Operator::F32x4Ge => BinOp::F32x4Ge,
        // f64x2 lane binary (127..=140)
        Operator::F64x2Add => BinOp::F64x2Add,
        Operator::F64x2Sub => BinOp::F64x2Sub,
        Operator::F64x2Mul => BinOp::F64x2Mul,
        Operator::F64x2Div => BinOp::F64x2Div,
        Operator::F64x2Min => BinOp::F64x2Min,
        Operator::F64x2Max => BinOp::F64x2Max,
        Operator::F64x2PMin => BinOp::F64x2PMin,
        Operator::F64x2PMax => BinOp::F64x2PMax,
        Operator::F64x2Eq => BinOp::F64x2Eq,
        Operator::F64x2Ne => BinOp::F64x2Ne,
        Operator::F64x2Lt => BinOp::F64x2Lt,
        Operator::F64x2Gt => BinOp::F64x2Gt,
        Operator::F64x2Le => BinOp::F64x2Le,
        Operator::F64x2Ge => BinOp::F64x2Ge,
        _ => return None,
    })
}

fn check_supported_op(ctx: &LiftModuleCtx<'_>, op: &Operator<'_>) -> Result<(), WasmError> {
    if map_unop(op).is_some() || map_binop(op).is_some() {
        return Ok(());
    }
    match op {
        Operator::Unreachable
        | Operator::Nop
        | Operator::Br { .. }
        | Operator::BrIf { .. }
        | Operator::BrTable { .. }
        | Operator::Return
        | Operator::Call { .. }
        | Operator::Drop
        | Operator::Select
        | Operator::LocalGet { .. }
        | Operator::LocalSet { .. }
        | Operator::LocalTee { .. }
        | Operator::GlobalGet { .. }
        | Operator::GlobalSet { .. }
        | Operator::I32Const { .. }
        | Operator::I64Const { .. }
        | Operator::F32Const { .. }
        | Operator::F64Const { .. }
        | Operator::V128Const { .. }
        | Operator::I8x16ExtractLaneS { .. }
        | Operator::I8x16ExtractLaneU { .. }
        | Operator::I16x8ExtractLaneS { .. }
        | Operator::I16x8ExtractLaneU { .. }
        | Operator::I32x4ExtractLane { .. }
        | Operator::I64x2ExtractLane { .. }
        | Operator::F32x4ExtractLane { .. }
        | Operator::F64x2ExtractLane { .. }
        | Operator::I8x16ReplaceLane { .. }
        | Operator::I16x8ReplaceLane { .. }
        | Operator::I32x4ReplaceLane { .. }
        | Operator::I64x2ReplaceLane { .. }
        | Operator::F32x4ReplaceLane { .. }
        | Operator::F64x2ReplaceLane { .. }
        | Operator::V128Bitselect
        | Operator::I8x16Shuffle { .. } => Ok(()),
        Operator::TypedSelect { ty } => {
            convert_val_type(*ty)?;
            Ok(())
        }
        Operator::MemorySize { mem }
        | Operator::MemoryGrow { mem }
        | Operator::MemoryFill { mem } => {
            ctx.check_mem_idx(*mem)?;
            Ok(())
        }
        Operator::MemoryCopy { dst_mem, src_mem } => {
            ctx.check_mem_idx(*dst_mem)?;
            ctx.check_mem_idx(*src_mem)?;
            Ok(())
        }
        Operator::I32Load { memarg }
        | Operator::I64Load { memarg }
        | Operator::F32Load { memarg }
        | Operator::F64Load { memarg }
        | Operator::V128Load { memarg }
        | Operator::I32Load8S { memarg }
        | Operator::I32Load8U { memarg }
        | Operator::I32Load16S { memarg }
        | Operator::I32Load16U { memarg }
        | Operator::I64Load8S { memarg }
        | Operator::I64Load8U { memarg }
        | Operator::I64Load16S { memarg }
        | Operator::I64Load16U { memarg }
        | Operator::I64Load32S { memarg }
        | Operator::I64Load32U { memarg }
        | Operator::I32Store { memarg }
        | Operator::I64Store { memarg }
        | Operator::F32Store { memarg }
        | Operator::F64Store { memarg }
        | Operator::V128Store { memarg }
        | Operator::I32Store8 { memarg }
        | Operator::I32Store16 { memarg }
        | Operator::I64Store8 { memarg }
        | Operator::I64Store16 { memarg }
        | Operator::I64Store32 { memarg } => {
            ctx.check_memarg(*memarg)?;
            Ok(())
        }
        other => Err(WasmError::UnsupportedFeature(format!(
            "unsupported Wasm instruction: {other:?}"
        ))),
    }
}
