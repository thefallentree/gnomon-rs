//! Lossless deterministic `wasm32` -> `GnomonIR` lifter powered by `wasmparser`.

use std::collections::{BTreeSet, HashMap};

use gnomon_kernel::{
    BinOp, CallTarget, EffectOp, FuncDef, FuncId, GlobalDef, GlobalId, HostCallId, HostContract,
    MemId, MemWidth, MemoryDef, Module, Op, Region, Stmt, TrapCode, UnOp, Val, ValId, ValType,
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
                                Val::I64(_) => {
                                    return Err(WasmError::UnsupportedFeature(
                                        "64-bit data segment offset is not supported".into(),
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
                    "type index {type_idx} uses unsupported non-i32/i64 or non-function types"
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
            Region::Block(vec![
                Stmt::Let {
                    dst: ValId(0),
                    ty: ValType::I32,
                    op: Op::ConstI32(1),
                },
                Stmt::Yield(vec![ValId(0)]),
            ])
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
        };
        for _ in 0..count {
            local_types.push(ty);
            init_local_env.push(z);
        }
    }

    let mut_locals_table = prescan_mut_locals(body)?;
    let mut next_frame_id = 1usize;

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
                        f.stmts.push(Stmt::Yield(yielded));
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
                    if root.reachable {
                        let ret_len = root.results.len();
                        let split = root.stack.len().saturating_sub(ret_len);
                        let ret_vals: Vec<ValId> =
                            root.stack[split..].iter().map(|&(id, _)| id).collect();
                        let mut stmts = root.stmts;
                        if !ret_vals.is_empty() {
                            stmts.push(Stmt::Yield(ret_vals));
                        }
                        return Ok((func_params, Region::Block(stmts)));
                    }
                    return Ok((func_params, Region::Block(root.stmts)));
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
                        f.stmts.push(Stmt::Yield(yielded));
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

                let region = match f.kind {
                    FrameKind::Block => Region::Block(f.stmts),
                    FrameKind::Loop => Region::BoundedLoop {
                        max_iters: u32::MAX,
                        init_vars: f.loop_init_vars,
                        state_vars: f.loop_state_vars,
                        body: Box::new(Region::Block(f.stmts)),
                    },
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
                                vec![Stmt::Yield(implicit_else_vals)]
                            };
                            (f.stmts, else_stmts)
                        };
                        let res_tys: Vec<ValType> =
                            region_results.iter().map(|&(_, ty)| ty).collect();
                        Region::IfElse {
                            cond,
                            then_region: Box::new(Region::Block(then_stmts)),
                            else_region: Box::new(Region::Block(else_stmts)),
                            results: res_tys,
                        }
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
                parent.stmts.push(Stmt::Region {
                    results: region_results,
                    region,
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
                cur.stmts.push(if is_loop {
                    Stmt::Continue {
                        depth: relative_depth,
                        cond: None,
                        values: vals,
                    }
                } else {
                    Stmt::Break {
                        depth: relative_depth,
                        cond: None,
                        values: vals,
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
                cur.stmts.push(if is_loop {
                    Stmt::Continue {
                        depth: relative_depth,
                        cond: Some(cond),
                        values: vals,
                    }
                } else {
                    Stmt::Break {
                        depth: relative_depth,
                        cond: Some(cond),
                        values: vals,
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
                            values: vals,
                        }
                    } else {
                        Stmt::Break {
                            depth: d,
                            cond: Some(cond_id),
                            values: vals,
                        }
                    });
                }
                let def_frame = &frames[default_idx];
                let mut def_vals = label_vals;
                def_vals.extend(def_frame.mut_local_vals(&cur_locals));
                arm_stmts.push(if def_frame.kind == FrameKind::Loop {
                    Stmt::Continue {
                        depth: default_depth,
                        cond: None,
                        values: def_vals,
                    }
                } else {
                    Stmt::Break {
                        depth: default_depth,
                        cond: None,
                        values: def_vals,
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
                cur.stmts.push(Stmt::Return(ret_vals));
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
                cur.stmts.push(Stmt::Call {
                    results,
                    target,
                    args,
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
            // Stores
            Operator::I32Store { memarg } => {
                emit_store(ctx, frames.last_mut().unwrap(), memarg, MemWidth::B4)?;
            }
            Operator::I64Store { memarg } => {
                emit_store(ctx, frames.last_mut().unwrap(), memarg, MemWidth::B8)?;
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

fn map_unop(op: &Operator<'_>) -> Option<UnOp> {
    Some(match op {
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
        _ => return None,
    })
}

fn map_binop(op: &Operator<'_>) -> Option<BinOp> {
    Some(match op {
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
        | Operator::I64Const { .. } => Ok(()),
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
