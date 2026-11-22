//! Lossless `GnomonIR` -> `.wasm` emitter powered by `wasm-encoder`,
//! self-validated via `wasmparser::Validator`.

use std::collections::HashMap;

use gnomon_kernel::{
    BinOp, CallTarget, EffectOp, FuncDef, FuncId, GlobalId, HostCallId, MemId, MemWidth, Module,
    Op, Region, Stmt, UnOp, Val, ValId, ValType,
};
use wasm_encoder::{
    BlockType, CodeSection, ConstExpr, DataSection, EntityType, ExportKind, ExportSection,
    Function, FunctionSection, GlobalSection, GlobalType, ImportSection, InstructionSink, MemArg,
    MemArgTarget, MemorySection, MemoryType, Module as WasmModule, TypeSection, ValType as WValType,
};
use wasmparser::{Validator, WasmFeatures};

use crate::WasmError;

/// Lowers a `gnomon_kernel::Module` back to validated WebAssembly binary bytes.
pub fn emit_wasm(module: &Module) -> Result<Vec<u8>, WasmError> {
    let mut mem_map: HashMap<MemId, u32> = HashMap::new();
    for (idx, m) in module.memories.iter().enumerate() {
        let idx_u32 = u32::try_from(idx)
            .map_err(|_| WasmError::ValidationError("too many memories".into()))?;
        if mem_map.insert(m.id, idx_u32).is_some() {
            return Err(WasmError::ValidationError(format!(
                "duplicate MemId {:?}",
                m.id
            )));
        }
    }

    let mut global_map: HashMap<GlobalId, u32> = HashMap::new();
    for (idx, g) in module.globals.iter().enumerate() {
        let idx_u32 = u32::try_from(idx)
            .map_err(|_| WasmError::ValidationError("too many globals".into()))?;
        if global_map.insert(g.id, idx_u32).is_some() {
            return Err(WasmError::ValidationError(format!(
                "duplicate GlobalId {:?}",
                g.id
            )));
        }
    }

    let mut host_map: HashMap<HostCallId, u32> = HashMap::new();
    for (idx, hc) in module.host_contracts.iter().enumerate() {
        let idx_u32 = u32::try_from(idx)
            .map_err(|_| WasmError::ValidationError("too many host imports".into()))?;
        if host_map.insert(hc.id, idx_u32).is_some() {
            return Err(WasmError::ValidationError(format!(
                "duplicate HostCallId {:?}",
                hc.id
            )));
        }
    }

    let num_imported = module.host_contracts.len();
    let mut func_map: HashMap<FuncId, u32> = HashMap::new();
    for (idx, f) in module.funcs.iter().enumerate() {
        let wasm_idx = u32::try_from(num_imported + idx)
            .map_err(|_| WasmError::ValidationError("too many functions".into()))?;
        if func_map.insert(f.id, wasm_idx).is_some() {
            return Err(WasmError::ValidationError(format!(
                "duplicate FuncId {:?}",
                f.id
            )));
        }
    }

    let mut type_pool = TypePool::default();
    let mut host_type_idxs = Vec::with_capacity(module.host_contracts.len());
    for hc in &module.host_contracts {
        let p: Vec<ValType> = hc.params.iter().map(|&(_, ty)| ty).collect();
        let r: Vec<ValType> = hc.results.iter().map(|&(_, ty)| ty).collect();
        host_type_idxs.push(type_pool.intern(&p, &r));
    }

    let mut func_type_idxs = Vec::with_capacity(module.funcs.len());
    for f in &module.funcs {
        let p: Vec<ValType> = f.params.iter().map(|&(_, ty)| ty).collect();
        func_type_idxs.push(type_pool.intern(&p, &f.results));
    }

    let ctx = EmitCtx {
        mem_map: &mem_map,
        global_map: &global_map,
        host_map: &host_map,
        func_map: &func_map,
    };

    let mut encoded_funcs = Vec::with_capacity(module.funcs.len());
    for f in &module.funcs {
        encoded_funcs.push(emit_function(&ctx, &mut type_pool, f)?);
    }

    let mut wasm = WasmModule::new();
    if !type_pool.types.is_empty() {
        let mut ts = TypeSection::new();
        for (params, results) in &type_pool.types {
            let wp: Vec<WValType> = params.iter().copied().map(to_wval_type).collect();
            let wr: Vec<WValType> = results.iter().copied().map(to_wval_type).collect();
            ts.ty().function(wp, wr);
        }
        wasm.section(&ts);
    }

    if !module.host_contracts.is_empty() {
        let mut imports = ImportSection::new();
        for (hc, &type_idx) in module.host_contracts.iter().zip(&host_type_idxs) {
            imports.import(
                &hc.module_name,
                &hc.field_name,
                EntityType::Function(type_idx),
            );
        }
        wasm.section(&imports);
    }

    if !func_type_idxs.is_empty() {
        let mut funcs_sec = FunctionSection::new();
        for &type_idx in &func_type_idxs {
            funcs_sec.function(type_idx);
        }
        wasm.section(&funcs_sec);
    }

    if !module.memories.is_empty() {
        let mut mems_sec = MemorySection::new();
        for m in &module.memories {
            mems_sec.memory(MemoryType {
                minimum: u64::from(m.min_pages),
                maximum: m.max_pages.map(u64::from),
                memory64: false,
                shared: false,
                page_size_log2: None,
            });
        }
        wasm.section(&mems_sec);
    }

    if !module.globals.is_empty() {
        let mut globs_sec = GlobalSection::new();
        for g in &module.globals {
            let init = match g.init {
                Val::I32(v) => ConstExpr::i32_const(v),
                Val::I64(v) => ConstExpr::i64_const(v),
            };
            globs_sec.global(
                GlobalType {
                    val_type: to_wval_type(g.ty),
                    mutable: g.mutable,
                    shared: false,
                },
                &init,
            );
        }
        wasm.section(&globs_sec);
    }

    let mut exports = ExportSection::new();
    for f in &module.funcs {
        if let Some(name) = &f.export_name {
            let idx = func_map[&f.id];
            exports.export(name, ExportKind::Func, idx);
        }
    }
    for (name, mid) in &module.memory_exports {
        let idx = *mem_map.get(mid).ok_or_else(|| {
            WasmError::ValidationError(format!("memory export '{name}' references unknown {mid:?}"))
        })?;
        exports.export(name, ExportKind::Memory, idx);
    }
    for (name, gid) in &module.global_exports {
        let idx = *global_map.get(gid).ok_or_else(|| {
            WasmError::ValidationError(format!("global export '{name}' references unknown {gid:?}"))
        })?;
        exports.export(name, ExportKind::Global, idx);
    }
    if !exports.is_empty() {
        wasm.section(&exports);
    }

    if !encoded_funcs.is_empty() {
        let mut code_sec = CodeSection::new();
        for func in &encoded_funcs {
            code_sec.function(func);
        }
        wasm.section(&code_sec);
    }

    let mut data_sec = DataSection::new();
    for m in &module.memories {
        let mem_idx = mem_map[&m.id];
        for (offset, bytes) in &m.init_data {
            data_sec.active(
                mem_idx,
                &ConstExpr::i32_const(*offset as i32),
                bytes.iter().copied(),
            );
        }
    }
    if !data_sec.is_empty() {
        wasm.section(&data_sec);
    }

    let bytes = wasm.finish();

    let mut validator = Validator::new_with_features(WasmFeatures::default());
    validator
        .validate_all(&bytes)
        .map_err(|e| WasmError::ValidationError(format!("emitted wasm failed validation: {e}")))?;

    Ok(bytes)
}

#[derive(Default)]
struct TypePool {
    types: Vec<(Vec<ValType>, Vec<ValType>)>,
    map: HashMap<(Vec<ValType>, Vec<ValType>), u32>,
}

impl TypePool {
    fn intern(&mut self, params: &[ValType], results: &[ValType]) -> u32 {
        let key = (params.to_vec(), results.to_vec());
        if let Some(&idx) = self.map.get(&key) {
            return idx;
        }
        let idx = self.types.len() as u32;
        self.types.push(key.clone());
        self.map.insert(key, idx);
        idx
    }

    fn block_type(&mut self, results: &[ValType]) -> BlockType {
        match results {
            [] => BlockType::Empty,
            [ty] => BlockType::Result(to_wval_type(*ty)),
            many => BlockType::FunctionType(self.intern(&[], many)),
        }
    }
}

struct EmitCtx<'a> {
    mem_map: &'a HashMap<MemId, u32>,
    global_map: &'a HashMap<GlobalId, u32>,
    host_map: &'a HashMap<HostCallId, u32>,
    func_map: &'a HashMap<FuncId, u32>,
}

fn to_wval_type(ty: ValType) -> WValType {
    match ty {
        ValType::I32 => WValType::I32,
        ValType::I64 => WValType::I64,
    }
}

struct LocalEnv {
    next_local: u32,
    extra_locals: Vec<WValType>,
    bindings: HashMap<ValId, (u32, ValType)>,
}

impl LocalEnv {
    fn new(params: &[(ValId, ValType)]) -> Result<Self, WasmError> {
        let mut bindings = HashMap::new();
        for (idx, &(id, ty)) in params.iter().enumerate() {
            if bindings.insert(id, (idx as u32, ty)).is_some() {
                return Err(WasmError::ValidationError(format!(
                    "duplicate parameter ValId {id:?}"
                )));
            }
        }
        Ok(Self {
            next_local: params.len() as u32,
            extra_locals: Vec::new(),
            bindings,
        })
    }

    fn alloc_temp(&mut self, ty: ValType) -> u32 {
        let idx = self.next_local;
        self.next_local += 1;
        self.extra_locals.push(to_wval_type(ty));
        idx
    }

    fn bind(&mut self, id: ValId, ty: ValType) -> u32 {
        let idx = self.alloc_temp(ty);
        self.bindings.insert(id, (idx, ty));
        idx
    }

    fn get(&self, id: ValId) -> Result<(u32, ValType), WasmError> {
        self.bindings
            .get(&id)
            .copied()
            .ok_or_else(|| WasmError::ValidationError(format!("undefined ValId {id:?}")))
    }
}

enum EmitFrame {
    Block { ir_depth_cost: bool },
    LoopExit,
    LoopCont { state_locals: Vec<u32> },
}

enum Target<'a> {
    Block { wasm_depth: u32 },
    Loop { wasm_depth: u32, state_locals: &'a [u32] },
}

fn resolve_target<'a>(
    frames: &'a [EmitFrame],
    ir_depth: u32,
    is_continue: bool,
) -> Result<Target<'a>, WasmError> {
    let mut seen = 0u32;
    for idx in (0..frames.len()).rev() {
        match &frames[idx] {
            EmitFrame::Block { ir_depth_cost: false } => {}
            EmitFrame::Block { ir_depth_cost: true } => {
                if seen == ir_depth {
                    if is_continue {
                        return Err(WasmError::ValidationError(
                            "Continue targets a non-loop Block/If".into(),
                        ));
                    }
                    let wasm_depth = (frames.len() - 1 - idx) as u32;
                    return Ok(Target::Block { wasm_depth });
                }
                seen += 1;
            }
            EmitFrame::LoopCont { .. } => {}
            EmitFrame::LoopExit => {
                if seen == ir_depth {
                    if !is_continue {
                        let wasm_depth = (frames.len() - 1 - idx) as u32;
                        return Ok(Target::Block { wasm_depth });
                    }
                    let cont_idx = idx + 1;
                    let state_locals = match &frames[cont_idx] {
                        EmitFrame::LoopCont { state_locals } => state_locals.as_slice(),
                        _ => unreachable!("LoopExit is always paired with LoopCont above it"),
                    };
                    let wasm_depth = (frames.len() - 1 - cont_idx) as u32;
                    return Ok(Target::Loop {
                        wasm_depth,
                        state_locals,
                    });
                }
                seen += 1;
            }
        }
    }
    Err(WasmError::ValidationError(format!(
        "branch depth {ir_depth} exceeds active region stack"
    )))
}

fn emit_function(
    ctx: &EmitCtx<'_>,
    type_pool: &mut TypePool,
    f: &FuncDef,
) -> Result<Function, WasmError> {
    let mut locals = LocalEnv::new(&f.params)?;
    let mut inst_bytes = Vec::new();
    let mut frames = vec![EmitFrame::Block {
        ir_depth_cost: true,
    }];

    {
        let mut sink = InstructionSink::new(&mut inst_bytes);
        match &f.body {
            Region::Block(stmts) => {
                emit_block_stmts(ctx, type_pool, &mut locals, &mut frames, &mut sink, stmts)?;
            }
            other => {
                let mut root_frames = Vec::new();
                emit_region(
                    ctx,
                    type_pool,
                    &mut locals,
                    &mut root_frames,
                    &mut sink,
                    other,
                    &f.results,
                )?;
            }
        }
        sink.end();
    }

    let mut func = Function::new_with_locals_types(
        locals.extra_locals.iter().copied(),
    );
    func.raw(inst_bytes);
    Ok(func)
}

fn emit_region(
    ctx: &EmitCtx<'_>,
    type_pool: &mut TypePool,
    locals: &mut LocalEnv,
    frames: &mut Vec<EmitFrame>,
    sink: &mut InstructionSink<'_>,
    region: &Region,
    expected_results: &[ValType],
) -> Result<bool, WasmError> {
    match region {
        Region::Block(stmts) => {
            let bt = type_pool.block_type(expected_results);
            sink.block(bt);
            frames.push(EmitFrame::Block {
                ir_depth_cost: true,
            });
            let saved = locals.bindings.clone();
            let res = emit_block_stmts(ctx, type_pool, locals, frames, sink, stmts);
            locals.bindings = saved;
            let fell_through = res?;
            frames.pop();
            sink.end();
            Ok(fell_through)
        }
        Region::IfElse {
            cond,
            then_region,
            else_region,
            results,
        } => {
            let (cond_local, _) = locals.get(*cond)?;
            sink.local_get(cond_local);
            let bt = type_pool.block_type(results);
            sink.if_(bt);

            emit_if_branch(ctx, type_pool, locals, frames, sink, then_region, results)?;
            let skip_else = results.is_empty()
                && matches!(else_region.as_ref(), Region::Block(s) if s.is_empty());
            if !skip_else {
                sink.else_();
                emit_if_branch(ctx, type_pool, locals, frames, sink, else_region, results)?;
            }
            sink.end();
            Ok(true)
        }
        Region::BoundedLoop {
            max_iters,
            init_vars,
            state_vars,
            body,
        } => {
            if init_vars.len() != state_vars.len() {
                return Err(WasmError::ValidationError(
                    "BoundedLoop init_vars/state_vars length mismatch".into(),
                ));
            }
            for &iv in init_vars {
                let (l, _) = locals.get(iv)?;
                sink.local_get(l);
            }
            let saved_bindings = locals.bindings.clone();
            let mut state_locals = Vec::with_capacity(state_vars.len());
            for &(sv, ty) in state_vars {
                state_locals.push(locals.bind(sv, ty));
            }
            for &sl in state_locals.iter().rev() {
                sink.local_set(sl);
            }

            let rem_local = if *max_iters < u32::MAX {
                let rl = locals.alloc_temp(ValType::I32);
                sink.i32_const(*max_iters as i32);
                sink.local_set(rl);
                Some(rl)
            } else {
                None
            };

            let bt = type_pool.block_type(expected_results);
            sink.block(bt);
            sink.loop_(bt);

            if let Some(rl) = rem_local {
                sink.local_get(rl);
                sink.i32_eqz();
                sink.if_(BlockType::Empty);
                // Exhaust fuel cleanly so Wasmtime reports TrapCode::OutOfFuel, matching gnomon-kernel.
                sink.loop_(BlockType::Empty);
                sink.br(0);
                sink.end();
                sink.unreachable();
                sink.end();
                sink.local_get(rl);
                sink.i32_const(1);
                sink.i32_sub();
                sink.local_set(rl);
            }

            frames.push(EmitFrame::LoopExit);
            frames.push(EmitFrame::LoopCont { state_locals });

            let body_res = match body.as_ref() {
                Region::Block(stmts) => {
                    emit_block_stmts(ctx, type_pool, locals, frames, sink, stmts)
                }
                other => emit_region(
                    ctx,
                    type_pool,
                    locals,
                    frames,
                    sink,
                    other,
                    expected_results,
                ),
            };
            locals.bindings = saved_bindings;
            body_res?;

            frames.pop();
            frames.pop();
            sink.end();
            sink.end();
            Ok(true)
        }
        Region::InvariantLoop {
            init_vars,
            state_vars,
            cond,
            body,
            ..
        } => {
            if init_vars.len() != state_vars.len() {
                return Err(WasmError::ValidationError(
                    "InvariantLoop init_vars/state_vars length mismatch".into(),
                ));
            }
            for &iv in init_vars {
                let (l, _) = locals.get(iv)?;
                sink.local_get(l);
            }
            let saved_bindings = locals.bindings.clone();
            let mut state_locals = Vec::with_capacity(state_vars.len());
            for &(sv, ty) in state_vars {
                state_locals.push(locals.bind(sv, ty));
            }
            for &sl in state_locals.iter().rev() {
                sink.local_set(sl);
            }

            let state_tys: Vec<ValType> = state_vars.iter().map(|&(_, t)| t).collect();
            let bt = type_pool.block_type(&state_tys);
            sink.block(bt);
            sink.loop_(bt);

            // Evaluate loop condition region (returns single i32 on stack).
            let cond_res: Result<bool, WasmError> = match cond.as_ref() {
                Region::Block(stmts) => {
                    sink.block(BlockType::Result(WValType::I32));
                    frames.push(EmitFrame::Block {
                        ir_depth_cost: true,
                    });
                    let saved_cond = locals.bindings.clone();
                    let r = emit_block_stmts(ctx, type_pool, locals, frames, sink, stmts);
                    locals.bindings = saved_cond;
                    frames.pop();
                    sink.end();
                    r
                }
                other => emit_region(
                    ctx,
                    type_pool,
                    locals,
                    frames,
                    sink,
                    other,
                    &[ValType::I32],
                ),
            };
            if let Err(e) = cond_res {
                locals.bindings = saved_bindings;
                return Err(e);
            }

            sink.i32_eqz();
            sink.if_(BlockType::Empty);
            for &sl in &state_locals {
                sink.local_get(sl);
            }
            sink.br(2); // 0 = this if, 1 = $cont, 2 = $exit
            sink.end();

            frames.push(EmitFrame::LoopExit);
            frames.push(EmitFrame::LoopCont {
                state_locals: state_locals.clone(),
            });

            let body_res = match body.as_ref() {
                Region::Block(stmts) => {
                    let saved_body = locals.bindings.clone();
                    let r = emit_block_stmts(ctx, type_pool, locals, frames, sink, stmts);
                    locals.bindings = saved_body;
                    r
                }
                other => emit_region(ctx, type_pool, locals, frames, sink, other, &state_tys),
            };
            locals.bindings = saved_bindings;
            let body_fell = body_res?;
            if body_fell {
                for &sl in state_locals.iter().rev() {
                    sink.local_set(sl);
                }
                sink.br(0);
            }

            frames.pop();
            frames.pop();
            sink.end();
            sink.end();
            Ok(true)
        }
    }
}

fn emit_if_branch(
    ctx: &EmitCtx<'_>,
    type_pool: &mut TypePool,
    locals: &mut LocalEnv,
    frames: &mut Vec<EmitFrame>,
    sink: &mut InstructionSink<'_>,
    branch: &Region,
    expected_results: &[ValType],
) -> Result<(), WasmError> {
    let saved = locals.bindings.clone();
    let res = match branch {
        Region::Block(stmts) => {
            frames.push(EmitFrame::Block {
                ir_depth_cost: true,
            });
            let r = emit_block_stmts(ctx, type_pool, locals, frames, sink, stmts);
            frames.pop();
            r.map(|_| ())
        }
        other => {
            frames.push(EmitFrame::Block {
                ir_depth_cost: false,
            });
            let r = emit_region(
                ctx,
                type_pool,
                locals,
                frames,
                sink,
                other,
                expected_results,
            );
            frames.pop();
            r.map(|_| ())
        }
    };
    locals.bindings = saved;
    res
}

/// Emits statements in a `Region::Block`. Returns `true` if control could fall through
/// normally without hitting an unconditional terminator (`Yield`/`Break`/`Continue`/`Return`/`Trap`).
fn emit_block_stmts(
    ctx: &EmitCtx<'_>,
    type_pool: &mut TypePool,
    locals: &mut LocalEnv,
    frames: &mut Vec<EmitFrame>,
    sink: &mut InstructionSink<'_>,
    stmts: &[Stmt],
) -> Result<bool, WasmError> {
    for stmt in stmts {
        match stmt {
            Stmt::Let { dst, ty, op } => {
                emit_op(ctx, locals, sink, op)?;
                let l = locals.bind(*dst, *ty);
                sink.local_set(l);
            }
            Stmt::Effect(eff) => {
                let trapped = emit_effect(ctx, locals, sink, eff)?;
                if trapped {
                    return Ok(false);
                }
            }
            Stmt::Region { results, region } => {
                let res_tys: Vec<ValType> = results.iter().map(|&(_, ty)| ty).collect();
                emit_region(ctx, type_pool, locals, frames, sink, region, &res_tys)?;
                let mut res_locals = Vec::with_capacity(results.len());
                for &(id, ty) in results {
                    res_locals.push(locals.bind(id, ty));
                }
                for &rl in res_locals.iter().rev() {
                    sink.local_set(rl);
                }
            }
            Stmt::Call {
                results,
                target,
                args,
            } => {
                for &a in args {
                    let (l, _) = locals.get(a)?;
                    sink.local_get(l);
                }
                let func_idx = match target {
                    CallTarget::Func(fid) => *ctx.func_map.get(fid).ok_or_else(|| {
                        WasmError::ValidationError(format!("unknown FuncId {fid:?}"))
                    })?,
                    CallTarget::Host(hid) => *ctx.host_map.get(hid).ok_or_else(|| {
                        WasmError::ValidationError(format!("unknown HostCallId {hid:?}"))
                    })?,
                    CallTarget::Stratum(sid) => {
                        return Err(WasmError::UnsupportedFeature(format!(
                            "CallTarget::Stratum({sid:?}) must be lowered to Layer 0 before emit_wasm"
                        )));
                    }
                };
                sink.call(func_idx);
                let mut res_locals = Vec::with_capacity(results.len());
                for &(id, ty) in results {
                    res_locals.push(locals.bind(id, ty));
                }
                for &rl in res_locals.iter().rev() {
                    sink.local_set(rl);
                }
            }
            Stmt::Yield(vals) => {
                for &v in vals {
                    let (l, _) = locals.get(v)?;
                    sink.local_get(l);
                }
                return Ok(true);
            }
            Stmt::Return(vals) => {
                for &v in vals {
                    let (l, _) = locals.get(v)?;
                    sink.local_get(l);
                }
                sink.return_();
                return Ok(false);
            }
            Stmt::Break {
                depth,
                cond,
                values,
            } => {
                let target = resolve_target(frames, *depth, false)?;
                let wasm_depth = match target {
                    Target::Block { wasm_depth } => wasm_depth,
                    Target::Loop { .. } => unreachable!(),
                };
                match cond {
                    None => {
                        for &v in values {
                            let (l, _) = locals.get(v)?;
                            sink.local_get(l);
                        }
                        sink.br(wasm_depth);
                        return Ok(false);
                    }
                    Some(c) => {
                        let (cl, _) = locals.get(*c)?;
                        if values.is_empty() {
                            sink.local_get(cl);
                            sink.br_if(wasm_depth);
                        } else {
                            // Guarded branch carrying values: avoid leaving values on stack when false.
                            sink.local_get(cl);
                            sink.if_(BlockType::Empty);
                            for &v in values {
                                let (l, _) = locals.get(v)?;
                                sink.local_get(l);
                            }
                            sink.br(wasm_depth + 1);
                            sink.end();
                        }
                    }
                }
            }
            Stmt::Continue {
                depth,
                cond,
                values,
            } => {
                let (wasm_depth, state_locals) = match resolve_target(frames, *depth, true)? {
                    Target::Loop {
                        wasm_depth,
                        state_locals,
                    } => (wasm_depth, state_locals),
                    Target::Block { .. } => unreachable!(),
                };
                if values.len() != state_locals.len() {
                    return Err(WasmError::ValidationError(
                        "Continue values arity does not match loop state_vars".into(),
                    ));
                }
                match cond {
                    None => {
                        for &v in values {
                            let (l, _) = locals.get(v)?;
                            sink.local_get(l);
                        }
                        for &sl in state_locals.iter().rev() {
                            sink.local_set(sl);
                        }
                        sink.br(wasm_depth);
                        return Ok(false);
                    }
                    Some(c) => {
                        let (cl, _) = locals.get(*c)?;
                        sink.local_get(cl);
                        sink.if_(BlockType::Empty);
                        for &v in values {
                            let (l, _) = locals.get(v)?;
                            sink.local_get(l);
                        }
                        for &sl in state_locals.iter().rev() {
                            sink.local_set(sl);
                        }
                        sink.br(wasm_depth + 1);
                        sink.end();
                    }
                }
            }
        }
    }
    Ok(true)
}

fn memarg(mem_idx: u32, offset: u32, width: MemWidth) -> MemArg {
    let align = match width {
        MemWidth::B1 => 0,
        MemWidth::B2 => 1,
        MemWidth::B4 => 2,
        MemWidth::B8 => 3,
    };
    MemArg {
        offset: u64::from(offset),
        align,
        target: MemArgTarget::Memory(mem_idx),
        ordering: None,
    }
}

fn lookup_mem(ctx: &EmitCtx<'_>, id: MemId) -> Result<u32, WasmError> {
    ctx.mem_map
        .get(&id)
        .copied()
        .ok_or_else(|| WasmError::ValidationError(format!("unknown MemId {id:?}")))
}

fn emit_op(
    ctx: &EmitCtx<'_>,
    locals: &LocalEnv,
    sink: &mut InstructionSink<'_>,
    op: &Op,
) -> Result<(), WasmError> {
    match op {
        Op::ConstI32(v) => {
            sink.i32_const(*v);
        }
        Op::ConstI64(v) => {
            sink.i64_const(*v);
        }
        Op::Copy(id) => {
            let (l, _) = locals.get(*id)?;
            sink.local_get(l);
        }
        Op::Select {
            cond,
            true_val,
            false_val,
        } => {
            let (tl, _) = locals.get(*true_val)?;
            let (fl, _) = locals.get(*false_val)?;
            let (cl, _) = locals.get(*cond)?;
            sink.local_get(tl);
            sink.local_get(fl);
            sink.local_get(cl);
            sink.select();
        }
        Op::GlobalGet(gid) => {
            let idx = ctx
                .global_map
                .get(gid)
                .copied()
                .ok_or_else(|| WasmError::ValidationError(format!("unknown GlobalId {gid:?}")))?;
            sink.global_get(idx);
        }
        Op::Un(unop, a) => {
            let (al, _) = locals.get(*a)?;
            sink.local_get(al);
            match unop {
                UnOp::I32Eqz => sink.i32_eqz(),
                UnOp::I64Eqz => sink.i64_eqz(),
                UnOp::I32Clz => sink.i32_clz(),
                UnOp::I32Ctz => sink.i32_ctz(),
                UnOp::I32Popcnt => sink.i32_popcnt(),
                UnOp::I64Clz => sink.i64_clz(),
                UnOp::I64Ctz => sink.i64_ctz(),
                UnOp::I64Popcnt => sink.i64_popcnt(),
                UnOp::I32WrapI64 => sink.i32_wrap_i64(),
                UnOp::I64ExtendI32S => sink.i64_extend_i32_s(),
                UnOp::I64ExtendI32U => sink.i64_extend_i32_u(),
                UnOp::I32Extend8S => sink.i32_extend8_s(),
                UnOp::I32Extend16S => sink.i32_extend16_s(),
                UnOp::I64Extend8S => sink.i64_extend8_s(),
                UnOp::I64Extend16S => sink.i64_extend16_s(),
                UnOp::I64Extend32S => sink.i64_extend32_s(),
            };
        }
        Op::Bin(binop, l, r) => {
            let (ll, _) = locals.get(*l)?;
            let (rl, _) = locals.get(*r)?;
            sink.local_get(ll);
            sink.local_get(rl);
            match binop {
                BinOp::I32Eq => sink.i32_eq(),
                BinOp::I32Ne => sink.i32_ne(),
                BinOp::I32LtS => sink.i32_lt_s(),
                BinOp::I32LtU => sink.i32_lt_u(),
                BinOp::I32GtS => sink.i32_gt_s(),
                BinOp::I32GtU => sink.i32_gt_u(),
                BinOp::I32LeS => sink.i32_le_s(),
                BinOp::I32LeU => sink.i32_le_u(),
                BinOp::I32GeS => sink.i32_ge_s(),
                BinOp::I32GeU => sink.i32_ge_u(),
                BinOp::I64Eq => sink.i64_eq(),
                BinOp::I64Ne => sink.i64_ne(),
                BinOp::I64LtS => sink.i64_lt_s(),
                BinOp::I64LtU => sink.i64_lt_u(),
                BinOp::I64GtS => sink.i64_gt_s(),
                BinOp::I64GtU => sink.i64_gt_u(),
                BinOp::I64LeS => sink.i64_le_s(),
                BinOp::I64LeU => sink.i64_le_u(),
                BinOp::I64GeS => sink.i64_ge_s(),
                BinOp::I64GeU => sink.i64_ge_u(),
                BinOp::I32Add => sink.i32_add(),
                BinOp::I32Sub => sink.i32_sub(),
                BinOp::I32Mul => sink.i32_mul(),
                BinOp::I32DivS => sink.i32_div_s(),
                BinOp::I32DivU => sink.i32_div_u(),
                BinOp::I32RemS => sink.i32_rem_s(),
                BinOp::I32RemU => sink.i32_rem_u(),
                BinOp::I64Add => sink.i64_add(),
                BinOp::I64Sub => sink.i64_sub(),
                BinOp::I64Mul => sink.i64_mul(),
                BinOp::I64DivS => sink.i64_div_s(),
                BinOp::I64DivU => sink.i64_div_u(),
                BinOp::I64RemS => sink.i64_rem_s(),
                BinOp::I64RemU => sink.i64_rem_u(),
                BinOp::I32And => sink.i32_and(),
                BinOp::I32Or => sink.i32_or(),
                BinOp::I32Xor => sink.i32_xor(),
                BinOp::I32Shl => sink.i32_shl(),
                BinOp::I32ShrS => sink.i32_shr_s(),
                BinOp::I32ShrU => sink.i32_shr_u(),
                BinOp::I32Rotl => sink.i32_rotl(),
                BinOp::I32Rotr => sink.i32_rotr(),
                BinOp::I64And => sink.i64_and(),
                BinOp::I64Or => sink.i64_or(),
                BinOp::I64Xor => sink.i64_xor(),
                BinOp::I64Shl => sink.i64_shl(),
                BinOp::I64ShrS => sink.i64_shr_s(),
                BinOp::I64ShrU => sink.i64_shr_u(),
                BinOp::I64Rotl => sink.i64_rotl(),
                BinOp::I64Rotr => sink.i64_rotr(),
            };
        }
        Op::Load {
            mem,
            addr,
            offset,
            width,
            signed,
            result_ty,
        } => {
            let mem_idx = lookup_mem(ctx, *mem)?;
            let (al, _) = locals.get(*addr)?;
            sink.local_get(al);
            let ma = memarg(mem_idx, *offset, *width);
            match (result_ty, width, signed) {
                (ValType::I32, MemWidth::B1, true) => sink.i32_load8_s(ma),
                (ValType::I32, MemWidth::B1, false) => sink.i32_load8_u(ma),
                (ValType::I32, MemWidth::B2, true) => sink.i32_load16_s(ma),
                (ValType::I32, MemWidth::B2, false) => sink.i32_load16_u(ma),
                (ValType::I32, MemWidth::B4, _) => sink.i32_load(ma),
                (ValType::I64, MemWidth::B1, true) => sink.i64_load8_s(ma),
                (ValType::I64, MemWidth::B1, false) => sink.i64_load8_u(ma),
                (ValType::I64, MemWidth::B2, true) => sink.i64_load16_s(ma),
                (ValType::I64, MemWidth::B2, false) => sink.i64_load16_u(ma),
                (ValType::I64, MemWidth::B4, true) => sink.i64_load32_s(ma),
                (ValType::I64, MemWidth::B4, false) => sink.i64_load32_u(ma),
                (ValType::I64, MemWidth::B8, _) => sink.i64_load(ma),
                (ValType::I32, MemWidth::B8, _) => {
                    return Err(WasmError::ValidationError(
                        "invalid 8-byte load into i32".into(),
                    ));
                }
            };
        }
        Op::MemorySize(mem) => {
            let mem_idx = lookup_mem(ctx, *mem)?;
            sink.memory_size(mem_idx);
        }
        Op::MemoryGrow { mem, delta } => {
            let mem_idx = lookup_mem(ctx, *mem)?;
            let (dl, _) = locals.get(*delta)?;
            sink.local_get(dl);
            sink.memory_grow(mem_idx);
        }
    }
    Ok(())
}

/// Returns `true` if the effect unconditionally traps.
fn emit_effect(
    ctx: &EmitCtx<'_>,
    locals: &LocalEnv,
    sink: &mut InstructionSink<'_>,
    eff: &EffectOp,
) -> Result<bool, WasmError> {
    match eff {
        EffectOp::Store {
            mem,
            addr,
            offset,
            width,
            val,
        } => {
            let mem_idx = lookup_mem(ctx, *mem)?;
            let (al, _) = locals.get(*addr)?;
            let (vl, vty) = locals.get(*val)?;
            sink.local_get(al);
            sink.local_get(vl);
            let ma = memarg(mem_idx, *offset, *width);
            match (vty, width) {
                (ValType::I32, MemWidth::B1) => sink.i32_store8(ma),
                (ValType::I32, MemWidth::B2) => sink.i32_store16(ma),
                (ValType::I32, MemWidth::B4) => sink.i32_store(ma),
                (ValType::I64, MemWidth::B1) => sink.i64_store8(ma),
                (ValType::I64, MemWidth::B2) => sink.i64_store16(ma),
                (ValType::I64, MemWidth::B4) => sink.i64_store32(ma),
                (ValType::I64, MemWidth::B8) => sink.i64_store(ma),
                (ValType::I32, MemWidth::B8) => {
                    return Err(WasmError::ValidationError(
                        "invalid 8-byte store from i32".into(),
                    ));
                }
            };
            Ok(false)
        }
        EffectOp::MemoryCopy {
            dst_mem,
            src_mem,
            dst,
            src,
            len,
        } => {
            let dm = lookup_mem(ctx, *dst_mem)?;
            let sm = lookup_mem(ctx, *src_mem)?;
            let (dl, _) = locals.get(*dst)?;
            let (sl, _) = locals.get(*src)?;
            let (ll, _) = locals.get(*len)?;
            sink.local_get(dl);
            sink.local_get(sl);
            sink.local_get(ll);
            sink.memory_copy(dm, sm);
            Ok(false)
        }
        EffectOp::MemoryFill {
            mem,
            dst,
            val,
            len,
        } => {
            let m = lookup_mem(ctx, *mem)?;
            let (dl, _) = locals.get(*dst)?;
            let (vl, _) = locals.get(*val)?;
            let (ll, _) = locals.get(*len)?;
            sink.local_get(dl);
            sink.local_get(vl);
            sink.local_get(ll);
            sink.memory_fill(m);
            Ok(false)
        }
        EffectOp::GlobalSet { id, val } => {
            let gidx = ctx
                .global_map
                .get(id)
                .copied()
                .ok_or_else(|| WasmError::ValidationError(format!("unknown GlobalId {id:?}")))?;
            let (vl, _) = locals.get(*val)?;
            sink.local_get(vl);
            sink.global_set(gidx);
            Ok(false)
        }
        EffectOp::Trap(trap) => {
            match trap {
                gnomon_kernel::TrapCode::DivByZero => {
                    sink.i32_const(1).i32_const(0).i32_div_s().drop();
                }
                gnomon_kernel::TrapCode::IntOverflow => {
                    sink.i32_const(i32::MIN).i32_const(-1).i32_div_s().drop();
                }
                _ => {
                    sink.unreachable();
                }
            }
            Ok(true)
        }
        EffectOp::Nop => {
            sink.nop();
            Ok(false)
        }
    }
}
