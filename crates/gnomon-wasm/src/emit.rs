//! Lossless `GnomonIR` -> `.wasm` emitter powered by `wasm-encoder`,
//! self-validated via `wasmparser::Validator`.

use std::collections::HashMap;

use gnomon_kernel::{
    BinOp, CallTarget, EffectOp, FuncDef, FuncId, GlobalId, HostCallId, LaneKind, MemId, MemWidth,
    Module, Op, RegionNode, RegionRef, Span, Stmt, UnOp, Val, ValId, ValType,
};
use wasm_encoder::{
    BlockType, CodeSection, ConstExpr, DataSection, EntityType, ExportKind, ExportSection,
    Function, FunctionSection, GlobalSection, GlobalType, Ieee32, Ieee64, ImportSection,
    InstructionSink, MemArg, MemArgTarget, MemorySection, MemoryType, Module as WasmModule,
    TypeSection, ValType as WValType,
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
                Val::F32(b) => ConstExpr::f32_const(Ieee32::new(b)),
                Val::F64(b) => ConstExpr::f64_const(Ieee64::new(b)),
                Val::V128(b) => ConstExpr::v128_const(b as i128),
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
        ValType::F32 => WValType::F32,
        ValType::F64 => WValType::F64,
        ValType::V128 => WValType::V128,
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
        let root_ref = f.body.as_ref();
        match root_ref.node {
            RegionNode::Block(stmts) => {
                emit_block_stmts(ctx, type_pool, &mut locals, &mut frames, &mut sink, root_ref, stmts)?;
            }
            _ => {
                let mut root_frames = Vec::new();
                emit_region(
                    ctx,
                    type_pool,
                    &mut locals,
                    &mut root_frames,
                    &mut sink,
                    root_ref,
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
    region: RegionRef<'_>,
    expected_results: &[ValType],
) -> Result<bool, WasmError> {
    match region.node {
        RegionNode::Block(stmts) => {
            let bt = type_pool.block_type(expected_results);
            sink.block(bt);
            frames.push(EmitFrame::Block {
                ir_depth_cost: true,
            });
            let saved = locals.bindings.clone();
            let res = emit_block_stmts(ctx, type_pool, locals, frames, sink, region, stmts);
            locals.bindings = saved;
            let fell_through = res?;
            frames.pop();
            sink.end();
            Ok(fell_through)
        }
        RegionNode::IfElse {
            cond,
            then_region,
            else_region,
            results,
        } => {
            let (cond_local, _) = locals.get(cond)?;
            sink.local_get(cond_local);
            let res_tys = region.region.tys_vec(results);
            let bt = type_pool.block_type(&res_tys);
            sink.if_(bt);

            let then_ref = region.child(then_region).ok_or_else(|| {
                WasmError::ValidationError("invalid IfElse then_region node id".into())
            })?;
            let else_ref = region.child(else_region).ok_or_else(|| {
                WasmError::ValidationError("invalid IfElse else_region node id".into())
            })?;
            emit_if_branch(ctx, type_pool, locals, frames, sink, then_ref, &res_tys)?;
            let skip_else = res_tys.is_empty() && else_ref.is_empty_block();
            if !skip_else {
                sink.else_();
                emit_if_branch(ctx, type_pool, locals, frames, sink, else_ref, &res_tys)?;
            }
            sink.end();
            Ok(true)
        }
        RegionNode::BoundedLoop {
            max_iters,
            init_vars,
            state_vars,
            body,
        } => {
            if init_vars.len != state_vars.len {
                return Err(WasmError::ValidationError(
                    "BoundedLoop init_vars/state_vars length mismatch".into(),
                ));
            }
            for iv in region.vals(init_vars) {
                let (l, _) = locals.get(iv)?;
                sink.local_get(l);
            }
            let saved_bindings = locals.bindings.clone();
            let mut state_locals = Vec::with_capacity(state_vars.len_usize());
            for (sv, ty) in region.vars(state_vars) {
                state_locals.push(locals.bind(sv, ty));
            }
            for &sl in state_locals.iter().rev() {
                sink.local_set(sl);
            }

            let rem_local = if max_iters < u32::MAX {
                let rl = locals.alloc_temp(ValType::I32);
                sink.i32_const(max_iters as i32);
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

            let body_ref = region.child(body).ok_or_else(|| {
                WasmError::ValidationError("invalid BoundedLoop body node id".into())
            })?;
            let body_res = match body_ref.node {
                RegionNode::Block(stmts) => {
                    emit_block_stmts(ctx, type_pool, locals, frames, sink, body_ref, stmts)
                }
                _ => emit_region(
                    ctx,
                    type_pool,
                    locals,
                    frames,
                    sink,
                    body_ref,
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
        RegionNode::InvariantLoop {
            init_vars,
            state_vars,
            cond,
            body,
            ..
        } => {
            if init_vars.len != state_vars.len {
                return Err(WasmError::ValidationError(
                    "InvariantLoop init_vars/state_vars length mismatch".into(),
                ));
            }
            for iv in region.vals(init_vars) {
                let (l, _) = locals.get(iv)?;
                sink.local_get(l);
            }
            let saved_bindings = locals.bindings.clone();
            let mut state_locals = Vec::with_capacity(state_vars.len_usize());
            let mut state_tys = Vec::with_capacity(state_vars.len_usize());
            for (sv, ty) in region.vars(state_vars) {
                state_locals.push(locals.bind(sv, ty));
                state_tys.push(ty);
            }
            for &sl in state_locals.iter().rev() {
                sink.local_set(sl);
            }

            let bt = type_pool.block_type(&state_tys);
            sink.block(bt);
            sink.loop_(bt);

            let cond_ref = region.child(cond).ok_or_else(|| {
                WasmError::ValidationError("invalid InvariantLoop cond node id".into())
            })?;
            let cond_res: Result<bool, WasmError> = match cond_ref.node {
                RegionNode::Block(stmts) => {
                    sink.block(BlockType::Result(WValType::I32));
                    frames.push(EmitFrame::Block {
                        ir_depth_cost: true,
                    });
                    let saved_cond = locals.bindings.clone();
                    let r = emit_block_stmts(ctx, type_pool, locals, frames, sink, cond_ref, stmts);
                    locals.bindings = saved_cond;
                    frames.pop();
                    sink.end();
                    r
                }
                _ => emit_region(
                    ctx,
                    type_pool,
                    locals,
                    frames,
                    sink,
                    cond_ref,
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
            sink.br(2);
            sink.end();

            frames.push(EmitFrame::LoopExit);
            frames.push(EmitFrame::LoopCont {
                state_locals: state_locals.clone(),
            });

            let body_ref = region.child(body).ok_or_else(|| {
                WasmError::ValidationError("invalid InvariantLoop body node id".into())
            })?;
            let body_res = match body_ref.node {
                RegionNode::Block(stmts) => {
                    let saved_body = locals.bindings.clone();
                    let r = emit_block_stmts(ctx, type_pool, locals, frames, sink, body_ref, stmts);
                    locals.bindings = saved_body;
                    r
                }
                _ => emit_region(ctx, type_pool, locals, frames, sink, body_ref, &state_tys),
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
    branch: RegionRef<'_>,
    expected_results: &[ValType],
) -> Result<(), WasmError> {
    let saved = locals.bindings.clone();
    let res = match branch.node {
        RegionNode::Block(stmts) => {
            frames.push(EmitFrame::Block {
                ir_depth_cost: true,
            });
            let r = emit_block_stmts(ctx, type_pool, locals, frames, sink, branch, stmts);
            frames.pop();
            r.map(|_| ())
        }
        _ => {
            frames.push(EmitFrame::Block {
                ir_depth_cost: false,
            });
            let r = emit_region(
                ctx,
                type_pool,
                locals,
                frames,
                sink,
                branch,
                expected_results,
            );
            frames.pop();
            r.map(|_| ())
        }
    };
    locals.bindings = saved;
    res
}

/// Emits statements in a `RegionNode::Block`. Returns `true` if control could fall through
/// normally without hitting an unconditional terminator (`Yield`/`Break`/`Continue`/`Return`/`Trap`).
fn emit_block_stmts(
    ctx: &EmitCtx<'_>,
    type_pool: &mut TypePool,
    locals: &mut LocalEnv,
    frames: &mut Vec<EmitFrame>,
    sink: &mut InstructionSink<'_>,
    owner: RegionRef<'_>,
    stmts: Span,
) -> Result<bool, WasmError> {
    for stmt in owner.stmts(stmts) {
        match stmt {
            Stmt::Let { dst, ty, op } => {
                emit_op(ctx, locals, sink, &op)?;
                let l = locals.bind(dst, ty);
                sink.local_set(l);
            }
            Stmt::Effect(eff) => {
                let trapped = emit_effect(ctx, locals, sink, &eff)?;
                if trapped {
                    return Ok(false);
                }
            }
            Stmt::Region { results, region } => {
                let res_tys: Vec<ValType> = owner.vars(results).map(|(_, ty)| ty).collect();
                let sub_ref = owner.child(region).ok_or_else(|| {
                    WasmError::ValidationError("invalid Stmt::Region node id".into())
                })?;
                emit_region(ctx, type_pool, locals, frames, sink, sub_ref, &res_tys)?;
                let mut res_locals = Vec::with_capacity(results.len_usize());
                for (id, ty) in owner.vars(results) {
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
                for a in owner.vals(args) {
                    let (l, _) = locals.get(a)?;
                    sink.local_get(l);
                }
                let func_idx = match target {
                    CallTarget::Func(fid) => *ctx.func_map.get(&fid).ok_or_else(|| {
                        WasmError::ValidationError(format!("unknown FuncId {fid:?}"))
                    })?,
                    CallTarget::Host(hid) => *ctx.host_map.get(&hid).ok_or_else(|| {
                        WasmError::ValidationError(format!("unknown HostCallId {hid:?}"))
                    })?,
                    CallTarget::Stratum(sid) => {
                        return Err(WasmError::UnsupportedFeature(format!(
                            "CallTarget::Stratum({sid:?}) must be lowered to Layer 0 before emit_wasm"
                        )));
                    }
                };
                sink.call(func_idx);
                let mut res_locals = Vec::with_capacity(results.len_usize());
                for (id, ty) in owner.vars(results) {
                    res_locals.push(locals.bind(id, ty));
                }
                for &rl in res_locals.iter().rev() {
                    sink.local_set(rl);
                }
            }
            Stmt::Yield(vals) => {
                for v in owner.vals(vals) {
                    let (l, _) = locals.get(v)?;
                    sink.local_get(l);
                }
                return Ok(true);
            }
            Stmt::Return(vals) => {
                for v in owner.vals(vals) {
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
                let target = resolve_target(frames, depth, false)?;
                let wasm_depth = match target {
                    Target::Block { wasm_depth } => wasm_depth,
                    Target::Loop { .. } => unreachable!(),
                };
                match cond {
                    None => {
                        for v in owner.vals(values) {
                            let (l, _) = locals.get(v)?;
                            sink.local_get(l);
                        }
                        sink.br(wasm_depth);
                        return Ok(false);
                    }
                    Some(c) => {
                        let (cl, _) = locals.get(c)?;
                        if values.is_empty() {
                            sink.local_get(cl);
                            sink.br_if(wasm_depth);
                        } else {
                            sink.local_get(cl);
                            sink.if_(BlockType::Empty);
                            for v in owner.vals(values) {
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
                let (wasm_depth, state_locals) = match resolve_target(frames, depth, true)? {
                    Target::Loop {
                        wasm_depth,
                        state_locals,
                    } => (wasm_depth, state_locals),
                    Target::Block { .. } => unreachable!(),
                };
                if values.len_usize() != state_locals.len() {
                    return Err(WasmError::ValidationError(
                        "Continue values arity does not match loop state_vars".into(),
                    ));
                }
                match cond {
                    None => {
                        for v in owner.vals(values) {
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
                        let (cl, _) = locals.get(c)?;
                        sink.local_get(cl);
                        sink.if_(BlockType::Empty);
                        for v in owner.vals(values) {
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
        MemWidth::B16 => 4,
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
        Op::ConstF32(bits) => {
            sink.f32_const(Ieee32::new(*bits));
        }
        Op::ConstF64(bits) => {
            sink.f64_const(Ieee64::new(*bits));
        }
        Op::ConstV128(bits) => {
            sink.v128_const(*bits as i128);
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
                // Integer unary (0..=15)
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
                // Scalar FP unary (16..=29)
                UnOp::F32Abs => sink.f32_abs(),
                UnOp::F32Neg => sink.f32_neg(),
                UnOp::F32Ceil => sink.f32_ceil(),
                UnOp::F32Floor => sink.f32_floor(),
                UnOp::F32Trunc => sink.f32_trunc(),
                UnOp::F32Nearest => sink.f32_nearest(),
                UnOp::F32Sqrt => sink.f32_sqrt(),
                UnOp::F64Abs => sink.f64_abs(),
                UnOp::F64Neg => sink.f64_neg(),
                UnOp::F64Ceil => sink.f64_ceil(),
                UnOp::F64Floor => sink.f64_floor(),
                UnOp::F64Trunc => sink.f64_trunc(),
                UnOp::F64Nearest => sink.f64_nearest(),
                UnOp::F64Sqrt => sink.f64_sqrt(),
                // Trapping float-to-int truncations (30..=37)
                UnOp::I32TruncF32S => sink.i32_trunc_f32_s(),
                UnOp::I32TruncF32U => sink.i32_trunc_f32_u(),
                UnOp::I32TruncF64S => sink.i32_trunc_f64_s(),
                UnOp::I32TruncF64U => sink.i32_trunc_f64_u(),
                UnOp::I64TruncF32S => sink.i64_trunc_f32_s(),
                UnOp::I64TruncF32U => sink.i64_trunc_f32_u(),
                UnOp::I64TruncF64S => sink.i64_trunc_f64_s(),
                UnOp::I64TruncF64U => sink.i64_trunc_f64_u(),
                // Saturating float-to-int truncations (38..=45)
                UnOp::I32TruncSatF32S => sink.i32_trunc_sat_f32_s(),
                UnOp::I32TruncSatF32U => sink.i32_trunc_sat_f32_u(),
                UnOp::I32TruncSatF64S => sink.i32_trunc_sat_f64_s(),
                UnOp::I32TruncSatF64U => sink.i32_trunc_sat_f64_u(),
                UnOp::I64TruncSatF32S => sink.i64_trunc_sat_f32_s(),
                UnOp::I64TruncSatF32U => sink.i64_trunc_sat_f32_u(),
                UnOp::I64TruncSatF64S => sink.i64_trunc_sat_f64_s(),
                UnOp::I64TruncSatF64U => sink.i64_trunc_sat_f64_u(),
                // Int-to-float conversions (46..=53)
                UnOp::F32ConvertI32S => sink.f32_convert_i32_s(),
                UnOp::F32ConvertI32U => sink.f32_convert_i32_u(),
                UnOp::F32ConvertI64S => sink.f32_convert_i64_s(),
                UnOp::F32ConvertI64U => sink.f32_convert_i64_u(),
                UnOp::F64ConvertI32S => sink.f64_convert_i32_s(),
                UnOp::F64ConvertI32U => sink.f64_convert_i32_u(),
                UnOp::F64ConvertI64S => sink.f64_convert_i64_s(),
                UnOp::F64ConvertI64U => sink.f64_convert_i64_u(),
                // Demote / Promote / Reinterpret (54..=59)
                UnOp::F32DemoteF64 => sink.f32_demote_f64(),
                UnOp::F64PromoteF32 => sink.f64_promote_f32(),
                UnOp::I32ReinterpretF32 => sink.i32_reinterpret_f32(),
                UnOp::I64ReinterpretF64 => sink.i64_reinterpret_f64(),
                UnOp::F32ReinterpretI32 => sink.f32_reinterpret_i32(),
                UnOp::F64ReinterpretI64 => sink.f64_reinterpret_i64(),
                // v128 unary / splat / bitmask / lane-convert / extend (60..=99)
                UnOp::V128Not => sink.v128_not(),
                UnOp::V128AnyTrue => sink.v128_any_true(),
                UnOp::I8x16Splat => sink.i8x16_splat(),
                UnOp::I16x8Splat => sink.i16x8_splat(),
                UnOp::I32x4Splat => sink.i32x4_splat(),
                UnOp::I64x2Splat => sink.i64x2_splat(),
                UnOp::F32x4Splat => sink.f32x4_splat(),
                UnOp::F64x2Splat => sink.f64x2_splat(),
                UnOp::I8x16Bitmask => sink.i8x16_bitmask(),
                UnOp::I16x8Bitmask => sink.i16x8_bitmask(),
                UnOp::I32x4Bitmask => sink.i32x4_bitmask(),
                UnOp::I64x2Bitmask => sink.i64x2_bitmask(),
                UnOp::I32x4AllTrue => sink.i32x4_all_true(),
                UnOp::I64x2AllTrue => sink.i64x2_all_true(),
                UnOp::I32x4Abs => sink.i32x4_abs(),
                UnOp::I32x4Neg => sink.i32x4_neg(),
                UnOp::I64x2Abs => sink.i64x2_abs(),
                UnOp::I64x2Neg => sink.i64x2_neg(),
                UnOp::F32x4Abs => sink.f32x4_abs(),
                UnOp::F32x4Neg => sink.f32x4_neg(),
                UnOp::F32x4Sqrt => sink.f32x4_sqrt(),
                UnOp::F32x4Ceil => sink.f32x4_ceil(),
                UnOp::F32x4Floor => sink.f32x4_floor(),
                UnOp::F32x4Trunc => sink.f32x4_trunc(),
                UnOp::F32x4Nearest => sink.f32x4_nearest(),
                UnOp::F64x2Abs => sink.f64x2_abs(),
                UnOp::F64x2Neg => sink.f64x2_neg(),
                UnOp::F64x2Sqrt => sink.f64x2_sqrt(),
                UnOp::F64x2Ceil => sink.f64x2_ceil(),
                UnOp::F64x2Floor => sink.f64x2_floor(),
                UnOp::F64x2Trunc => sink.f64x2_trunc(),
                UnOp::F64x2Nearest => sink.f64x2_nearest(),
                UnOp::I32x4TruncSatF32x4S => sink.i32x4_trunc_sat_f32x4_s(),
                UnOp::I32x4TruncSatF32x4U => sink.i32x4_trunc_sat_f32x4_u(),
                UnOp::F32x4ConvertI32x4S => sink.f32x4_convert_i32x4_s(),
                UnOp::F32x4ConvertI32x4U => sink.f32x4_convert_i32x4_u(),
                UnOp::I64x2ExtendLowI32x4S => sink.i64x2_extend_low_i32x4_s(),
                UnOp::I64x2ExtendLowI32x4U => sink.i64x2_extend_low_i32x4_u(),
                UnOp::I64x2ExtendHighI32x4S => sink.i64x2_extend_high_i32x4_s(),
                UnOp::I64x2ExtendHighI32x4U => sink.i64x2_extend_high_i32x4_u(),
            };
        }
        Op::Bin(binop, l, r) => {
            let (ll, _) = locals.get(*l)?;
            let (rl, _) = locals.get(*r)?;
            sink.local_get(ll);
            sink.local_get(rl);
            match binop {
                // Integer binary (0..=49)
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
                // Scalar FP binary (50..=75)
                BinOp::F32Add => sink.f32_add(),
                BinOp::F32Sub => sink.f32_sub(),
                BinOp::F32Mul => sink.f32_mul(),
                BinOp::F32Div => sink.f32_div(),
                BinOp::F32Min => sink.f32_min(),
                BinOp::F32Max => sink.f32_max(),
                BinOp::F32Copysign => sink.f32_copysign(),
                BinOp::F32Eq => sink.f32_eq(),
                BinOp::F32Ne => sink.f32_ne(),
                BinOp::F32Lt => sink.f32_lt(),
                BinOp::F32Gt => sink.f32_gt(),
                BinOp::F32Le => sink.f32_le(),
                BinOp::F32Ge => sink.f32_ge(),
                BinOp::F64Add => sink.f64_add(),
                BinOp::F64Sub => sink.f64_sub(),
                BinOp::F64Mul => sink.f64_mul(),
                BinOp::F64Div => sink.f64_div(),
                BinOp::F64Min => sink.f64_min(),
                BinOp::F64Max => sink.f64_max(),
                BinOp::F64Copysign => sink.f64_copysign(),
                BinOp::F64Eq => sink.f64_eq(),
                BinOp::F64Ne => sink.f64_ne(),
                BinOp::F64Lt => sink.f64_lt(),
                BinOp::F64Gt => sink.f64_gt(),
                BinOp::F64Le => sink.f64_le(),
                BinOp::F64Ge => sink.f64_ge(),
                // v128 bitwise & swizzle (76..=80)
                BinOp::V128And => sink.v128_and(),
                BinOp::V128AndNot => sink.v128_andnot(),
                BinOp::V128Or => sink.v128_or(),
                BinOp::V128Xor => sink.v128_xor(),
                BinOp::I8x16Swizzle => sink.i8x16_swizzle(),
                // i32x4 lane binary (81..=100)
                BinOp::I32x4Add => sink.i32x4_add(),
                BinOp::I32x4Sub => sink.i32x4_sub(),
                BinOp::I32x4Mul => sink.i32x4_mul(),
                BinOp::I32x4MinS => sink.i32x4_min_s(),
                BinOp::I32x4MinU => sink.i32x4_min_u(),
                BinOp::I32x4MaxS => sink.i32x4_max_s(),
                BinOp::I32x4MaxU => sink.i32x4_max_u(),
                BinOp::I32x4Eq => sink.i32x4_eq(),
                BinOp::I32x4Ne => sink.i32x4_ne(),
                BinOp::I32x4LtS => sink.i32x4_lt_s(),
                BinOp::I32x4LtU => sink.i32x4_lt_u(),
                BinOp::I32x4GtS => sink.i32x4_gt_s(),
                BinOp::I32x4GtU => sink.i32x4_gt_u(),
                BinOp::I32x4LeS => sink.i32x4_le_s(),
                BinOp::I32x4LeU => sink.i32x4_le_u(),
                BinOp::I32x4GeS => sink.i32x4_ge_s(),
                BinOp::I32x4GeU => sink.i32x4_ge_u(),
                BinOp::I32x4Shl => sink.i32x4_shl(),
                BinOp::I32x4ShrS => sink.i32x4_shr_s(),
                BinOp::I32x4ShrU => sink.i32x4_shr_u(),
                // i64x2 lane binary (101..=112)
                BinOp::I64x2Add => sink.i64x2_add(),
                BinOp::I64x2Sub => sink.i64x2_sub(),
                BinOp::I64x2Mul => sink.i64x2_mul(),
                BinOp::I64x2Eq => sink.i64x2_eq(),
                BinOp::I64x2Ne => sink.i64x2_ne(),
                BinOp::I64x2LtS => sink.i64x2_lt_s(),
                BinOp::I64x2GtS => sink.i64x2_gt_s(),
                BinOp::I64x2LeS => sink.i64x2_le_s(),
                BinOp::I64x2GeS => sink.i64x2_ge_s(),
                BinOp::I64x2Shl => sink.i64x2_shl(),
                BinOp::I64x2ShrS => sink.i64x2_shr_s(),
                BinOp::I64x2ShrU => sink.i64x2_shr_u(),
                // f32x4 lane binary (113..=126)
                BinOp::F32x4Add => sink.f32x4_add(),
                BinOp::F32x4Sub => sink.f32x4_sub(),
                BinOp::F32x4Mul => sink.f32x4_mul(),
                BinOp::F32x4Div => sink.f32x4_div(),
                BinOp::F32x4Min => sink.f32x4_min(),
                BinOp::F32x4Max => sink.f32x4_max(),
                BinOp::F32x4PMin => sink.f32x4_pmin(),
                BinOp::F32x4PMax => sink.f32x4_pmax(),
                BinOp::F32x4Eq => sink.f32x4_eq(),
                BinOp::F32x4Ne => sink.f32x4_ne(),
                BinOp::F32x4Lt => sink.f32x4_lt(),
                BinOp::F32x4Gt => sink.f32x4_gt(),
                BinOp::F32x4Le => sink.f32x4_le(),
                BinOp::F32x4Ge => sink.f32x4_ge(),
                // f64x2 lane binary (127..=140)
                BinOp::F64x2Add => sink.f64x2_add(),
                BinOp::F64x2Sub => sink.f64x2_sub(),
                BinOp::F64x2Mul => sink.f64x2_mul(),
                BinOp::F64x2Div => sink.f64x2_div(),
                BinOp::F64x2Min => sink.f64x2_min(),
                BinOp::F64x2Max => sink.f64x2_max(),
                BinOp::F64x2PMin => sink.f64x2_pmin(),
                BinOp::F64x2PMax => sink.f64x2_pmax(),
                BinOp::F64x2Eq => sink.f64x2_eq(),
                BinOp::F64x2Ne => sink.f64x2_ne(),
                BinOp::F64x2Lt => sink.f64x2_lt(),
                BinOp::F64x2Gt => sink.f64x2_gt(),
                BinOp::F64x2Le => sink.f64x2_le(),
                BinOp::F64x2Ge => sink.f64x2_ge(),
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
                (ValType::F32, MemWidth::B4, _) => sink.f32_load(ma),
                (ValType::F64, MemWidth::B8, _) => sink.f64_load(ma),
                (ValType::V128, MemWidth::B16, _) => sink.v128_load(ma),
                (ty, w, _) => {
                    return Err(WasmError::ValidationError(format!(
                        "invalid load width {w:?} for result type {ty:?}"
                    )));
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
        Op::SimdExtractLane { kind, lane, vec } => {
            if *lane >= kind.num_lanes() {
                return Err(WasmError::ValidationError(format!(
                    "SIMD extract lane {lane} out of range for {kind:?}"
                )));
            }
            let (vl, _) = locals.get(*vec)?;
            sink.local_get(vl);
            match kind {
                LaneKind::I8x16S => sink.i8x16_extract_lane_s(*lane),
                LaneKind::I8x16U => sink.i8x16_extract_lane_u(*lane),
                LaneKind::I16x8S => sink.i16x8_extract_lane_s(*lane),
                LaneKind::I16x8U => sink.i16x8_extract_lane_u(*lane),
                LaneKind::I32x4 => sink.i32x4_extract_lane(*lane),
                LaneKind::I64x2 => sink.i64x2_extract_lane(*lane),
                LaneKind::F32x4 => sink.f32x4_extract_lane(*lane),
                LaneKind::F64x2 => sink.f64x2_extract_lane(*lane),
            };
        }
        Op::SimdReplaceLane { kind, lane, vec, val } => {
            if *lane >= kind.num_lanes() {
                return Err(WasmError::ValidationError(format!(
                    "SIMD replace lane {lane} out of range for {kind:?}"
                )));
            }
            let (vecl, _) = locals.get(*vec)?;
            let (vall, _) = locals.get(*val)?;
            sink.local_get(vecl);
            sink.local_get(vall);
            match kind {
                LaneKind::I8x16S | LaneKind::I8x16U => sink.i8x16_replace_lane(*lane),
                LaneKind::I16x8S | LaneKind::I16x8U => sink.i16x8_replace_lane(*lane),
                LaneKind::I32x4 => sink.i32x4_replace_lane(*lane),
                LaneKind::I64x2 => sink.i64x2_replace_lane(*lane),
                LaneKind::F32x4 => sink.f32x4_replace_lane(*lane),
                LaneKind::F64x2 => sink.f64x2_replace_lane(*lane),
            };
        }
        Op::SimdBitselect { a, b, mask } => {
            let (al, _) = locals.get(*a)?;
            let (bl, _) = locals.get(*b)?;
            let (ml, _) = locals.get(*mask)?;
            sink.local_get(al);
            sink.local_get(bl);
            sink.local_get(ml);
            sink.v128_bitselect();
        }
        Op::SimdShuffle { lhs, rhs, lanes } => {
            let (ll, _) = locals.get(*lhs)?;
            let (rl, _) = locals.get(*rhs)?;
            sink.local_get(ll);
            sink.local_get(rl);
            sink.i8x16_shuffle(*lanes);
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
                (ValType::F32, MemWidth::B4) => sink.f32_store(ma),
                (ValType::F64, MemWidth::B8) => sink.f64_store(ma),
                (ValType::V128, MemWidth::B16) => sink.v128_store(ma),
                (ty, w) => {
                    return Err(WasmError::ValidationError(format!(
                        "invalid store width {w:?} for value type {ty:?}"
                    )));
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
