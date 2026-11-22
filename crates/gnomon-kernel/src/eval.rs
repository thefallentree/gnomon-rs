//! Deterministic small-step reference interpreter for `GnomonIR`.

use alloc::{vec, vec::Vec};
use crate::ir::*;
use crate::registry::StratumRegistry;
use crate::vc::validate_read_only_with_registry;

pub const WASM_PAGE_SIZE: usize = 65_536;
pub const MAX_WASM_PAGES: u32 = 65_536;
pub const MAX_CALL_DEPTH: u32 = 256;

/// Concrete state of one Wasm linear memory.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MemoryState { pub id: MemId, pub bytes: Vec<u8>, pub max_pages: Option<u32> }

impl MemoryState {
    fn ea_end(&self, addr: u32, offset: u32, len: u64) -> Result<usize, TrapCode> {
        let ea = (addr as u64).checked_add(offset as u64).ok_or(TrapCode::OutOfBoundsMem)?;
        let end = ea.checked_add(len).ok_or(TrapCode::OutOfBoundsMem)?;
        if end > self.bytes.len() as u64 { Err(TrapCode::OutOfBoundsMem) } else { Ok(ea as usize) }
    }

    pub fn load(&self, addr: u32, offset: u32, w: MemWidth, signed: bool, ty: ValType) -> Result<Val, TrapCode> {
        let s = &self.bytes[self.ea_end(addr, offset, w.bytes())?..][..w.bytes() as usize];
        let v: i64 = match (w, signed) {
            (MemWidth::B1, false) => s[0] as i64, (MemWidth::B1, true) => (s[0] as i8) as i64,
            (MemWidth::B2, false) => u16::from_le_bytes([s[0], s[1]]) as i64, (MemWidth::B2, true) => i16::from_le_bytes([s[0], s[1]]) as i64,
            (MemWidth::B4, false) => u32::from_le_bytes([s[0], s[1], s[2], s[3]]) as i64, (MemWidth::B4, true) => i32::from_le_bytes([s[0], s[1], s[2], s[3]]) as i64,
            (MemWidth::B8, _) if ty == ValType::I64 => u64::from_le_bytes(s.try_into().unwrap()) as i64,
            (MemWidth::B8, _) => return Err(TrapCode::Unreachable),
        };
        Ok(match ty { ValType::I32 => Val::I32(v as i32), ValType::I64 => Val::I64(v) })
    }
    pub fn store(&mut self, addr: u32, offset: u32, w: MemWidth, val: Val) -> Result<(), TrapCode> {
        let start = self.ea_end(addr, offset, w.bytes())?;
        let raw = match val { Val::I32(v) if w != MemWidth::B8 => v as u32 as u64, Val::I64(v) => v as u64, Val::I32(_) => return Err(TrapCode::Unreachable) };
        self.bytes[start..start + w.bytes() as usize].copy_from_slice(&raw.to_le_bytes()[..w.bytes() as usize]);
        Ok(())
    }
    pub fn fill(&mut self, dst: u32, val: u8, len: u32) -> Result<(), TrapCode> {
        let start = self.ea_end(dst, 0, len as u64)?;
        self.bytes[start..start + len as usize].fill(val);
        Ok(())
    }
    pub fn size_pages(&self) -> u32 { (self.bytes.len() / WASM_PAGE_SIZE) as u32 }
    pub fn grow(&mut self, delta: u32) -> i32 {
        let (cur, limit) = (self.size_pages(), self.max_pages.unwrap_or(MAX_WASM_PAGES).min(MAX_WASM_PAGES));
        let Some(len) = cur.checked_add(delta).filter(|&n| n <= limit).and_then(|n| (n as usize).checked_mul(WASM_PAGE_SIZE)) else { return -1 };
        self.bytes.resize(len, 0);
        cur as i32
    }
}

/// Complete deterministic VM memory, global, and fuel state.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HeapState { pub memories: Vec<MemoryState>, pub globals: Vec<Val>, pub fuel_remaining: u64 }

impl HeapState {
    pub fn from_module(module: &Module, fuel: u64) -> Result<Self, TrapCode> {
        let mut memories = Vec::with_capacity(module.memories.len());
        for m in &module.memories {
            if m.min_pages > m.max_pages.unwrap_or(MAX_WASM_PAGES).min(MAX_WASM_PAGES) { return Err(TrapCode::OutOfBoundsMem); }
            let len = (m.min_pages as usize).checked_mul(WASM_PAGE_SIZE).ok_or(TrapCode::OutOfBoundsMem)?;
            let mut bytes = vec![0u8; len];
            for (off, data) in &m.init_data {
                let end = (*off as u64).checked_add(data.len() as u64).ok_or(TrapCode::OutOfBoundsMem)?;
                if end > bytes.len() as u64 { return Err(TrapCode::OutOfBoundsMem); }
                bytes[*off as usize..end as usize].copy_from_slice(data);
            }
            memories.push(MemoryState { id: m.id, bytes, max_pages: m.max_pages });
        }
        Ok(Self { memories, globals: module.globals.iter().map(|g| g.init).collect(), fuel_remaining: fuel })
    }

    pub fn memory(&self, id: MemId) -> Result<&MemoryState, TrapCode> { self.memories.iter().find(|m| m.id == id).ok_or(TrapCode::OutOfBoundsMem) }
    pub fn memory_mut(&mut self, id: MemId) -> Result<&mut MemoryState, TrapCode> { self.memories.iter_mut().find(|m| m.id == id).ok_or(TrapCode::OutOfBoundsMem) }

    pub fn memory_copy(&mut self, dm: MemId, sm: MemId, dst: u32, src: u32, len: u32) -> Result<(), TrapCode> {
        let (ds, ss, n) = (self.memory(dm)?.ea_end(dst, 0, len as u64)?, self.memory(sm)?.ea_end(src, 0, len as u64)?, len as usize);
        if dm == sm { self.memory_mut(dm)?.bytes.copy_within(ss..ss + n, ds); } else {
            let chunk = self.memory(sm)?.bytes[ss..ss + n].to_vec();
            self.memory_mut(dm)?.bytes[ds..ds + n].copy_from_slice(&chunk);
        }
        Ok(())
    }

    fn consume_fuel(&mut self, n: u64) -> Result<(), TrapCode> {
        self.fuel_remaining = self.fuel_remaining.checked_sub(n).ok_or(TrapCode::OutOfFuel)?;
        Ok(())
    }
}

struct Env {
    entries: [(ValId, Val); 16],
    len: usize,
    spill: Vec<(ValId, Val)>,
}

impl Default for Env {
    fn default() -> Self {
        Self { entries: [(ValId(0), Val::I32(0)); 16], len: 0, spill: Vec::new() }
    }
}

impl Env {
    fn len(&self) -> usize {
        self.len
    }
    fn truncate(&mut self, saved: usize) {
        if saved < self.len {
            if (self.len >> 4) != 0 && self.len > 16 {
                self.spill.truncate(saved.saturating_sub(16));
            }
            self.len = saved;
        }
    }
    fn get(&self, id: ValId) -> Result<Val, TrapCode> {
        if self.len <= 3 {
            if self.len >= 3 && self.entries[2].0 == id {
                return Ok(self.entries[2].1);
            }
            if self.len >= 2 && self.entries[1].0 == id {
                return Ok(self.entries[1].1);
            }
            if self.len >= 1 && self.entries[0].0 == id {
                return Ok(self.entries[0].1);
            }
            return Err(TrapCode::Unreachable);
        }
        if (self.len >> 4) != 0 && self.len > 16 {
            let mut j = self.spill.len();
            while j > 0 {
                j -= 1;
                if self.spill[j].0 == id {
                    return Ok(self.spill[j].1);
                }
            }
        }
        let mut i = self.len.min(16);
        while i > 0 {
            i -= 1;
            if self.entries[i & 15].0 == id {
                return Ok(self.entries[i & 15].1);
            }
        }
        Err(TrapCode::Unreachable)
    }
    fn u32(&self, id: ValId) -> Result<u32, TrapCode> { self.get(id)?.as_u32().ok_or(TrapCode::Unreachable) }
    fn set(&mut self, id: ValId, val: Val) {
        if (self.len >> 4) == 0 {
            self.entries[self.len & 15] = (id, val);
            self.len += 1;
        } else {
            self.spill.push((id, val));
            self.len += 1;
        }
    }
    fn bind(&mut self, params: &[(ValId, ValType)], vals: &[Val]) -> Result<(), TrapCode> {
        let n = params.len();
        if n != vals.len() {
            return Err(TrapCode::Unreachable);
        }
        if n <= 2 {
            if n >= 1 {
                if vals[0].val_type() != params[0].1 {
                    return Err(TrapCode::Unreachable);
                }
                self.set(params[0].0, vals[0]);
            }
            if n == 2 {
                if vals[1].val_type() != params[1].1 {
                    return Err(TrapCode::Unreachable);
                }
                self.set(params[1].0, vals[1]);
            }
            return Ok(());
        }
        let mut i = 0;
        while i < n {
            let (id, ty) = params[i];
            let val = vals[i];
            if val.val_type() != ty {
                return Err(TrapCode::Unreachable);
            }
            self.set(id, val);
            i += 1;
        }
        Ok(())
    }
    fn bind_buf(&mut self, params: &[(ValId, ValType)], vals: &ValBuf) -> Result<(), TrapCode> {
        self.bind(params, vals.as_slice())
    }
}

#[derive(Clone)]
pub(crate) struct ValBuf {
    vals: [Val; 8],
    len: usize,
    spill: Vec<Val>,
}

impl ValBuf {
    const EMPTY: Self = Self { vals: [Val::I32(0); 8], len: 0, spill: Vec::new() };

    fn push(&mut self, v: Val) {
        if (self.len >> 3) == 0 {
            self.vals[self.len & 7] = v;
            self.len += 1;
        } else {
            if self.len == 8 {
                self.spill.extend_from_slice(&self.vals);
            }
            self.spill.push(v);
            self.len += 1;
        }
    }
    fn as_slice(&self) -> &[Val] {
        if (self.len >> 3) == 0 || self.len == 8 {
            &self.vals[..self.len.min(8)]
        } else {
            self.spill.as_slice()
        }
    }
    pub(crate) fn first(&self) -> Option<Val> {
        self.as_slice().first().copied()
    }
    fn single_i32(&self) -> Option<i32> {
        match self.as_slice() {
            [v] => v.as_i32(),
            _ => None,
        }
    }
    fn into_vec(self) -> Vec<Val> {
        match self.len {
            0 => Vec::new(),
            1 => vec![self.vals[0]],
            2 => vec![self.vals[0], self.vals[1]],
            n if n > 8 => self.spill,
            n => self.vals[..n].to_vec(),
        }
    }
    fn check_types(&self, tys: &[ValType]) -> Result<(), TrapCode> {
        check_types(self.as_slice(), tys)
    }
    fn check_state(&self, sv: &[(ValId, ValType)]) -> Result<(), TrapCode> {
        let s = self.as_slice();
        if s.len() != sv.len() {
            return Err(TrapCode::Unreachable);
        }
        if s.len() <= 2 {
            if !s.is_empty() && s[0].val_type() != sv[0].1 {
                return Err(TrapCode::Unreachable);
            }
            if s.len() == 2 && s[1].val_type() != sv[1].1 {
                return Err(TrapCode::Unreachable);
            }
            return Ok(());
        }
        let mut i = 0;
        while i < s.len() {
            if s[i].val_type() != sv[i].1 {
                return Err(TrapCode::Unreachable);
            }
            i += 1;
        }
        Ok(())
    }
}

enum Flow {
    Normal(ValBuf),
    Break { depth: u32, values: ValBuf },
    Continue { depth: u32, values: ValBuf },
    Return(ValBuf),
}
struct Ctx<'a> { module: &'a Module, registry: &'a StratumRegistry, depth: u32 }

/// Evaluates an exported or internal function in `module`.
pub fn eval_func(
    module: &Module, registry: &StratumRegistry, func_id: FuncId, args: &[Val], mut initial_heap: HeapState,
) -> Result<(Vec<Val>, HeapState), TrapCode> {
    Ok((eval_func_inner(module, registry, func_id, args, &mut initial_heap, 0)?, initial_heap))
}

/// Evaluates a standalone `Region` with explicit initial SSA bindings.
pub fn eval_region(
    module: &Module, registry: &StratumRegistry, region: &Region, bindings: &[(ValId, Val)], mut initial_heap: HeapState,
) -> Result<(Vec<Val>, HeapState), TrapCode> {
    let vals = eval_region_buf(module, registry, region, bindings, &mut initial_heap)?;
    Ok((vals.into_vec(), initial_heap))
}

pub(crate) fn eval_region_first(
    module: &Module,
    registry: &StratumRegistry,
    region: &Region,
    bindings: &[(ValId, Val)],
    heap: &mut HeapState,
) -> Result<Option<Val>, TrapCode> {
    Ok(eval_region_buf(module, registry, region, bindings, heap)?.first())
}

fn eval_region_buf(
    module: &Module,
    registry: &StratumRegistry,
    region: &Region,
    bindings: &[(ValId, Val)],
    heap: &mut HeapState,
) -> Result<ValBuf, TrapCode> {
    let mut env = Env::default();
    let n = bindings.len();
    if n <= 2 {
        if n > 0 { env.set(bindings[0].0, bindings[0].1); }
        if n > 1 { env.set(bindings[1].0, bindings[1].1); }
    } else {
        for &(id, v) in bindings {
            env.set(id, v);
        }
    }
    let ctx = Ctx { module, registry, depth: 0 };
    match eval_region_flow(&ctx, &mut env, heap, region)? {
        Flow::Normal(v) | Flow::Return(v) => Ok(v),
        _ => Err(TrapCode::Unreachable),
    }
}

fn eval_body_buf(ctx: Ctx<'_>, params: &[(ValId, ValType)], results: &[ValType], body: &Region, args: &[Val], heap: &mut HeapState) -> Result<ValBuf, TrapCode> {
    if ctx.depth >= MAX_CALL_DEPTH { return Err(TrapCode::OutOfFuel); }
    heap.consume_fuel(1)?;
    let mut env = Env::default();
    env.bind(params, args)?;
    let vals = match eval_region_flow(&ctx, &mut env, heap, body)? {
        Flow::Normal(v) | Flow::Return(v) => v,
        _ => return Err(TrapCode::Unreachable),
    };
    vals.check_types(results)?;
    Ok(vals)
}

fn eval_func_inner(module: &Module, registry: &StratumRegistry, func_id: FuncId, args: &[Val], heap: &mut HeapState, depth: u32) -> Result<Vec<Val>, TrapCode> {
    let f = module.func(func_id).ok_or(TrapCode::Unreachable)?;
    Ok(eval_body_buf(Ctx { module, registry, depth }, &f.params, &f.results, &f.body, args, heap)?.into_vec())
}

fn check_types(vals: &[Val], tys: &[ValType]) -> Result<(), TrapCode> {
    if vals.len() != tys.len() {
        return Err(TrapCode::Unreachable);
    }
    if vals.len() <= 2 {
        if !vals.is_empty() && vals[0].val_type() != tys[0] {
            return Err(TrapCode::Unreachable);
        }
        if vals.len() == 2 && vals[1].val_type() != tys[1] {
            return Err(TrapCode::Unreachable);
        }
        return Ok(());
    }
    let mut i = 0;
    while i < vals.len() {
        if vals[i].val_type() != tys[i] {
            return Err(TrapCode::Unreachable);
        }
        i += 1;
    }
    Ok(())
}

fn eval_vals_buf(env: &Env, ids: &[ValId]) -> Result<ValBuf, TrapCode> {
    let mut out = ValBuf::EMPTY;
    match ids {
        [] => {}
        [i0] => out.push(env.get(*i0)?),
        [i0, i1] => {
            out.push(env.get(*i0)?);
            out.push(env.get(*i1)?);
        }
        _ => {
            let mut i = 0;
            while i < ids.len() {
                out.push(env.get(ids[i])?);
                i += 1;
            }
        }
    }
    Ok(out)
}

enum BlockStep<'a> {
    Done(Flow),
    SubRegion {
        next_idx: usize,
        saved: usize,
        results: &'a [(ValId, ValType)],
        sub: &'a Region,
    },
}

fn apply_block_exit(f: Flow, catch_break: bool) -> Result<Flow, TrapCode> {
    if !catch_break {
        return Ok(f);
    }
    match f {
        Flow::Break { depth: 0, values } => Ok(Flow::Normal(values)),
        Flow::Break { depth, values } => Ok(Flow::Break { depth: depth - 1, values }),
        Flow::Continue { depth: 0, .. } => Err(TrapCode::Unreachable),
        Flow::Continue { depth, values } => Ok(Flow::Continue { depth: depth - 1, values }),
        other => Ok(other),
    }
}

fn step_one_stmt<'a>(
    ctx: &Ctx<'_>,
    env: &mut Env,
    heap: &mut HeapState,
    stmt: &'a Stmt,
    next_idx: usize,
    saved: usize,
    catch_break: bool,
) -> Result<Option<BlockStep<'a>>, TrapCode> {
    if let Err(t) = heap.consume_fuel(1) {
        env.truncate(saved);
        return Err(t);
    }
    let take_cond = |c: Option<ValId>, e: &Env| c.map_or(Ok(true), |id| Ok(e.u32(id)? != 0));
    match stmt {
        Stmt::Let { dst, ty, op } => {
            let val = match eval_op(env, heap, op) {
                Ok(v) => v,
                Err(t) => { env.truncate(saved); return Err(t); }
            };
            if val.val_type() != *ty { env.truncate(saved); return Err(TrapCode::Unreachable); }
            env.set(*dst, val);
            Ok(None)
        }
        Stmt::Effect(eff) => {
            if let Err(t) = eval_effect(ctx, env, heap, eff) { env.truncate(saved); return Err(t); }
            Ok(None)
        }
        Stmt::Region { results, region: sub } => {
            Ok(Some(BlockStep::SubRegion { next_idx, saved, results, sub }))
        }
        Stmt::Call { results, target, args } => {
            let a = match eval_vals_buf(env, args) { Ok(v) => v, Err(t) => { env.truncate(saved); return Err(t); } };
            let r = match eval_call(ctx, heap, *target, a.as_slice()) { Ok(v) => v, Err(t) => { env.truncate(saved); return Err(t); } };
            if let Err(t) = env.bind_buf(results, &r) { env.truncate(saved); return Err(t); }
            Ok(None)
        }
        Stmt::Yield(vals) => {
            let v = match eval_vals_buf(env, vals) { Ok(v) => v, Err(t) => { env.truncate(saved); return Err(t); } };
            env.truncate(saved);
            Ok(Some(BlockStep::Done(apply_block_exit(Flow::Normal(v), catch_break)?)))
        }
        Stmt::Break { depth, cond, values } => {
            let taken = match take_cond(*cond, env) { Ok(b) => b, Err(t) => { env.truncate(saved); return Err(t); } };
            if taken {
                let v = match eval_vals_buf(env, values) { Ok(v) => v, Err(t) => { env.truncate(saved); return Err(t); } };
                env.truncate(saved);
                Ok(Some(BlockStep::Done(apply_block_exit(Flow::Break { depth: *depth, values: v }, catch_break)?)))
            } else {
                Ok(None)
            }
        }
        Stmt::Continue { depth, cond, values } => {
            let taken = match take_cond(*cond, env) { Ok(b) => b, Err(t) => { env.truncate(saved); return Err(t); } };
            if taken {
                let v = match eval_vals_buf(env, values) { Ok(v) => v, Err(t) => { env.truncate(saved); return Err(t); } };
                env.truncate(saved);
                Ok(Some(BlockStep::Done(apply_block_exit(Flow::Continue { depth: *depth, values: v }, catch_break)?)))
            } else {
                Ok(None)
            }
        }
        Stmt::Return(vals) => {
            let v = match eval_vals_buf(env, vals) { Ok(v) => v, Err(t) => { env.truncate(saved); return Err(t); } };
            env.truncate(saved);
            Ok(Some(BlockStep::Done(Flow::Return(v))))
        }
    }
}

fn step_block<'a>(
    ctx: &Ctx<'_>,
    env: &mut Env,
    heap: &mut HeapState,
    stmts: &'a [Stmt],
    mut idx: usize,
    saved: usize,
    catch_break: bool,
) -> Result<BlockStep<'a>, TrapCode> {
    if idx == 0 && stmts.len() <= 2 {
        if !stmts.is_empty()
            && let Some(step) = step_one_stmt(ctx, env, heap, &stmts[0], 1, saved, catch_break)?
        {
            return Ok(step);
        }
        if stmts.len() == 2
            && let Some(step) = step_one_stmt(ctx, env, heap, &stmts[1], 2, saved, catch_break)?
        {
            return Ok(step);
        }
        env.truncate(saved);
        return Ok(BlockStep::Done(apply_block_exit(Flow::Normal(ValBuf::EMPTY), catch_break)?));
    }
    while idx < stmts.len() {
        let stmt = &stmts[idx];
        idx += 1;
        if let Some(step) = step_one_stmt(ctx, env, heap, stmt, idx, saved, catch_break)? {
            return Ok(step);
        }
    }
    env.truncate(saved);
    Ok(BlockStep::Done(apply_block_exit(Flow::Normal(ValBuf::EMPTY), catch_break)?))
}

fn eval_region_flow(ctx: &Ctx<'_>, env: &mut Env, heap: &mut HeapState, root: &Region) -> Result<Flow, TrapCode> {
    if let Region::Block(stmts) = root
        && stmts.is_empty()
    {
        return Ok(Flow::Normal(ValBuf::EMPTY));
    }
    enum EvalFrame<'a> {
        Block {
            stmts: &'a [Stmt],
            next_idx: usize,
            saved: usize,
            results: &'a [(ValId, ValType)],
            catch_break: bool,
        },
        IfCheck { results: &'a [ValType] },
        BoundedWait {
            max_iters: u32,
            iter: u32,
            state_vars: &'a [(ValId, ValType)],
            body: &'a Region,
            base_len: usize,
        },
        InvCondWait {
            state_vars: &'a [(ValId, ValType)],
            cond: &'a Region,
            body: &'a Region,
            base_len: usize,
            state: ValBuf,
        },
        InvBodyWait {
            state_vars: &'a [(ValId, ValType)],
            cond: &'a Region,
            body: &'a Region,
            base_len: usize,
        },
    }
    enum Next<'a> {
        Enter { region: &'a Region, as_loop_body: bool },
        BoundedIter { max_iters: u32, iter: u32, state_vars: &'a [(ValId, ValType)], body: &'a Region, base_len: usize, state: ValBuf },
        InvIter { state_vars: &'a [(ValId, ValType)], cond: &'a Region, body: &'a Region, base_len: usize, state: ValBuf },
        Deliver(Flow),
    }

    let mut frames = Stack2::<EvalFrame<'_>>::new();
    let mut cur = 'init: {
        if let Region::Block(stmts) = root
            && stmts.len() <= 2
        {
            match step_block(ctx, env, heap, stmts, 0, env.len(), true)? {
                BlockStep::Done(done) => return Ok(done),
                BlockStep::SubRegion { next_idx, saved, results, sub } => {
                    frames.push(EvalFrame::Block { stmts, next_idx, saved, results, catch_break: true });
                    break 'init Next::Enter { region: sub, as_loop_body: false };
                }
            }
        }
        if let Region::InvariantLoop { init_vars, state_vars, cond, body, .. } = root
            && let (Region::Block(c_stmts), Region::Block(b_stmts)) = (cond.as_ref(), body.as_ref())
        {
            let mut state = eval_vals_buf(env, init_vars)?;
            state.check_state(state_vars)?;
            let base_len = env.len();
            loop {
                if let Err(t) = heap.consume_fuel(1) { env.truncate(base_len); return Err(t); }
                env.truncate(base_len);
                if let Err(t) = env.bind_buf(state_vars, &state) { env.truncate(base_len); return Err(t); }
                match step_block(ctx, env, heap, c_stmts, 0, env.len(), true)? {
                    BlockStep::Done(Flow::Normal(v)) => match v.single_i32() {
                        Some(0) => { env.truncate(base_len); return Ok(Flow::Normal(state)); }
                        Some(_) => {}
                        None => { env.truncate(base_len); return Err(TrapCode::Unreachable); }
                    },
                    BlockStep::Done(Flow::Return(v)) => { env.truncate(base_len); return Ok(Flow::Return(v)); }
                    BlockStep::SubRegion { next_idx, saved, results, sub } => {
                        frames.push(EvalFrame::InvCondWait { state_vars, cond, body, base_len, state });
                        frames.push(EvalFrame::Block { stmts: c_stmts, next_idx, saved, results, catch_break: true });
                        break 'init Next::Enter { region: sub, as_loop_body: false };
                    }
                    _ => { env.truncate(base_len); return Err(TrapCode::Unreachable); }
                }
                match step_block(ctx, env, heap, b_stmts, 0, env.len(), false)? {
                    BlockStep::Done(Flow::Normal(v) | Flow::Continue { depth: 0, values: v }) => {
                        if let Err(t) = v.check_state(state_vars) { env.truncate(base_len); return Err(t); }
                        state = v;
                    }
                    BlockStep::Done(Flow::Break { depth: 0, values }) => { env.truncate(base_len); return Ok(Flow::Normal(values)); }
                    BlockStep::Done(Flow::Break { depth, values }) => { env.truncate(base_len); return Ok(Flow::Break { depth: depth - 1, values }); }
                    BlockStep::Done(Flow::Continue { depth, values }) => { env.truncate(base_len); return Ok(Flow::Continue { depth: depth - 1, values }); }
                    BlockStep::Done(Flow::Return(v)) => { env.truncate(base_len); return Ok(Flow::Return(v)); }
                    BlockStep::SubRegion { next_idx, saved, results, sub } => {
                        frames.push(EvalFrame::InvBodyWait { state_vars, cond, body, base_len });
                        frames.push(EvalFrame::Block { stmts: b_stmts, next_idx, saved, results, catch_break: false });
                        break 'init Next::Enter { region: sub, as_loop_body: false };
                    }
                }
            }
        }
        Next::Enter { region: root, as_loop_body: false }
    };

    loop {
        match cur {
            Next::Deliver(f) => {
                let Some(frame) = frames.pop() else { return Ok(f); };
                match frame {
                    EvalFrame::Block { stmts, next_idx, saved, results, catch_break } => {
                        if let Flow::Normal(vals) = f {
                            if let Err(t) = env.bind_buf(results, &vals) { env.truncate(saved); return Err(t); }
                            match step_block(ctx, env, heap, stmts, next_idx, saved, catch_break)? {
                                BlockStep::Done(done) => cur = Next::Deliver(done),
                                BlockStep::SubRegion { next_idx: ni, saved: sv, results: res, sub } => {
                                    frames.push(EvalFrame::Block { stmts, next_idx: ni, saved: sv, results: res, catch_break });
                                    cur = Next::Enter { region: sub, as_loop_body: false };
                                }
                            }
                        } else {
                            env.truncate(saved);
                            cur = Next::Deliver(apply_block_exit(f, catch_break)?);
                        }
                    }
                    EvalFrame::IfCheck { results } => {
                        if let Flow::Normal(ref v) = f { v.check_types(results)?; }
                        cur = Next::Deliver(f);
                    }
                    EvalFrame::BoundedWait { max_iters, iter, state_vars, body, base_len } => match f {
                        Flow::Normal(v) | Flow::Break { depth: 0, values: v } => {
                            env.truncate(base_len);
                            cur = Next::Deliver(Flow::Normal(v));
                        }
                        Flow::Break { depth, values } => {
                            env.truncate(base_len);
                            cur = Next::Deliver(Flow::Break { depth: depth - 1, values });
                        }
                        Flow::Continue { depth: 0, values } => {
                            if let Err(t) = values.check_state(state_vars) { env.truncate(base_len); return Err(t); }
                            cur = Next::BoundedIter { max_iters, iter: iter + 1, state_vars, body, base_len, state: values };
                        }
                        Flow::Continue { depth, values } => {
                            env.truncate(base_len);
                            cur = Next::Deliver(Flow::Continue { depth: depth - 1, values });
                        }
                        Flow::Return(v) => { env.truncate(base_len); cur = Next::Deliver(Flow::Return(v)); }
                    },
                    EvalFrame::InvCondWait { state_vars, cond, body, base_len, state } => match f {
                        Flow::Normal(v) => match v.single_i32() {
                            Some(0) => { env.truncate(base_len); cur = Next::Deliver(Flow::Normal(state)); }
                            Some(_) => {
                                frames.push(EvalFrame::InvBodyWait { state_vars, cond, body, base_len });
                                cur = Next::Enter { region: body, as_loop_body: true };
                            }
                            None => { env.truncate(base_len); return Err(TrapCode::Unreachable); }
                        },
                        Flow::Return(v) => { env.truncate(base_len); cur = Next::Deliver(Flow::Return(v)); }
                        _ => { env.truncate(base_len); return Err(TrapCode::Unreachable); }
                    },
                    EvalFrame::InvBodyWait { state_vars, cond, body, base_len } => match f {
                        Flow::Normal(v) | Flow::Continue { depth: 0, values: v } => {
                            if let Err(t) = v.check_state(state_vars) { env.truncate(base_len); return Err(t); }
                            cur = Next::InvIter { state_vars, cond, body, base_len, state: v };
                        }
                        Flow::Break { depth: 0, values } => { env.truncate(base_len); cur = Next::Deliver(Flow::Normal(values)); }
                        Flow::Break { depth, values } => { env.truncate(base_len); cur = Next::Deliver(Flow::Break { depth: depth - 1, values }); }
                        Flow::Continue { depth, values } => { env.truncate(base_len); cur = Next::Deliver(Flow::Continue { depth: depth - 1, values }); }
                        Flow::Return(v) => { env.truncate(base_len); cur = Next::Deliver(Flow::Return(v)); }
                    },
                }
            }
            Next::Enter { region, as_loop_body } => match region {
                Region::Block(stmts) => match step_block(ctx, env, heap, stmts, 0, env.len(), !as_loop_body)? {
                    BlockStep::Done(done) => cur = Next::Deliver(done),
                    BlockStep::SubRegion { next_idx, saved, results, sub } => {
                        frames.push(EvalFrame::Block { stmts, next_idx, saved, results, catch_break: !as_loop_body });
                        cur = Next::Enter { region: sub, as_loop_body: false };
                    }
                },
                Region::IfElse { cond, then_region, else_region, results } => {
                    let b = if env.u32(*cond)? != 0 { then_region } else { else_region };
                    frames.push(EvalFrame::IfCheck { results });
                    cur = Next::Enter { region: b, as_loop_body: false };
                }
                Region::BoundedLoop { max_iters, init_vars, state_vars, body } => {
                    let state = eval_vals_buf(env, init_vars)?;
                    state.check_state(state_vars)?;
                    cur = Next::BoundedIter { max_iters: *max_iters, iter: 0, state_vars, body, base_len: env.len(), state };
                }
                Region::InvariantLoop { init_vars, state_vars, cond, body, .. } => {
                    let state = eval_vals_buf(env, init_vars)?;
                    state.check_state(state_vars)?;
                    cur = Next::InvIter { state_vars, cond, body, base_len: env.len(), state };
                }
            },
            Next::BoundedIter { max_iters, iter, state_vars, body, base_len, state } => {
                if iter >= max_iters { env.truncate(base_len); return Err(TrapCode::OutOfFuel); }
                if let Err(t) = heap.consume_fuel(1) { env.truncate(base_len); return Err(t); }
                env.truncate(base_len);
                if let Err(t) = env.bind_buf(state_vars, &state) { env.truncate(base_len); return Err(t); }
                frames.push(EvalFrame::BoundedWait { max_iters, iter, state_vars, body, base_len });
                cur = Next::Enter { region: body, as_loop_body: true };
            }
            Next::InvIter { state_vars, cond, body, base_len, state } => {
                if let Err(t) = heap.consume_fuel(1) { env.truncate(base_len); return Err(t); }
                env.truncate(base_len);
                if let Err(t) = env.bind_buf(state_vars, &state) { env.truncate(base_len); return Err(t); }
                frames.push(EvalFrame::InvCondWait { state_vars, cond, body, base_len, state });
                cur = Next::Enter { region: cond, as_loop_body: false };
            }
        }
    }
}

#[inline(never)]
fn eval_op(env: &Env, heap: &mut HeapState, op: &Op) -> Result<Val, TrapCode> {
    match op {
        Op::ConstI32(v) => Ok(Val::I32(*v)), Op::ConstI64(v) => Ok(Val::I64(*v)), Op::Copy(id) => env.get(*id),
        Op::Select { cond, true_val, false_val } => {
            let (c, t, f) = (env.u32(*cond)?, env.get(*true_val)?, env.get(*false_val)?);
            if t.val_type() != f.val_type() { Err(TrapCode::Unreachable) } else { Ok(if c != 0 { t } else { f }) }
        }
        Op::GlobalGet(gid) => heap.globals.get(gid.0 as usize).copied().ok_or(TrapCode::Unreachable),
        Op::Un(u, a) => eval_unop(*u, env.get(*a)?),
        Op::Bin(b, l, r) => eval_binop(*b, env.get(*l)?, env.get(*r)?),
        Op::Load { mem, addr, offset, width, signed, result_ty } => heap.memory(*mem)?.load(env.u32(*addr)?, *offset, *width, *signed, *result_ty),
        Op::MemorySize(mem) => Ok(Val::I32(heap.memory(*mem)?.size_pages() as i32)),
        Op::MemoryGrow { mem, delta } => Ok(Val::I32(heap.memory_mut(*mem)?.grow(env.u32(*delta)?))),
    }
}

#[inline(never)]
fn eval_effect(ctx: &Ctx<'_>, env: &Env, heap: &mut HeapState, eff: &EffectOp) -> Result<(), TrapCode> {
    match eff {
        EffectOp::Store { mem, addr, offset, width, val } => heap.memory_mut(*mem)?.store(env.u32(*addr)?, *offset, *width, env.get(*val)?),
        EffectOp::MemoryCopy { dst_mem, src_mem, dst, src, len } => heap.memory_copy(*dst_mem, *src_mem, env.u32(*dst)?, env.u32(*src)?, env.u32(*len)?),
        EffectOp::MemoryFill { mem, dst, val, len } => heap.memory_mut(*mem)?.fill(env.u32(*dst)?, env.u32(*val)? as u8, env.u32(*len)?),
        EffectOp::GlobalSet { id, val } => {
            let (gdef, v) = (ctx.module.global(*id).ok_or(TrapCode::Unreachable)?, env.get(*val)?);
            if !gdef.mutable || v.val_type() != gdef.ty { return Err(TrapCode::Unreachable); }
            *heap.globals.get_mut(id.0 as usize).ok_or(TrapCode::Unreachable)? = v;
            Ok(())
        }
        EffectOp::Trap(code) => Err(*code), EffectOp::Nop => Ok(()),
    }
}

#[inline(never)]
fn eval_call(ctx: &Ctx<'_>, heap: &mut HeapState, target: CallTarget, args: &[Val]) -> Result<ValBuf, TrapCode> {
    match target {
        CallTarget::Func(fid) => {
            if ctx.module.funcs.is_empty() {
                return Err(TrapCode::Unreachable);
            }
            let f = ctx.module.func(fid).ok_or(TrapCode::Unreachable)?;
            eval_body_buf(Ctx { module: ctx.module, registry: ctx.registry, depth: ctx.depth + 1 }, &f.params, &f.results, &f.body, args, heap)
        }
        CallTarget::Stratum(sid) => {
            if ctx.registry.promoted().is_empty() && ctx.registry.candidates().is_empty() {
                return Err(TrapCode::Unreachable);
            }
            let op = ctx.registry.get_op(sid).ok_or(TrapCode::Unreachable)?;
            eval_body_buf(Ctx { module: ctx.module, registry: ctx.registry, depth: ctx.depth + 1 }, &op.params, &op.results, &op.body, args, heap)
        }
        CallTarget::Host(hid) => {
            if ctx.module.host_contracts.is_empty() {
                return Err(TrapCode::HostContractViolation);
            }
            let v = eval_host_call(ctx, heap, hid, args)?;
            let mut out = ValBuf::EMPTY;
            let mut i = 0;
            while i < v.len() {
                out.push(v[i]);
                i += 1;
            }
            Ok(out)
        }
    }
}

fn eval_host_call(ctx: &Ctx<'_>, heap: &mut HeapState, hid: HostCallId, args: &[Val]) -> Result<Vec<Val>, TrapCode> {
    let bound = |b: SliceBound| match b {
        SliceBound::Const(c) => Ok(c as u64),
        SliceBound::Arg(i) => args.get(i as usize).and_then(|v| v.as_u32()).map(|u| u as u64).ok_or(TrapCode::HostContractViolation),
    };
    let hc = ctx.module.host_contract(hid).ok_or(TrapCode::HostContractViolation)?;
    if !validate_read_only_with_registry(&hc.precondition, ctx.registry)
        || !validate_read_only_with_registry(&hc.postcondition, ctx.registry)
    {
        return Err(TrapCode::HostContractViolation);
    }
    let mut env = Env::default();
    env.bind(&hc.params, args).map_err(|_| TrapCode::HostContractViolation)?;
    let pred = |r: &Region, e: &mut Env, h: &HeapState| {
        matches!(eval_region_flow(ctx, e, &mut h.clone(), r), Ok(Flow::Normal(v)) if v.single_i32().is_some_and(|x| x != 0))
    };
    if !pred(&hc.precondition, &mut env, heap) { return Err(TrapCode::HostContractViolation); }
    for &(mid, r) in hc.read_footprints.iter().chain(&hc.write_footprints) {
        if bound(r.base)?.checked_add(bound(r.len)?).ok_or(TrapCode::OutOfBoundsMem)? > heap.memory(mid)?.bytes.len() as u64 {
            return Err(TrapCode::OutOfBoundsMem);
        }
    }
    let before = heap.memories.clone();
    let res = match &hc.sim_body {
        Some(body) => match eval_region_flow(ctx, &mut env, heap, body)? {
            Flow::Normal(v) | Flow::Return(v) => v.into_vec(),
            _ => return Err(TrapCode::HostContractViolation),
        },
        None => hc.results.iter().map(|(_, t)| Val::default_for(*t)).collect(),
    };
    let hc_res_tys: Vec<ValType> = hc.results.iter().map(|&(_, t)| t).collect();
    check_types(&res, &hc_res_tys).map_err(|_| TrapCode::HostContractViolation)?;
    let mut writes = Vec::with_capacity(hc.write_footprints.len());
    for &(mid, r) in &hc.write_footprints {
        let b = bound(r.base)? as usize;
        writes.push((mid, b, b + bound(r.len)? as usize));
    }
    for (prev, cur) in before.iter().zip(&heap.memories) {
        let mut rs: Vec<(usize, usize)> = writes.iter().filter(|w| w.0 == cur.id).map(|w| (w.1, w.2)).collect();
        for i in 1..rs.len() {
            let mut j = i;
            while j > 0 && rs[j - 1] > rs[j] { rs.swap(j - 1, j); j -= 1; }
        }
        let mut pos = 0usize;
        for (s, e) in rs {
            if s > pos && prev.bytes[pos..s] != cur.bytes[pos..s] { return Err(TrapCode::HostContractViolation); }
            pos = pos.max(e);
        }
        if prev.bytes[pos..] != cur.bytes[pos..] { return Err(TrapCode::HostContractViolation); }
    }
    env.bind(&hc.results, &res).map_err(|_| TrapCode::HostContractViolation)?;
    if !pred(&hc.postcondition, &mut env, heap) { return Err(TrapCode::HostContractViolation); }
    Ok(res)
}

fn eval_unop(op: UnOp, v: Val) -> Result<Val, TrapCode> {
    Ok(match (op, v) {
        (UnOp::I32Eqz, Val::I32(x)) => Val::I32(i32::from(x == 0)), (UnOp::I64Eqz, Val::I64(x)) => Val::I32(i32::from(x == 0)),
        (UnOp::I32Clz, Val::I32(x)) => Val::I32(x.leading_zeros() as i32), (UnOp::I32Ctz, Val::I32(x)) => Val::I32(x.trailing_zeros() as i32),
        (UnOp::I32Popcnt, Val::I32(x)) => Val::I32(x.count_ones() as i32), (UnOp::I64Clz, Val::I64(x)) => Val::I64(x.leading_zeros() as i64),
        (UnOp::I64Ctz, Val::I64(x)) => Val::I64(x.trailing_zeros() as i64), (UnOp::I64Popcnt, Val::I64(x)) => Val::I64(x.count_ones() as i64),
        (UnOp::I32WrapI64, Val::I64(x)) => Val::I32(x as i32), (UnOp::I64ExtendI32S, Val::I32(x)) => Val::I64(x as i64),
        (UnOp::I64ExtendI32U, Val::I32(x)) => Val::I64((x as u32) as i64), (UnOp::I32Extend8S, Val::I32(x)) => Val::I32((x as i8) as i32),
        (UnOp::I32Extend16S, Val::I32(x)) => Val::I32((x as i16) as i32), (UnOp::I64Extend8S, Val::I64(x)) => Val::I64((x as i8) as i64),
        (UnOp::I64Extend16S, Val::I64(x)) => Val::I64((x as i16) as i64), (UnOp::I64Extend32S, Val::I64(x)) => Val::I64((x as i32) as i64),
        _ => return Err(TrapCode::Unreachable),
    })
}

macro_rules! int_ops {
    ($a:expr, $c:expr, $s:ty, $u:ty, $w:path, $bits:expr, $op:expr;
     $eq:pat, $ne:pat, $lts:pat, $ltu:pat, $gts:pat, $gtu:pat, $les:pat, $leu:pat, $ges:pat, $geu:pat,
     $add:pat, $sub:pat, $mul:pat, $divs:pat, $divu:pat, $rems:pat, $remu:pat,
     $and:pat, $or:pat, $xor:pat, $shl:pat, $shrs:pat, $shru:pat, $rotl:pat, $rotr:pat) => {{
        let b = |cond: bool| Val::I32(i32::from(cond));
        Ok(match $op {
            $eq => b($a == $c), $ne => b($a != $c), $lts => b($a < $c), $ltu => b(($a as $u) < ($c as $u)),
            $gts => b($a > $c), $gtu => b(($a as $u) > ($c as $u)), $les => b($a <= $c), $leu => b(($a as $u) <= ($c as $u)),
            $ges => b($a >= $c), $geu => b(($a as $u) >= ($c as $u)),
            $add => $w($a.wrapping_add($c)), $sub => $w($a.wrapping_sub($c)), $mul => $w($a.wrapping_mul($c)),
            $divs if $c == 0 => return Err(TrapCode::DivByZero),
            $divs if $a == <$s>::MIN && $c == -1 => return Err(TrapCode::IntOverflow),
            $divs => $w($a.wrapping_div($c)),
            $divu => $w(($a as $u).checked_div($c as $u).ok_or(TrapCode::DivByZero)? as $s),
            $rems if $c == 0 => return Err(TrapCode::DivByZero),
            $rems if $a == <$s>::MIN && $c == -1 => $w(0),
            $rems => $w($a.wrapping_rem($c)),
            $remu => $w(($a as $u).checked_rem($c as $u).ok_or(TrapCode::DivByZero)? as $s),
            $and => $w($a & $c), $or => $w($a | $c), $xor => $w($a ^ $c),
            $shl => $w($a.wrapping_shl($c as u32)), $shrs => $w($a.wrapping_shr($c as u32)),
            $shru => $w(($a as $u).wrapping_shr($c as u32) as $s),
            $rotl => $w(($a as $u).rotate_left(($c as u32) & $bits) as $s),
            $rotr => $w(($a as $u).rotate_right(($c as u32) & $bits) as $s),
            _ => return Err(TrapCode::Unreachable),
        })
    }};
}

pub(crate) fn eval_binop(op: BinOp, l: Val, r: Val) -> Result<Val, TrapCode> {
    use BinOp::*;
    match (l, r) {
        (Val::I32(a), Val::I32(c)) => int_ops!(a, c, i32, u32, Val::I32, 31, op;
            I32Eq, I32Ne, I32LtS, I32LtU, I32GtS, I32GtU, I32LeS, I32LeU, I32GeS, I32GeU, I32Add, I32Sub, I32Mul,
            I32DivS, I32DivU, I32RemS, I32RemU, I32And, I32Or, I32Xor, I32Shl, I32ShrS, I32ShrU, I32Rotl, I32Rotr),
        (Val::I64(a), Val::I64(c)) => int_ops!(a, c, i64, u64, Val::I64, 63, op;
            I64Eq, I64Ne, I64LtS, I64LtU, I64GtS, I64GtU, I64LeS, I64LeU, I64GeS, I64GeU, I64Add, I64Sub, I64Mul,
            I64DivS, I64DivU, I64RemS, I64RemU, I64And, I64Or, I64Xor, I64Shl, I64ShrS, I64ShrU, I64Rotl, I64Rotr),
        _ => Err(TrapCode::Unreachable),
    }
}
