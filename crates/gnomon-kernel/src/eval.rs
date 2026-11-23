//! Deterministic reference interpreter for `GnomonIR`.

use alloc::{boxed::Box, vec, vec::Vec};
use crate::ir::*;
use crate::registry::StratumRegistry;
use crate::vc::validate_read_only_with_registry;

pub const WASM_PAGE_SIZE: usize = 65_536;
pub const MAX_WASM_PAGES: u32 = 65_536;
pub const MAX_CALL_DEPTH: u32 = 64;
const MAX_REGION_DEPTH: u32 = 64;

/// Concrete state of one Wasm linear memory.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MemoryState {
    pub id: MemId,
    pub bytes: Vec<u8>,
    pub max_pages: Option<u32>,
}

impl MemoryState {
    fn ea_end(&self, addr: u32, offset: u32, len: u64) -> Result<usize, TrapCode> {
        let ea = (addr as u64).checked_add(offset as u64).ok_or(TrapCode::OutOfBoundsMem)?;
        let end = ea.checked_add(len).ok_or(TrapCode::OutOfBoundsMem)?;
        if end > self.bytes.len() as u64 {
            Err(TrapCode::OutOfBoundsMem)
        } else {
            Ok(ea as usize)
        }
    }

    pub fn load(
        &self,
        addr: u32,
        offset: u32,
        w: MemWidth,
        signed: bool,
        ty: ValType,
    ) -> Result<Val, TrapCode> {
        let s = &self.bytes[self.ea_end(addr, offset, w.bytes())?..][..w.bytes() as usize];
        let v: i64 = match (w, signed) {
            (MemWidth::B1, false) => s[0] as i64,
            (MemWidth::B1, true) => (s[0] as i8) as i64,
            (MemWidth::B2, false) => u16::from_le_bytes([s[0], s[1]]) as i64,
            (MemWidth::B2, true) => i16::from_le_bytes([s[0], s[1]]) as i64,
            (MemWidth::B4, false) => u32::from_le_bytes([s[0], s[1], s[2], s[3]]) as i64,
            (MemWidth::B4, true) => i32::from_le_bytes([s[0], s[1], s[2], s[3]]) as i64,
            (MemWidth::B8, _) if ty == ValType::I64 => {
                u64::from_le_bytes([s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7]]) as i64
            }
            (MemWidth::B8, _) => return Err(TrapCode::Unreachable),
        };
        Ok(match ty {
            ValType::I32 => Val::I32(v as i32),
            ValType::I64 => Val::I64(v),
        })
    }

    pub fn store(&mut self, addr: u32, offset: u32, w: MemWidth, val: Val) -> Result<(), TrapCode> {
        let start = self.ea_end(addr, offset, w.bytes())?;
        let raw = match val {
            Val::I32(v) if w != MemWidth::B8 => v as u32 as u64,
            Val::I64(v) => v as u64,
            Val::I32(_) => return Err(TrapCode::Unreachable),
        };
        self.bytes[start..start + w.bytes() as usize]
            .copy_from_slice(&raw.to_le_bytes()[..w.bytes() as usize]);
        Ok(())
    }

    pub fn fill(&mut self, dst: u32, val: u8, len: u32) -> Result<(), TrapCode> {
        let start = self.ea_end(dst, 0, len as u64)?;
        self.bytes[start..start + len as usize].fill(val);
        Ok(())
    }

    pub fn size_pages(&self) -> u32 {
        (self.bytes.len() / WASM_PAGE_SIZE) as u32
    }

    pub fn grow(&mut self, delta: u32) -> i32 {
        let cur = self.size_pages();
        let limit = self.max_pages.unwrap_or(MAX_WASM_PAGES).min(MAX_WASM_PAGES);
        let Some(len) = cur
            .checked_add(delta)
            .filter(|&n| n <= limit)
            .and_then(|n| (n as usize).checked_mul(WASM_PAGE_SIZE))
        else {
            return -1;
        };
        self.bytes.resize(len, 0);
        cur as i32
    }
}

/// Complete deterministic VM memory, global, and fuel state.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HeapState {
    pub memories: Vec<MemoryState>,
    pub globals: Vec<Val>,
    pub fuel_remaining: u64,
}

impl HeapState {
    pub fn from_module(module: &Module, fuel: u64) -> Result<Self, TrapCode> {
        let mut memories = Vec::with_capacity(module.memories.len());
        for m in &module.memories {
            if m.min_pages > m.max_pages.unwrap_or(MAX_WASM_PAGES).min(MAX_WASM_PAGES) {
                return Err(TrapCode::OutOfBoundsMem);
            }
            let len = (m.min_pages as usize)
                .checked_mul(WASM_PAGE_SIZE)
                .ok_or(TrapCode::OutOfBoundsMem)?;
            let mut bytes = vec![0u8; len];
            for (off, data) in &m.init_data {
                let end = (*off as u64)
                    .checked_add(data.len() as u64)
                    .ok_or(TrapCode::OutOfBoundsMem)?;
                if end > bytes.len() as u64 {
                    return Err(TrapCode::OutOfBoundsMem);
                }
                bytes[*off as usize..end as usize].copy_from_slice(data);
            }
            memories.push(MemoryState { id: m.id, bytes, max_pages: m.max_pages });
        }
        Ok(Self {
            memories,
            globals: module.globals.iter().map(|g| g.init).collect(),
            fuel_remaining: fuel,
        })
    }

    pub fn memory(&self, id: MemId) -> Result<&MemoryState, TrapCode> {
        self.memories.iter().find(|m| m.id == id).ok_or(TrapCode::OutOfBoundsMem)
    }

    pub fn memory_mut(&mut self, id: MemId) -> Result<&mut MemoryState, TrapCode> {
        self.memories.iter_mut().find(|m| m.id == id).ok_or(TrapCode::OutOfBoundsMem)
    }

    pub fn memory_copy(
        &mut self,
        dm: MemId,
        sm: MemId,
        dst: u32,
        src: u32,
        len: u32,
    ) -> Result<(), TrapCode> {
        let ds = self.memory(dm)?.ea_end(dst, 0, len as u64)?;
        let ss = self.memory(sm)?.ea_end(src, 0, len as u64)?;
        let n = len as usize;
        if dm == sm {
            self.memory_mut(dm)?.bytes.copy_within(ss..ss + n, ds);
        } else {
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

/// `Copy` value tuple avoiding heap allocation for 0..=4 values.
#[derive(Clone, Copy, Debug)]
enum SmallVals {
    Inline([Val; 4], u8),
    Pool(u32),
}

impl SmallVals {
    const EMPTY: Self = Self::Inline([Val::I32(0); 4], 0);
}

#[derive(Clone, Copy)]
enum Flow {
    Normal(SmallVals),
    Break { depth: u32, values: SmallVals },
    Continue { depth: u32, values: SmallVals },
    Return(SmallVals),
}

const ENV_INLINE: usize = 16;
const ENV_UNDEF: u8 = 0;
const ENV_I32: u8 = 1;
const ENV_I64: u8 = 2;

struct Env {
    slot_val: [u64; ENV_INLINE],
    slot_tag: [u8; ENV_INLINE],
    trail_val: [u64; ENV_INLINE],
    trail_meta: [u8; ENV_INLINE],
    inline_len: usize,
    total_len: usize,
    spill: Vec<(ValId, Val)>,
}

impl Env {
    fn with_cap(_cap: usize) -> Self {
        Self {
            slot_val: [0; ENV_INLINE],
            slot_tag: [ENV_UNDEF; ENV_INLINE],
            trail_val: [0; ENV_INLINE],
            trail_meta: [0; ENV_INLINE],
            inline_len: 0,
            total_len: 0,
            spill: Vec::new(),
        }
    }

    fn from_bindings_cap(bindings: &[(ValId, Val)], extra: usize) -> Self {
        let mut env = Self::with_cap(bindings.len().saturating_add(extra));
        let mut i = 0;
        while i < bindings.len() {
            let _ = env.push(bindings[i].0, bindings[i].1);
            i += 1;
        }
        env
    }

    fn len(&self) -> usize {
        self.total_len
    }

    #[cold]
    #[inline(never)]
    fn truncate_spill(&mut self, saved: usize) {
        self.spill.truncate(saved.saturating_sub(self.inline_len));
    }

    fn truncate(&mut self, saved: usize) {
        if !self.spill.is_empty() {
            self.truncate_spill(saved);
        }
        while self.inline_len > saved {
            self.inline_len -= 1;
            let meta = self.trail_meta[self.inline_len];
            let idx = (meta >> 4) as usize;
            self.slot_tag[idx] = meta & 0x0f;
            self.slot_val[idx] = self.trail_val[self.inline_len];
        }
        self.total_len = saved;
    }

    #[cold]
    #[inline(never)]
    fn push_spill(&mut self, id: ValId, val: Val) {
        self.spill.push((id, val));
    }

    fn push(&mut self, id: ValId, val: Val) -> Result<(), TrapCode> {
        let idx = id.0 as usize;
        if self.spill.is_empty() && self.inline_len < ENV_INLINE && idx < ENV_INLINE {
            let (tag, bits) = match val {
                Val::I32(x) => (ENV_I32, x as u32 as u64),
                Val::I64(x) => (ENV_I64, x as u64),
            };
            self.trail_meta[self.inline_len] = ((idx as u8) << 4) | self.slot_tag[idx];
            self.trail_val[self.inline_len] = self.slot_val[idx];
            self.slot_tag[idx] = tag;
            self.slot_val[idx] = bits;
            self.inline_len += 1;
        } else {
            self.push_spill(id, val);
        }
        self.total_len += 1;
        Ok(())
    }

    #[cold]
    #[inline(never)]
    fn get_spill(&self, id: ValId) -> Option<Val> {
        let mut i = self.spill.len();
        while i > 0 {
            i -= 1;
            if self.spill[i].0 == id {
                return Some(self.spill[i].1);
            }
        }
        None
    }

    fn get(&self, id: ValId) -> Result<Val, TrapCode> {
        if !self.spill.is_empty()
            && let Some(v) = self.get_spill(id)
        {
            return Ok(v);
        }
        let idx = id.0 as usize;
        if idx < ENV_INLINE {
            match self.slot_tag[idx] {
                ENV_I32 => return Ok(Val::I32(self.slot_val[idx] as u32 as i32)),
                ENV_I64 => return Ok(Val::I64(self.slot_val[idx] as i64)),
                _ => {}
            }
        }
        Err(TrapCode::Unreachable)
    }

    fn u32(&self, id: ValId) -> Result<u32, TrapCode> {
        self.get(id)?.as_u32().ok_or(TrapCode::Unreachable)
    }
}

#[derive(Default)]
struct ValPool(Vec<Box<[Val]>>);

impl ValPool {
    fn intern_slice(&mut self, vals: &[Val]) -> SmallVals {
        if vals.len() <= 4 {
            let mut a = [Val::I32(0); 4];
            let mut i = 0;
            while i < vals.len() {
                a[i] = vals[i];
                i += 1;
            }
            SmallVals::Inline(a, vals.len() as u8)
        } else {
            let id = self.0.len() as u32;
            self.0.push(vals.to_vec().into_boxed_slice());
            SmallVals::Pool(id)
        }
    }

    fn eval_span(&mut self, env: &Env, reg: &Region, span: Span) -> Result<SmallVals, TrapCode> {
        match span.len {
            0 => Ok(SmallVals::EMPTY),
            1 => {
                let mut a = [Val::I32(0); 4];
                a[0] = env.get(reg.try_val(span, 0).ok_or(TrapCode::Unreachable)?)?;
                Ok(SmallVals::Inline(a, 1))
            }
            2 => {
                let mut a = [Val::I32(0); 4];
                a[0] = env.get(reg.try_val(span, 0).ok_or(TrapCode::Unreachable)?)?;
                a[1] = env.get(reg.try_val(span, 1).ok_or(TrapCode::Unreachable)?)?;
                Ok(SmallVals::Inline(a, 2))
            }
            3 => {
                let mut a = [Val::I32(0); 4];
                a[0] = env.get(reg.try_val(span, 0).ok_or(TrapCode::Unreachable)?)?;
                a[1] = env.get(reg.try_val(span, 1).ok_or(TrapCode::Unreachable)?)?;
                a[2] = env.get(reg.try_val(span, 2).ok_or(TrapCode::Unreachable)?)?;
                Ok(SmallVals::Inline(a, 3))
            }
            4 => {
                let mut a = [Val::I32(0); 4];
                a[0] = env.get(reg.try_val(span, 0).ok_or(TrapCode::Unreachable)?)?;
                a[1] = env.get(reg.try_val(span, 1).ok_or(TrapCode::Unreachable)?)?;
                a[2] = env.get(reg.try_val(span, 2).ok_or(TrapCode::Unreachable)?)?;
                a[3] = env.get(reg.try_val(span, 3).ok_or(TrapCode::Unreachable)?)?;
                Ok(SmallVals::Inline(a, 4))
            }
            n => {
                let mut v = vec![Val::I32(0); n as usize].into_boxed_slice();
                let mut i = 0;
                while i < n {
                    v[i as usize] = env.get(reg.try_val(span, i).ok_or(TrapCode::Unreachable)?)?;
                    i += 1;
                }
                let id = self.0.len() as u32;
                self.0.push(v);
                Ok(SmallVals::Pool(id))
            }
        }
    }

    fn len(&self, sv: SmallVals) -> usize {
        match sv {
            SmallVals::Inline(_, n) => n as usize,
            SmallVals::Pool(id) => self.0[id as usize].len(),
        }
    }

    fn get(&self, sv: SmallVals, idx: usize) -> Val {
        match sv {
            SmallVals::Inline(a, _) => a[idx],
            SmallVals::Pool(id) => self.0[id as usize][idx],
        }
    }

    fn first(&self, sv: SmallVals) -> Option<Val> {
        if self.len(sv) == 0 { None } else { Some(self.get(sv, 0)) }
    }

    fn as_single_i32(&self, sv: SmallVals) -> Option<i32> {
        match sv {
            SmallVals::Inline(a, 1) => a[0].as_i32(),
            _ => None,
        }
    }

    fn to_vec(&self, sv: SmallVals) -> Vec<Val> {
        match sv {
            SmallVals::Inline(a, n) => a[..n as usize].to_vec(),
            SmallVals::Pool(id) => self.0[id as usize].to_vec(),
        }
    }

    fn check_types(&self, sv: SmallVals, tys: &[ValType]) -> Result<(), TrapCode> {
        if self.len(sv) != tys.len() {
            return Err(TrapCode::Unreachable);
        }
        let mut i = 0;
        while i < tys.len() {
            if self.get(sv, i).val_type() != tys[i] {
                return Err(TrapCode::Unreachable);
            }
            i += 1;
        }
        Ok(())
    }

    fn check_tys_span(&self, sv: SmallVals, reg: &Region, span: Span) -> Result<(), TrapCode> {
        if self.len(sv) != span.len_usize() {
            return Err(TrapCode::Unreachable);
        }
        let mut i = 0;
        while i < span.len {
            let expected = reg.try_ty(span, i).ok_or(TrapCode::Unreachable)?;
            if self.get(sv, i as usize).val_type() != expected {
                return Err(TrapCode::Unreachable);
            }
            i += 1;
        }
        Ok(())
    }

    fn check_vars_span(&self, sv: SmallVals, reg: &Region, span: Span) -> Result<(), TrapCode> {
        if self.len(sv) != span.len_usize() {
            return Err(TrapCode::Unreachable);
        }
        let mut i = 0;
        while i < span.len {
            let (_, expected) = reg.try_var(span, i).ok_or(TrapCode::Unreachable)?;
            if self.get(sv, i as usize).val_type() != expected {
                return Err(TrapCode::Unreachable);
            }
            i += 1;
        }
        Ok(())
    }

    fn bind_params(
        &self,
        env: &mut Env,
        params: &[(ValId, ValType)],
        sv: SmallVals,
    ) -> Result<(), TrapCode> {
        if params.len() != self.len(sv) {
            return Err(TrapCode::Unreachable);
        }
        let mut i = 0;
        while i < params.len() {
            let v = self.get(sv, i);
            if v.val_type() != params[i].1 {
                return Err(TrapCode::Unreachable);
            }
            env.push(params[i].0, v)?;
            i += 1;
        }
        Ok(())
    }

    fn bind_span(
        &self,
        env: &mut Env,
        reg: &Region,
        vars: Span,
        sv: SmallVals,
    ) -> Result<(), TrapCode> {
        if vars.len_usize() != self.len(sv) {
            return Err(TrapCode::Unreachable);
        }
        let mut i = 0;
        while i < vars.len {
            let (id, ty) = reg.try_var(vars, i).ok_or(TrapCode::Unreachable)?;
            let v = self.get(sv, i as usize);
            if v.val_type() != ty {
                return Err(TrapCode::Unreachable);
            }
            env.push(id, v)?;
            i += 1;
        }
        Ok(())
    }
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

/// Evaluates an exported or internal function in `module`.
pub fn eval_func(
    module: &Module,
    registry: &StratumRegistry,
    func_id: FuncId,
    args: &[Val],
    mut initial_heap: HeapState,
) -> Result<(Vec<Val>, HeapState), TrapCode> {
    let f = module.func(func_id).ok_or(TrapCode::Unreachable)?;
    let mut vp = ValPool::default();
    let arg_sv = vp.intern_slice(args);
    let ret_sv = eval_call_body(
        module,
        registry,
        &f.params,
        &f.results,
        &f.body,
        arg_sv,
        &mut vp,
        &mut initial_heap,
        0,
        true,
    )?;
    Ok((vp.to_vec(ret_sv), initial_heap))
}

/// Evaluates a standalone `Region` with explicit initial SSA bindings.
pub fn eval_region(
    module: &Module,
    registry: &StratumRegistry,
    region: &Region,
    bindings: &[(ValId, Val)],
    mut initial_heap: HeapState,
) -> Result<(Vec<Val>, HeapState), TrapCode> {
    let mut vp = ValPool::default();
    let mut env = Env::from_bindings_cap(bindings, region.pool.len() + 1);
    match eval_node(
        module,
        registry,
        region,
        region.root,
        region.pool.len(),
        &mut env,
        &mut vp,
        &mut initial_heap,
        0,
        0,
        false,
        true,
    )? {
        Flow::Normal(sv) | Flow::Return(sv) => Ok((vp.to_vec(sv), initial_heap)),
        _ => Err(TrapCode::Unreachable),
    }
}

pub(crate) fn eval_region_first(
    module: &Module,
    registry: &StratumRegistry,
    region: &Region,
    bindings: &[(ValId, Val)],
    heap: &mut HeapState,
) -> Result<Option<Val>, TrapCode> {
    let mut vp = ValPool::default();
    let mut env = Env::from_bindings_cap(bindings, region.pool.len() + 1);
    match eval_node(
        module,
        registry,
        region,
        region.root,
        region.pool.len(),
        &mut env,
        &mut vp,
        heap,
        0,
        0,
        false,
        true,
    )? {
        Flow::Normal(sv) | Flow::Return(sv) => Ok(vp.first(sv)),
        _ => Err(TrapCode::Unreachable),
    }
}

#[allow(clippy::too_many_arguments)]
fn eval_call_body(
    module: &Module,
    registry: &StratumRegistry,
    params: &[(ValId, ValType)],
    expected_tys: &[ValType],
    body: &Region,
    arg_sv: SmallVals,
    vp: &mut ValPool,
    heap: &mut HeapState,
    call_depth: u32,
    allow_host: bool,
) -> Result<SmallVals, TrapCode> {
    if call_depth >= MAX_CALL_DEPTH {
        return Err(TrapCode::OutOfFuel);
    }
    heap.consume_fuel(1)?;
    let mut callee_env = Env::with_cap(params.len().saturating_add(body.pool.len() + 1));
    vp.bind_params(&mut callee_env, params, arg_sv)?;
    let flow = eval_node(
        module,
        registry,
        body,
        body.root,
        body.pool.len(),
        &mut callee_env,
        vp,
        heap,
        call_depth + 1,
        0,
        false,
        allow_host,
    )?;
    let sv = match flow {
        Flow::Normal(sv) | Flow::Return(sv) => sv,
        _ => return Err(TrapCode::Unreachable),
    };
    vp.check_types(sv, expected_tys)?;
    Ok(sv)
}

#[allow(clippy::too_many_arguments)]
fn eval_node(
    module: &Module,
    registry: &StratumRegistry,
    reg: &Region,
    node: RegionNode,
    limit: usize,
    env: &mut Env,
    vp: &mut ValPool,
    heap: &mut HeapState,
    call_depth: u32,
    region_depth: u32,
    as_loop_body: bool,
    allow_host: bool,
) -> Result<Flow, TrapCode> {
    if region_depth >= MAX_REGION_DEPTH {
        return Err(TrapCode::OutOfFuel);
    }
    match node {
        RegionNode::Block(span) => eval_block_stmts(
            module,
            registry,
            reg,
            span,
            limit,
            env,
            vp,
            heap,
            call_depth,
            region_depth + 1,
            !as_loop_body,
            allow_host,
        ),
        RegionNode::IfElse { cond, then_region, else_region, results } => {
            heap.consume_fuel(1)?;
            let target_id = if env.u32(cond)? != 0 { then_region } else { else_region };
            let branch = reg.try_node_below(target_id, limit).ok_or(TrapCode::Unreachable)?;
            let flow = eval_node(
                module,
                registry,
                reg,
                branch,
                target_id.0 as usize,
                env,
                vp,
                heap,
                call_depth,
                region_depth + 1,
                false,
                allow_host,
            )?;
            if let Flow::Normal(sv) = flow {
                vp.check_tys_span(sv, reg, results)?;
            }
            Ok(flow)
        }
        RegionNode::BoundedLoop { max_iters, init_vars, state_vars, body } => {
            let mut state = vp.eval_span(env, reg, init_vars)?;
            vp.check_vars_span(state, reg, state_vars)?;
            if max_iters == 0 {
                return Err(TrapCode::OutOfFuel);
            }
            let body_node = reg.try_node_below(body, limit).ok_or(TrapCode::Unreachable)?;
            let base_env = env.len();
            let mut iter = 0u32;
            while iter < max_iters {
                heap.consume_fuel(1)?;
                vp.bind_span(env, reg, state_vars, state)?;
                let flow = eval_node(
                    module,
                    registry,
                    reg,
                    body_node,
                    body.0 as usize,
                    env,
                    vp,
                    heap,
                    call_depth,
                    region_depth + 1,
                    true,
                    allow_host,
                )?;
                env.truncate(base_env);
                match flow {
                    Flow::Normal(sv) | Flow::Break { depth: 0, values: sv } => {
                        return Ok(Flow::Normal(sv));
                    }
                    Flow::Break { depth, values } => {
                        return Ok(Flow::Break { depth: depth - 1, values });
                    }
                    Flow::Continue { depth: 0, values } => {
                        vp.check_vars_span(values, reg, state_vars)?;
                        state = values;
                    }
                    Flow::Continue { depth, values } => {
                        return Ok(Flow::Continue { depth: depth - 1, values });
                    }
                    Flow::Return(sv) => return Ok(Flow::Return(sv)),
                }
                iter += 1;
            }
            Err(TrapCode::OutOfFuel)
        }
        RegionNode::InvariantLoop { init_vars, state_vars, cond, body, .. } => {
            let mut state = vp.eval_span(env, reg, init_vars)?;
            vp.check_vars_span(state, reg, state_vars)?;
            let cond_idx = cond.0 as usize;
            let body_idx = body.0 as usize;
            if cond_idx >= limit
                || cond_idx >= reg.pool.len()
                || body_idx >= limit
                || body_idx >= reg.pool.len()
            {
                return Err(TrapCode::Unreachable);
            }
            let cond_slot = reg.pool[cond_idx];
            let body_slot = reg.pool[body_idx];
            if !cond_slot.is_node() || !body_slot.is_node() {
                return Err(TrapCode::Unreachable);
            }
            let base_env = env.len();
            loop {
                heap.consume_fuel(1)?;
                vp.bind_span(env, reg, state_vars, state)?;
                let state_env = env.len();
                let cond_flow = if cond_slot.tag == TAG_NODE_BLOCK {
                    if region_depth + 1 >= MAX_REGION_DEPTH {
                        return Err(TrapCode::OutOfFuel);
                    }
                    eval_block_stmts(
                        module,
                        registry,
                        reg,
                        Span { start: cond_slot.w0, len: cond_slot.w1 },
                        cond_idx,
                        env,
                        vp,
                        heap,
                        call_depth,
                        region_depth + 2,
                        true,
                        allow_host,
                    )?
                } else {
                    let cond_node = cond_slot
                        .to_node_with_pool(cond_idx, reg.pool.as_slice())
                        .ok_or(TrapCode::Unreachable)?;
                    eval_node(
                        module,
                        registry,
                        reg,
                        cond_node,
                        cond_idx,
                        env,
                        vp,
                        heap,
                        call_depth,
                        region_depth + 1,
                        false,
                        allow_host,
                    )?
                };
                match cond_flow {
                    Flow::Normal(sv) => match vp.as_single_i32(sv) {
                        Some(0) => {
                            env.truncate(base_env);
                            return Ok(Flow::Normal(state));
                        }
                        Some(_) => {}
                        None => return Err(TrapCode::Unreachable),
                    },
                    Flow::Return(sv) => {
                        env.truncate(base_env);
                        return Ok(Flow::Return(sv));
                    }
                    _ => return Err(TrapCode::Unreachable),
                }
                env.truncate(state_env);
                let body_flow = if body_slot.tag == TAG_NODE_BLOCK {
                    if region_depth + 1 >= MAX_REGION_DEPTH {
                        return Err(TrapCode::OutOfFuel);
                    }
                    eval_block_stmts(
                        module,
                        registry,
                        reg,
                        Span { start: body_slot.w0, len: body_slot.w1 },
                        body_idx,
                        env,
                        vp,
                        heap,
                        call_depth,
                        region_depth + 2,
                        false,
                        allow_host,
                    )?
                } else {
                    let body_node = body_slot
                        .to_node_with_pool(body_idx, reg.pool.as_slice())
                        .ok_or(TrapCode::Unreachable)?;
                    eval_node(
                        module,
                        registry,
                        reg,
                        body_node,
                        body_idx,
                        env,
                        vp,
                        heap,
                        call_depth,
                        region_depth + 1,
                        true,
                        allow_host,
                    )?
                };
                env.truncate(base_env);
                match body_flow {
                    Flow::Normal(sv) | Flow::Continue { depth: 0, values: sv } => {
                        vp.check_vars_span(sv, reg, state_vars)?;
                        state = sv;
                    }
                    Flow::Break { depth: 0, values } => return Ok(Flow::Normal(values)),
                    Flow::Break { depth, values } => {
                        return Ok(Flow::Break { depth: depth - 1, values });
                    }
                    Flow::Continue { depth, values } => {
                        return Ok(Flow::Continue { depth: depth - 1, values });
                    }
                    Flow::Return(sv) => return Ok(Flow::Return(sv)),
                }
            }
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn eval_block_stmts(
    module: &Module,
    registry: &StratumRegistry,
    reg: &Region,
    span: Span,
    limit: usize,
    env: &mut Env,
    vp: &mut ValPool,
    heap: &mut HeapState,
    call_depth: u32,
    region_depth: u32,
    catch_break: bool,
    allow_host: bool,
) -> Result<Flow, TrapCode> {
    let saved_env = env.len();
    let mut idx = 0u32;
    while idx < span.len {
        let slot = reg.try_stmt_slot(span, idx).ok_or(TrapCode::Unreachable)?;
        heap.consume_fuel(1)?;
        match slot.tag {
            TAG_STMT_LET => {
                let (dst, ty, op) = slot.to_let_op().ok_or(TrapCode::Unreachable)?;
                let val = eval_op(env, heap, &op)?;
                if val.val_type() != ty {
                    return Err(TrapCode::Unreachable);
                }
                env.push(dst, val)?;
            }
            TAG_STMT_EFFECT => {
                let eff = slot.to_effect().ok_or(TrapCode::Unreachable)?;
                eval_effect(module, env, heap, &eff)?;
            }
            TAG_STMT_REGION => {
                let results = Span { start: slot.w0, len: slot.w1 };
                let sub_id = RegionNodeId(slot.w2);
                let sub_node = reg.try_node_below(sub_id, limit).ok_or(TrapCode::Unreachable)?;
                let sub_flow = eval_node(
                    module,
                    registry,
                    reg,
                    sub_node,
                    sub_id.0 as usize,
                    env,
                    vp,
                    heap,
                    call_depth,
                    region_depth,
                    false,
                    allow_host,
                )?;
                match sub_flow {
                    Flow::Normal(sv) => vp.bind_span(env, reg, results, sv)?,
                    other => {
                        env.truncate(saved_env);
                        return apply_block_exit(other, catch_break);
                    }
                }
            }
            TAG_STMT_CALL => {
                let results = Span { start: slot.w0, len: slot.w1 };
                let args = Span { start: slot.w3, len: slot.w4 };
                let arg_sv = vp.eval_span(env, reg, args)?;
                let ret_sv = if slot.sub == CALL_FUNC {
                    if module.funcs.is_empty() {
                        return Err(TrapCode::Unreachable);
                    }
                    let f = module.func(FuncId(slot.w2)).ok_or(TrapCode::Unreachable)?;
                    eval_call_body(
                        module,
                        registry,
                        &f.params,
                        &f.results,
                        &f.body,
                        arg_sv,
                        vp,
                        heap,
                        call_depth,
                        allow_host,
                    )?
                } else if slot.sub == CALL_STRATUM {
                    if registry.promoted().is_empty() && registry.candidates().is_empty() {
                        return Err(TrapCode::Unreachable);
                    }
                    let op = registry.get_op(StratumId(slot.w2)).ok_or(TrapCode::Unreachable)?;
                    eval_call_body(
                        module,
                        registry,
                        &op.params,
                        &op.results,
                        &op.body,
                        arg_sv,
                        vp,
                        heap,
                        call_depth,
                        allow_host,
                    )?
                } else if slot.sub == CALL_HOST {
                    if !allow_host || module.host_contracts.is_empty() {
                        return Err(TrapCode::HostContractViolation);
                    }
                    eval_host_call(module, registry, call_depth + 1, vp, heap, HostCallId(slot.w2), arg_sv)?
                } else {
                    return Err(TrapCode::Unreachable);
                };
                vp.bind_span(env, reg, results, ret_sv)?;
            }
            TAG_STMT_YIELD => {
                let vs = Span { start: slot.w0, len: slot.w1 };
                let sv = vp.eval_span(env, reg, vs)?;
                env.truncate(saved_env);
                return apply_block_exit(Flow::Normal(sv), catch_break);
            }
            TAG_STMT_BREAK => {
                let take = if slot.sub == 0 { true } else { env.u32(ValId(slot.w1))? != 0 };
                if take {
                    let sv = vp.eval_span(env, reg, Span { start: slot.w2, len: slot.w3 })?;
                    env.truncate(saved_env);
                    return apply_block_exit(Flow::Break { depth: slot.w0, values: sv }, catch_break);
                }
            }
            TAG_STMT_CONTINUE => {
                let take = if slot.sub == 0 { true } else { env.u32(ValId(slot.w1))? != 0 };
                if take {
                    let sv = vp.eval_span(env, reg, Span { start: slot.w2, len: slot.w3 })?;
                    env.truncate(saved_env);
                    return apply_block_exit(Flow::Continue { depth: slot.w0, values: sv }, catch_break);
                }
            }
            TAG_STMT_RETURN => {
                let vs = Span { start: slot.w0, len: slot.w1 };
                let sv = vp.eval_span(env, reg, vs)?;
                env.truncate(saved_env);
                return Ok(Flow::Return(sv));
            }
            _ => return Err(TrapCode::Unreachable),
        }
        idx += 1;
    }
    env.truncate(saved_env);
    apply_block_exit(Flow::Normal(SmallVals::EMPTY), catch_break)
}

fn eval_host_call(
    module: &Module,
    registry: &StratumRegistry,
    call_depth: u32,
    vp: &mut ValPool,
    heap: &mut HeapState,
    hid: HostCallId,
    arg_sv: SmallVals,
) -> Result<SmallVals, TrapCode> {
    if call_depth > MAX_CALL_DEPTH {
        return Err(TrapCode::OutOfFuel);
    }
    let hc = module.host_contract(hid).ok_or(TrapCode::HostContractViolation)?;
    if !validate_read_only_with_registry(&hc.precondition, registry)
        || !validate_read_only_with_registry(&hc.postcondition, registry)
    {
        return Err(TrapCode::HostContractViolation);
    }
    let bound = |b: SliceBound, vp_ref: &ValPool| match b {
        SliceBound::Const(c) => Ok(c as u64),
        SliceBound::Arg(i) => {
            if (i as usize) >= vp_ref.len(arg_sv) {
                return Err(TrapCode::HostContractViolation);
            }
            vp_ref
                .get(arg_sv, i as usize)
                .as_u32()
                .map(|u| u as u64)
                .ok_or(TrapCode::HostContractViolation)
        }
    };
    let max_sub = hc
        .precondition
        .pool
        .len()
        .max(hc.postcondition.pool.len())
        .max(hc.sim_body.as_ref().map_or(0, |b| b.pool.len()));
    let mut sub_env = Env::with_cap(hc.params.len() + hc.results.len() + max_sub + 2);
    vp.bind_params(&mut sub_env, &hc.params, arg_sv)
        .map_err(|_| TrapCode::HostContractViolation)?;

    let params_len = sub_env.len();
    let mut pre_heap = heap.clone();
    let pre_ok = matches!(
        eval_node(
            module,
            registry,
            &hc.precondition,
            hc.precondition.root,
            hc.precondition.pool.len(),
            &mut sub_env,
            vp,
            &mut pre_heap,
            call_depth,
            0,
            false,
            false,
        ),
        Ok(Flow::Normal(sv)) if vp.as_single_i32(sv).is_some_and(|x| x != 0)
    );
    sub_env.truncate(params_len);
    if !pre_ok {
        return Err(TrapCode::HostContractViolation);
    }
    for &(mid, r) in hc.read_footprints.iter().chain(&hc.write_footprints) {
        let end = bound(r.base, vp)?
            .checked_add(bound(r.len, vp)?)
            .ok_or(TrapCode::OutOfBoundsMem)?;
        if end > heap.memory(mid)?.bytes.len() as u64 {
            return Err(TrapCode::OutOfBoundsMem);
        }
    }
    let before = heap.memories.clone();
    let res_sv = match &hc.sim_body {
        Some(body) => {
            let flow = eval_node(
                module,
                registry,
                body,
                body.root,
                body.pool.len(),
                &mut sub_env,
                vp,
                heap,
                call_depth,
                0,
                false,
                false,
            )?;
            sub_env.truncate(params_len);
            match flow {
                Flow::Normal(sv) | Flow::Return(sv) => sv,
                _ => return Err(TrapCode::HostContractViolation),
            }
        }
        None => {
            let defaults: Vec<Val> = hc.results.iter().map(|&(_, t)| Val::default_for(t)).collect();
            vp.intern_slice(&defaults)
        }
    };
    if vp.len(res_sv) != hc.results.len()
        || (0..hc.results.len()).any(|i| vp.get(res_sv, i).val_type() != hc.results[i].1)
    {
        return Err(TrapCode::HostContractViolation);
    }
    let mut writes = Vec::with_capacity(hc.write_footprints.len());
    for &(mid, r) in &hc.write_footprints {
        let b = bound(r.base, vp)? as usize;
        writes.push((mid, b, b + bound(r.len, vp)? as usize));
    }
    for (prev, cur) in before.iter().zip(&heap.memories) {
        if prev.bytes.len() != cur.bytes.len() {
            return Err(TrapCode::HostContractViolation);
        }
        let mut rs: Vec<(usize, usize)> =
            writes.iter().filter(|w| w.0 == cur.id).map(|w| (w.1, w.2)).collect();
        for i in 1..rs.len() {
            let mut j = i;
            while j > 0 && rs[j - 1] > rs[j] {
                rs.swap(j - 1, j);
                j -= 1;
            }
        }
        let mut pos = 0usize;
        for (s, e) in rs {
            if s > pos && prev.bytes[pos..s] != cur.bytes[pos..s] {
                return Err(TrapCode::HostContractViolation);
            }
            pos = pos.max(e);
        }
        if prev.bytes[pos..] != cur.bytes[pos..] {
            return Err(TrapCode::HostContractViolation);
        }
    }
    vp.bind_params(&mut sub_env, &hc.results, res_sv)
        .map_err(|_| TrapCode::HostContractViolation)?;
    let mut post_heap = heap.clone();
    let post_ok = matches!(
        eval_node(
            module,
            registry,
            &hc.postcondition,
            hc.postcondition.root,
            hc.postcondition.pool.len(),
            &mut sub_env,
            vp,
            &mut post_heap,
            call_depth,
            0,
            false,
            false,
        ),
        Ok(Flow::Normal(sv)) if vp.as_single_i32(sv).is_some_and(|x| x != 0)
    );
    if !post_ok {
        return Err(TrapCode::HostContractViolation);
    }
    Ok(res_sv)
}

fn eval_op(env: &Env, heap: &mut HeapState, op: &Op) -> Result<Val, TrapCode> {
    match op {
        Op::ConstI32(v) => Ok(Val::I32(*v)),
        Op::ConstI64(v) => Ok(Val::I64(*v)),
        Op::Copy(id) => env.get(*id),
        Op::Select { cond, true_val, false_val } => {
            let (c, t, f) = (env.u32(*cond)?, env.get(*true_val)?, env.get(*false_val)?);
            if t.val_type() != f.val_type() {
                Err(TrapCode::Unreachable)
            } else {
                Ok(if c != 0 { t } else { f })
            }
        }
        Op::GlobalGet(gid) => heap.globals.get(gid.0 as usize).copied().ok_or(TrapCode::Unreachable),
        Op::Un(u, a) => eval_unop(*u, env.get(*a)?),
        Op::Bin(b, l, r) => eval_binop(*b, env.get(*l)?, env.get(*r)?),
        Op::Load { mem, addr, offset, width, signed, result_ty } => {
            heap.memory(*mem)?.load(env.u32(*addr)?, *offset, *width, *signed, *result_ty)
        }
        Op::MemorySize(mem) => Ok(Val::I32(heap.memory(*mem)?.size_pages() as i32)),
        Op::MemoryGrow { mem, delta } => Ok(Val::I32(heap.memory_mut(*mem)?.grow(env.u32(*delta)?))),
    }
}

fn eval_effect(
    module: &Module,
    env: &Env,
    heap: &mut HeapState,
    eff: &EffectOp,
) -> Result<(), TrapCode> {
    match eff {
        EffectOp::Store { mem, addr, offset, width, val } => {
            heap.memory_mut(*mem)?.store(env.u32(*addr)?, *offset, *width, env.get(*val)?)
        }
        EffectOp::MemoryCopy { dst_mem, src_mem, dst, src, len } => {
            heap.memory_copy(*dst_mem, *src_mem, env.u32(*dst)?, env.u32(*src)?, env.u32(*len)?)
        }
        EffectOp::MemoryFill { mem, dst, val, len } => {
            heap.memory_mut(*mem)?.fill(env.u32(*dst)?, env.u32(*val)? as u8, env.u32(*len)?)
        }
        EffectOp::GlobalSet { id, val } => {
            let gdef = module.global(*id).ok_or(TrapCode::Unreachable)?;
            let v = env.get(*val)?;
            if !gdef.mutable || v.val_type() != gdef.ty {
                return Err(TrapCode::Unreachable);
            }
            *heap.globals.get_mut(id.0 as usize).ok_or(TrapCode::Unreachable)? = v;
            Ok(())
        }
        EffectOp::Trap(code) => Err(*code),
        EffectOp::Nop => Ok(()),
    }
}

pub(crate) fn eval_unop(op: UnOp, v: Val) -> Result<Val, TrapCode> {
    Ok(match (op, v) {
        (UnOp::I32Eqz, Val::I32(x)) => Val::I32(i32::from(x == 0)),
        (UnOp::I64Eqz, Val::I64(x)) => Val::I32(i32::from(x == 0)),
        (UnOp::I32Clz, Val::I32(x)) => Val::I32(x.leading_zeros() as i32),
        (UnOp::I32Ctz, Val::I32(x)) => Val::I32(x.trailing_zeros() as i32),
        (UnOp::I32Popcnt, Val::I32(x)) => Val::I32(x.count_ones() as i32),
        (UnOp::I64Clz, Val::I64(x)) => Val::I64(x.leading_zeros() as i64),
        (UnOp::I64Ctz, Val::I64(x)) => Val::I64(x.trailing_zeros() as i64),
        (UnOp::I64Popcnt, Val::I64(x)) => Val::I64(x.count_ones() as i64),
        (UnOp::I32WrapI64, Val::I64(x)) => Val::I32(x as i32),
        (UnOp::I64ExtendI32S, Val::I32(x)) => Val::I64(x as i64),
        (UnOp::I64ExtendI32U, Val::I32(x)) => Val::I64((x as u32) as i64),
        (UnOp::I32Extend8S, Val::I32(x)) => Val::I32((x as i8) as i32),
        (UnOp::I32Extend16S, Val::I32(x)) => Val::I32((x as i16) as i32),
        (UnOp::I64Extend8S, Val::I64(x)) => Val::I64((x as i8) as i64),
        (UnOp::I64Extend16S, Val::I64(x)) => Val::I64((x as i16) as i64),
        (UnOp::I64Extend32S, Val::I64(x)) => Val::I64((x as i32) as i64),
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
            $eq => b($a == $c),
            $ne => b($a != $c),
            $lts => b($a < $c),
            $ltu => b(($a as $u) < ($c as $u)),
            $gts => b($a > $c),
            $gtu => b(($a as $u) > ($c as $u)),
            $les => b($a <= $c),
            $leu => b(($a as $u) <= ($c as $u)),
            $ges => b($a >= $c),
            $geu => b(($a as $u) >= ($c as $u)),
            $add => $w($a.wrapping_add($c)),
            $sub => $w($a.wrapping_sub($c)),
            $mul => $w($a.wrapping_mul($c)),
            $divs if $c == 0 => return Err(TrapCode::DivByZero),
            $divs if $a == <$s>::MIN && $c == -1 => return Err(TrapCode::IntOverflow),
            $divs => $w($a.wrapping_div($c)),
            $divu => $w(($a as $u).checked_div($c as $u).ok_or(TrapCode::DivByZero)? as $s),
            $rems if $c == 0 => return Err(TrapCode::DivByZero),
            $rems if $a == <$s>::MIN && $c == -1 => $w(0),
            $rems => $w($a.wrapping_rem($c)),
            $remu => $w(($a as $u).checked_rem($c as $u).ok_or(TrapCode::DivByZero)? as $s),
            $and => $w($a & $c),
            $or => $w($a | $c),
            $xor => $w($a ^ $c),
            $shl => $w($a.wrapping_shl($c as u32)),
            $shrs => $w($a.wrapping_shr($c as u32)),
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
            I32Eq, I32Ne, I32LtS, I32LtU, I32GtS, I32GtU, I32LeS, I32LeU, I32GeS, I32GeU,
            I32Add, I32Sub, I32Mul, I32DivS, I32DivU, I32RemS, I32RemU,
            I32And, I32Or, I32Xor, I32Shl, I32ShrS, I32ShrU, I32Rotl, I32Rotr),
        (Val::I64(a), Val::I64(c)) => int_ops!(a, c, i64, u64, Val::I64, 63, op;
            I64Eq, I64Ne, I64LtS, I64LtU, I64GtS, I64GtU, I64LeS, I64LeU, I64GeS, I64GeU,
            I64Add, I64Sub, I64Mul, I64DivS, I64DivU, I64RemS, I64RemU,
            I64And, I64Or, I64Xor, I64Shl, I64ShrS, I64ShrU, I64Rotl, I64Rotr),
        _ => Err(TrapCode::Unreachable),
    }
}
