//! Deterministic loop Verification Condition (VC) splitter.

use alloc::{boxed::Box, vec, vec::Vec};
use crate::eval::{HeapState, eval_region_first};
use crate::ir::*;
use crate::registry::StratumRegistry;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum VcKind { Init, Preservation, Exit }

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum VcError {
    NotAnInvariantLoop,
    ImpureSpecificationRegion,
    ArityMismatch,
    UnstructuredControlFlow,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum VcEvalResult { Holds, Vacuous, Violated(Option<TrapCode>) }

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VcObligation {
    pub kind: VcKind,
    pub params: Vec<(ValId, ValType)>,
    pub assumptions: Vec<Region>,
    pub goal: Region,
}

impl Drop for VcObligation {
    fn drop(&mut self) {
        if !self.assumptions.is_empty() && self.assumptions.len() <= 2 {
            let _ = self.assumptions.pop();
            let _ = self.assumptions.pop();
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoopVcs {
    pub init: VcObligation,
    pub preservation: VcObligation,
    pub exit: VcObligation,
}

/// Ensures a predicate/measure/spec region performs no heap, global, or unverified call mutations.
pub fn validate_read_only(region: &Region) -> bool {
    validate_ro_region(region, None)
}

/// Ensures `region` performs no heap or global mutations, verifying any `CallTarget::Stratum`
/// callees via `registry`'s inductively verified read-only metadata.
pub fn validate_read_only_with_registry(region: &Region, registry: &StratumRegistry) -> bool {
    validate_ro_region(region, Some(registry))
}

fn classify_stmt_ro(s: &Stmt, registry: Option<&StratumRegistry>) -> Option<bool> {
    match s {
        Stmt::Let { op, .. } => Some(!matches!(op, Op::MemoryGrow { .. })),
        Stmt::Effect(eff) => Some(matches!(eff, EffectOp::Trap(_) | EffectOp::Nop)),
        Stmt::Region { .. } => None,
        Stmt::Call { target: CallTarget::Stratum(sid), .. } => {
            Some(registry.is_some_and(|reg| reg.is_stratum_read_only(*sid)))
        }
        Stmt::Call { .. } => Some(false),
        Stmt::Yield(_) | Stmt::Break { .. } | Stmt::Continue { .. } | Stmt::Return(_) => Some(true),
    }
}

fn validate_ro_region(region: &Region, registry: Option<&StratumRegistry>) -> bool {
    if let Region::Block(stmts) = region {
        match stmts.as_slice() {
            [] => return true,
            [s0] => {
                if let Some(ok) = classify_stmt_ro(s0, registry) {
                    return ok;
                }
            }
            _ => {}
        }
    }
    let mut stack = Stack2::<&Region>::with_first(region);
    while let Some(r) = stack.pop() {
        match r {
            Region::Block(stmts) => match stmts.as_slice() {
                [] => {}
                [s0] => match classify_stmt_ro(s0, registry) {
                    Some(true) => {}
                    Some(false) => return false,
                    None => {
                        if let Stmt::Region { region: sub, .. } = s0 {
                            stack.push(sub);
                        }
                    }
                },
                _ => {
                    let mut i = 0;
                    while i < stmts.len() {
                        let s = &stmts[i];
                        match classify_stmt_ro(s, registry) {
                            Some(true) => {}
                            Some(false) => return false,
                            None => {
                                if let Stmt::Region { region: sub, .. } = s {
                                    stack.push(sub);
                                }
                            }
                        }
                        i += 1;
                    }
                }
            },
            Region::IfElse { then_region, else_region, .. } => {
                stack.push(else_region);
                stack.push(then_region);
            }
            Region::BoundedLoop { body, .. } => stack.push(body),
            Region::InvariantLoop { cond, invariant_pred, fuel_measure, body, .. } => {
                stack.push(body);
                stack.push(fuel_measure);
                stack.push(invariant_pred);
                stack.push(cond);
            }
        }
    }
    true
}

struct RemapScope {
    inline: [(ValId, ValId); 16],
    len: usize,
    spill: Vec<(ValId, ValId)>,
}

impl RemapScope {
    fn from_slice(initial: &[(ValId, ValId)]) -> Self {
        let mut s = Self { inline: [(ValId(0), ValId(0)); 16], len: 0, spill: Vec::new() };
        match initial {
            [] => {}
            [(k0, v0)] => s.push(*k0, *v0),
            [(k0, v0), (k1, v1)] => {
                s.push(*k0, *v0);
                s.push(*k1, *v1);
            }
            _ => {
                let mut i = 0;
                while i < initial.len() {
                    let (k, v) = initial[i];
                    s.push(k, v);
                    i += 1;
                }
            }
        }
        s
    }
    fn len(&self) -> usize {
        self.len
    }
    fn truncate(&mut self, saved: usize) {
        if saved < self.len {
            if (self.len >> 4) != 0 {
                self.spill.truncate(saved.saturating_sub(16));
            }
            self.len = saved;
        }
    }
    fn push(&mut self, old: ValId, new: ValId) {
        if (self.len >> 4) == 0 {
            self.inline[self.len & 15] = (old, new);
            self.len += 1;
        } else {
            self.len = self.len.saturating_add(1);
            self.spill.push((old, new));
        }
    }
    fn lookup(&self, id: ValId) -> ValId {
        if self.len <= 2 {
            if self.len == 2 && self.inline[1].0 == id {
                return self.inline[1].1;
            }
            if self.len >= 1 && self.inline[0].0 == id {
                return self.inline[0].1;
            }
            return id;
        }
        if (self.len >> 4) != 0 && self.len > 16 {
            let mut j = self.spill.len();
            while j > 0 {
                j -= 1;
                if self.spill[j].0 == id {
                    return self.spill[j].1;
                }
            }
        }
        let mut i = self.len.min(16);
        while i > 0 {
            i -= 1;
            if self.inline[i & 15].0 == id {
                return self.inline[i & 15].1;
            }
        }
        id
    }
}

fn lookup_val(id: ValId, scope: &RemapScope) -> ValId {
    scope.lookup(id)
}

fn fresh_val(old: ValId, scope: &mut RemapScope, next: &mut u32) -> ValId {
    let f = ValId(*next);
    *next = next.saturating_add(1);
    scope.push(old, f);
    f
}

/// Alpha-renames all locally defined `ValId`s in `region` using `initial_map`,
/// guaranteeing newly allocated `ValId`s never collide with free uses or `initial_map`.
pub fn remap_region_vals(region: &Region, initial_map: &[(ValId, ValId)], next_fresh: &mut u32) -> Region {
    let mut min_safe = max_val_id_in_region(region);
    match initial_map {
        [] => {}
        [(k0, v0)] => min_safe = min_safe.max(k0.0.max(v0.0).saturating_add(1)),
        [(k0, v0), (k1, v1)] => {
            min_safe = min_safe
                .max(k0.0.max(v0.0).saturating_add(1))
                .max(k1.0.max(v1.0).saturating_add(1));
        }
        _ => {
            let mut m_idx = 0;
            while m_idx < initial_map.len() {
                let (k, v) = initial_map[m_idx];
                min_safe = min_safe.max(k.0.max(v.0).saturating_add(1));
                m_idx += 1;
            }
        }
    }
    if *next_fresh < min_safe {
        *next_fresh = min_safe;
    }
    let mut scope = RemapScope::from_slice(initial_map);
    remap_inner(region, &mut scope, next_fresh)
}

fn remap_flat_stmt(stmt: &Stmt, scope: &mut RemapScope, next: &mut u32) -> Stmt {
    match stmt {
        Stmt::Let { dst, ty, op } => {
            let new_op = match op {
                Op::Copy(v) => Op::Copy(lookup_val(*v, scope)),
                Op::Select { cond, true_val, false_val } => Op::Select {
                    cond: lookup_val(*cond, scope),
                    true_val: lookup_val(*true_val, scope),
                    false_val: lookup_val(*false_val, scope),
                },
                Op::Un(u, v) => Op::Un(*u, lookup_val(*v, scope)),
                Op::Bin(b, l, r) => Op::Bin(*b, lookup_val(*l, scope), lookup_val(*r, scope)),
                Op::Load { mem, addr, offset, width, signed, result_ty } => Op::Load {
                    mem: *mem,
                    addr: lookup_val(*addr, scope),
                    offset: *offset,
                    width: *width,
                    signed: *signed,
                    result_ty: *result_ty,
                },
                Op::MemoryGrow { mem, delta } => Op::MemoryGrow { mem: *mem, delta: lookup_val(*delta, scope) },
                other => *other,
            };
            Stmt::Let { dst: fresh_val(*dst, scope, next), ty: *ty, op: new_op }
        }
        Stmt::Effect(eff) => Stmt::Effect(match eff {
            EffectOp::Store { mem, addr, offset, width, val } => EffectOp::Store {
                mem: *mem,
                addr: lookup_val(*addr, scope),
                offset: *offset,
                width: *width,
                val: lookup_val(*val, scope),
            },
            EffectOp::MemoryCopy { dst_mem, src_mem, dst, src, len } => EffectOp::MemoryCopy {
                dst_mem: *dst_mem,
                src_mem: *src_mem,
                dst: lookup_val(*dst, scope),
                src: lookup_val(*src, scope),
                len: lookup_val(*len, scope),
            },
            EffectOp::MemoryFill { mem, dst, val, len } => EffectOp::MemoryFill {
                mem: *mem,
                dst: lookup_val(*dst, scope),
                val: lookup_val(*val, scope),
                len: lookup_val(*len, scope),
            },
            EffectOp::GlobalSet { id, val } => EffectOp::GlobalSet { id: *id, val: lookup_val(*val, scope) },
            other => *other,
        }),
        Stmt::Call { results, target, args } => {
            let args = remap_vals(args, scope);
            let new_res = match results.as_slice() {
                [] => Vec::new(),
                [(id0, ty0)] => vec![(fresh_val(*id0, scope, next), *ty0)],
                _ => {
                    let mut nr = Vec::with_capacity(results.len());
                    let mut i = 0;
                    while i < results.len() {
                        nr.push((fresh_val(results[i].0, scope, next), results[i].1));
                        i += 1;
                    }
                    nr
                }
            };
            Stmt::Call { results: new_res, target: *target, args }
        }
        Stmt::Yield(vs) => Stmt::Yield(remap_vals(vs, scope)),
        Stmt::Return(vs) => Stmt::Return(remap_vals(vs, scope)),
        Stmt::Break { depth, cond, values } => Stmt::Break {
            depth: *depth,
            cond: cond.map(|c| lookup_val(c, scope)),
            values: remap_vals(values, scope),
        },
        Stmt::Continue { depth, cond, values } => Stmt::Continue {
            depth: *depth,
            cond: cond.map(|c| lookup_val(c, scope)),
            values: remap_vals(values, scope),
        },
        Stmt::Region { .. } => unreachable!(),
    }
}

enum RemapTask<'a> {
    Enter(&'a Region),
    StepBlock { stmts: &'a [Stmt], idx: usize, saved: usize, out: Vec<Stmt> },
    FinishSubRegion { results: &'a [(ValId, ValType)], stmts: &'a [Stmt], next_idx: usize, saved: usize, out: Vec<Stmt> },
    BuildIfElse { cond: ValId, results: &'a [ValType] },
    BuildBounded { max_iters: u32, init_vars: Vec<ValId>, state_vars: Vec<(ValId, ValType)>, saved: usize },
    BuildInv { init_vars: Vec<ValId>, state_vars: Vec<(ValId, ValType)>, saved: usize },
}

fn remap_inner(root: &Region, scope: &mut RemapScope, next: &mut u32) -> Region {
    if let Region::Block(stmts) = root {
        match stmts.as_slice() {
            [] => return Region::Block(Vec::new()),
            [s0] if !matches!(s0, Stmt::Region { .. }) => {
                let saved = scope.len();
                let r = remap_flat_stmt(s0, scope, next);
                scope.truncate(saved);
                return Region::Block(vec![r]);
            }
            _ => {}
        }
    }
    let mut tasks = Stack2::<RemapTask<'_>>::with_first(RemapTask::Enter(root));
    let mut vals = Stack2::<Region>::new();
    'outer: while let Some(task) = tasks.pop() {
        match task {
            RemapTask::Enter(region) => match region {
                Region::Block(stmts) => tasks.push(RemapTask::StepBlock {
                    stmts,
                    idx: 0,
                    saved: scope.len(),
                    out: Vec::new(),
                }),
                Region::IfElse { cond, then_region, else_region, results } => {
                    let c = lookup_val(*cond, scope);
                    tasks.push(RemapTask::BuildIfElse { cond: c, results });
                    tasks.push(RemapTask::Enter(else_region));
                    tasks.push(RemapTask::Enter(then_region));
                }
                Region::BoundedLoop { max_iters, init_vars, state_vars, body } => {
                    let new_inits = remap_vals(init_vars, scope);
                    let saved = scope.len();
                    let mut new_states = Vec::with_capacity(state_vars.len());
                    for &(id, ty) in state_vars {
                        new_states.push((fresh_val(id, scope, next), ty));
                    }
                    tasks.push(RemapTask::BuildBounded { max_iters: *max_iters, init_vars: new_inits, state_vars: new_states, saved });
                    tasks.push(RemapTask::Enter(body));
                }
                Region::InvariantLoop { init_vars, state_vars, cond, invariant_pred, fuel_measure, body } => {
                    let new_inits = remap_vals(init_vars, scope);
                    let saved = scope.len();
                    let mut new_states = Vec::with_capacity(state_vars.len());
                    for &(id, ty) in state_vars {
                        new_states.push((fresh_val(id, scope, next), ty));
                    }
                    tasks.push(RemapTask::BuildInv { init_vars: new_inits, state_vars: new_states, saved });
                    tasks.push(RemapTask::Enter(body));
                    tasks.push(RemapTask::Enter(fuel_measure));
                    tasks.push(RemapTask::Enter(invariant_pred));
                    tasks.push(RemapTask::Enter(cond));
                }
            },
            RemapTask::StepBlock { stmts, mut idx, saved, mut out } => {
                while idx < stmts.len() {
                    if let Stmt::Region { results, region: sub } = &stmts[idx] {
                        tasks.push(RemapTask::FinishSubRegion { results, stmts, next_idx: idx + 1, saved, out });
                        tasks.push(RemapTask::Enter(sub));
                        continue 'outer;
                    }
                    out.push(remap_flat_stmt(&stmts[idx], scope, next));
                    idx += 1;
                }
                scope.truncate(saved);
                vals.push(Region::Block(out));
            }
            RemapTask::FinishSubRegion { results, stmts, next_idx, saved, mut out } => {
                let sub = vals.pop().unwrap_or_else(|| Region::Block(Vec::new()));
                let mut new_res = Vec::with_capacity(results.len());
                for &(id, ty) in results {
                    new_res.push((fresh_val(id, scope, next), ty));
                }
                out.push(Stmt::Region { results: new_res, region: sub });
                tasks.push(RemapTask::StepBlock { stmts, idx: next_idx, saved, out });
            }
            RemapTask::BuildIfElse { cond, results } => {
                let else_r = vals.pop().unwrap_or_else(|| Region::Block(Vec::new()));
                let then_r = vals.pop().unwrap_or_else(|| Region::Block(Vec::new()));
                vals.push(Region::IfElse {
                    cond,
                    results: results.to_vec(),
                    then_region: Box::new(then_r),
                    else_region: Box::new(else_r),
                });
            }
            RemapTask::BuildBounded { max_iters, init_vars, state_vars, saved } => {
                let body_r = vals.pop().unwrap_or_else(|| Region::Block(Vec::new()));
                scope.truncate(saved);
                vals.push(Region::BoundedLoop { max_iters, init_vars, state_vars, body: Box::new(body_r) });
            }
            RemapTask::BuildInv { init_vars, state_vars, saved } => {
                let body_r = vals.pop().unwrap_or_else(|| Region::Block(Vec::new()));
                let fuel_r = vals.pop().unwrap_or_else(|| Region::Block(Vec::new()));
                let inv_r = vals.pop().unwrap_or_else(|| Region::Block(Vec::new()));
                let cond_r = vals.pop().unwrap_or_else(|| Region::Block(Vec::new()));
                scope.truncate(saved);
                vals.push(Region::InvariantLoop {
                    init_vars,
                    state_vars,
                    cond: Box::new(cond_r),
                    invariant_pred: Box::new(inv_r),
                    fuel_measure: Box::new(fuel_r),
                    body: Box::new(body_r),
                });
            }
        }
    }
    vals.pop().unwrap_or_else(|| Region::Block(Vec::new()))
}

fn remap_vals(vs: &[ValId], scope: &RemapScope) -> Vec<ValId> {
    match vs {
        [] => Vec::new(),
        [v0] => vec![lookup_val(*v0, scope)],
        [v0, v1] => vec![lookup_val(*v0, scope), lookup_val(*v1, scope)],
        _ => {
            let mut out = Vec::with_capacity(vs.len());
            let mut i = 0;
            while i < vs.len() {
                out.push(lookup_val(vs[i], scope));
                i += 1;
            }
            out
        }
    }
}

fn bump_id(v: ValId, m: &mut u32) {
    *m = (*m).max(v.0.saturating_add(1));
}

fn bump_ids(vs: &[ValId], m: &mut u32) {
    match vs {
        [] => {}
        [v0] => bump_id(*v0, m),
        [v0, v1] => {
            bump_id(*v0, m);
            bump_id(*v1, m);
        }
        _ => {
            let mut i = 0;
            while i < vs.len() {
                bump_id(vs[i], m);
                i += 1;
            }
        }
    }
}

fn bump_typed(vs: &[(ValId, ValType)], m: &mut u32) {
    match vs {
        [] => {}
        [(v0, _)] => bump_id(*v0, m),
        [(v0, _), (v1, _)] => {
            bump_id(*v0, m);
            bump_id(*v1, m);
        }
        _ => {
            let mut i = 0;
            while i < vs.len() {
                bump_id(vs[i].0, m);
                i += 1;
            }
        }
    }
}

pub(crate) fn max_val_id_in_region(region: &Region) -> u32 {
    if let Region::Block(stmts) = region {
        match stmts.as_slice() {
            [] => return 0,
            [s0] if !matches!(s0, Stmt::Region { .. }) => return max_val_id_flat_one(s0),
            _ => {}
        }
    }
    max_val_id_iter(region)
}

fn max_val_id_flat_one(s: &Stmt) -> u32 {
    let mut max = 0u32;
    match s {
        Stmt::Let { dst, op, .. } => {
            bump_id(*dst, &mut max);
            match op {
                Op::Copy(v) | Op::Un(_, v) | Op::Load { addr: v, .. } | Op::MemoryGrow { delta: v, .. } => {
                    bump_id(*v, &mut max);
                }
                Op::Select { cond, true_val, false_val } => {
                    bump_id(*cond, &mut max);
                    bump_id(*true_val, &mut max);
                    bump_id(*false_val, &mut max);
                }
                Op::Bin(_, l, r) => {
                    bump_id(*l, &mut max);
                    bump_id(*r, &mut max);
                }
                Op::ConstI32(_) | Op::ConstI64(_) | Op::GlobalGet(_) | Op::MemorySize(_) => {}
            }
        }
        Stmt::Effect(eff) => match eff {
            EffectOp::Store { addr, val, .. } => {
                bump_id(*addr, &mut max);
                bump_id(*val, &mut max);
            }
            EffectOp::MemoryCopy { dst, src, len, .. } | EffectOp::MemoryFill { dst, val: src, len, .. } => {
                bump_id(*dst, &mut max);
                bump_id(*src, &mut max);
                bump_id(*len, &mut max);
            }
            EffectOp::GlobalSet { val, .. } => bump_id(*val, &mut max),
            EffectOp::Trap(_) | EffectOp::Nop => {}
        },
        Stmt::Call { results, args, .. } => {
            bump_typed(results, &mut max);
            bump_ids(args, &mut max);
        }
        Stmt::Yield(vs) | Stmt::Return(vs) => bump_ids(vs, &mut max),
        Stmt::Break { cond, values, .. } | Stmt::Continue { cond, values, .. } => {
            if let Some(c) = cond {
                bump_id(*c, &mut max);
            }
            bump_ids(values, &mut max);
        }
        Stmt::Region { .. } => {}
    }
    max
}

fn max_val_id_iter(root: &Region) -> u32 {
    let mut max = 0u32;
    let mut stack = Stack2::<&Region>::with_first(root);
    while let Some(r) = stack.pop() {
        match r {
            Region::Block(stmts) => {
                for s in stmts {
                    if let Stmt::Region { results, region } = s {
                        bump_typed(results, &mut max);
                        stack.push(region);
                    } else {
                        max = max.max(max_val_id_flat_one(s));
                    }
                }
            }
            Region::IfElse { cond, then_region, else_region, .. } => {
                bump_id(*cond, &mut max);
                stack.push(else_region);
                stack.push(then_region);
            }
            Region::BoundedLoop { init_vars, state_vars, body, .. } => {
                bump_ids(init_vars, &mut max);
                bump_typed(state_vars, &mut max);
                stack.push(body);
            }
            Region::InvariantLoop { init_vars, state_vars, cond, invariant_pred, fuel_measure, body } => {
                bump_ids(init_vars, &mut max);
                bump_typed(state_vars, &mut max);
                stack.push(body);
                stack.push(fuel_measure);
                stack.push(invariant_pred);
                stack.push(cond);
            }
        }
    }
    max
}

fn flat_stmt_escapes(s: &Stmt, inner_d: u32, allow_ct: bool) -> Option<bool> {
    match s {
        Stmt::Return(_) => Some(true),
        Stmt::Break { depth: br_d, .. } if *br_d >= inner_d => Some(true),
        Stmt::Continue { depth: ct_d, .. }
            if if allow_ct { *ct_d > inner_d } else { *ct_d >= inner_d } =>
        {
            Some(true)
        }
        Stmt::Region { .. } => None,
        _ => Some(false),
    }
}

/// Checks whether `region` contains `Return` or any `Break`/`Continue` escaping its boundary.
fn has_escaping_flow(region: &Region, depth: u32, is_loop_body_root: bool, allow_root_continue: bool) -> bool {
    if let Region::Block(stmts) = region {
        let inner_d = if is_loop_body_root { depth } else { depth + 1 };
        match stmts.as_slice() {
            [] => return false,
            [s0] => {
                if let Some(esc) = flat_stmt_escapes(s0, inner_d, allow_root_continue) {
                    return esc;
                }
            }
            _ => {}
        }
    }
    let mut stack = Stack2::with_first((region, depth, is_loop_body_root, allow_root_continue));
    while let Some((reg, d, is_root, allow_ct)) = stack.pop() {
        match reg {
            Region::Block(stmts) => {
                let inner_d = if is_root { d } else { d + 1 };
                for s in stmts {
                    match flat_stmt_escapes(s, inner_d, allow_ct) {
                        Some(true) => return true,
                        Some(false) => {}
                        None => {
                            if let Stmt::Region { region: sub, .. } = s {
                                stack.push((sub, inner_d, false, allow_ct));
                            }
                        }
                    }
                }
            }
            Region::IfElse { then_region, else_region, .. } => {
                stack.push((else_region, d, false, allow_ct));
                stack.push((then_region, d, false, allow_ct));
            }
            Region::BoundedLoop { body, .. } => stack.push((body, d + 1, true, allow_ct)),
            Region::InvariantLoop { cond, invariant_pred, fuel_measure, body, .. } => {
                stack.push((body, d + 1, true, allow_ct));
                stack.push((fuel_measure, 0, false, false));
                stack.push((invariant_pred, 0, false, false));
                stack.push((cond, 0, false, false));
            }
        }
    }
    false
}

fn clone_val_vec(vs: &[ValId]) -> Vec<ValId> {
    match vs {
        [] => Vec::new(),
        [v0] => vec![*v0],
        [v0, v1] => vec![*v0, *v1],
        _ => vs.to_vec(),
    }
}

fn normalize_flat_stmt(s: &Stmt, inner_d: u32) -> Stmt {
    match s {
        Stmt::Let { dst, ty, op } => Stmt::Let { dst: *dst, ty: *ty, op: *op },
        Stmt::Effect(eff) => Stmt::Effect(*eff),
        Stmt::Call { results, target, args } => {
            Stmt::Call { results: results.clone(), target: *target, args: clone_val_vec(args) }
        }
        Stmt::Yield(vs) => Stmt::Yield(clone_val_vec(vs)),
        Stmt::Return(vs) => Stmt::Return(clone_val_vec(vs)),
        Stmt::Break { depth, cond, values } => {
            Stmt::Break { depth: *depth, cond: *cond, values: clone_val_vec(values) }
        }
        Stmt::Continue { depth: d, cond, values } if *d == inner_d => {
            Stmt::Break { depth: *d, cond: *cond, values: clone_val_vec(values) }
        }
        Stmt::Continue { depth, cond, values } => {
            Stmt::Continue { depth: *depth, cond: *cond, values: clone_val_vec(values) }
        }
        Stmt::Region { .. } => unreachable!(),
    }
}

enum NormTask<'a> {
    Enter { region: &'a Region, depth: u32, is_root: bool },
    StepBlock { stmts: &'a [Stmt], idx: usize, inner_d: u32, out: Vec<Stmt> },
    FinishSubRegion { results: &'a [(ValId, ValType)], stmts: &'a [Stmt], next_idx: usize, inner_d: u32, out: Vec<Stmt> },
    BuildIfElse { cond: ValId, results: &'a [ValType] },
    BuildBounded { max_iters: u32, init_vars: &'a [ValId], state_vars: &'a [(ValId, ValType)] },
    BuildInv { init_vars: &'a [ValId], state_vars: &'a [(ValId, ValType)], cond: &'a Region, inv: &'a Region, fuel: &'a Region },
}

fn normalize_loop_body_for_vc(region: &Region, depth: u32, is_loop_body_root: bool) -> Region {
    if let Region::Block(stmts) = region {
        let inner_d = if is_loop_body_root { depth } else { depth + 1 };
        match stmts.as_slice() {
            [] => return Region::Block(Vec::new()),
            [s0] if !matches!(s0, Stmt::Region { .. }) => {
                return Region::Block(vec![normalize_flat_stmt(s0, inner_d)]);
            }
            _ => {}
        }
    }
    let mut tasks = Stack2::with_first(NormTask::Enter { region, depth, is_root: is_loop_body_root });
    let mut vals = Stack2::<Region>::new();
    'outer: while let Some(task) = tasks.pop() {
        match task {
            NormTask::Enter { region: r, depth: d, is_root } => match r {
                Region::Block(stmts) => tasks.push(NormTask::StepBlock {
                    stmts,
                    idx: 0,
                    inner_d: if is_root { d } else { d + 1 },
                    out: Vec::new(),
                }),
                Region::IfElse { cond, then_region, else_region, results } => {
                    tasks.push(NormTask::BuildIfElse { cond: *cond, results });
                    tasks.push(NormTask::Enter { region: else_region, depth: d, is_root: false });
                    tasks.push(NormTask::Enter { region: then_region, depth: d, is_root: false });
                }
                Region::BoundedLoop { max_iters, init_vars, state_vars, body } => {
                    tasks.push(NormTask::BuildBounded { max_iters: *max_iters, init_vars, state_vars });
                    tasks.push(NormTask::Enter { region: body, depth: d + 1, is_root: true });
                }
                Region::InvariantLoop { init_vars, state_vars, cond, invariant_pred, fuel_measure, body } => {
                    tasks.push(NormTask::BuildInv { init_vars, state_vars, cond, inv: invariant_pred, fuel: fuel_measure });
                    tasks.push(NormTask::Enter { region: body, depth: d + 1, is_root: true });
                }
            },
            NormTask::StepBlock { stmts, mut idx, inner_d, mut out } => {
                while idx < stmts.len() {
                    if let Stmt::Region { results, region: sub } = &stmts[idx] {
                        tasks.push(NormTask::FinishSubRegion { results, stmts, next_idx: idx + 1, inner_d, out });
                        tasks.push(NormTask::Enter { region: sub, depth: inner_d, is_root: false });
                        continue 'outer;
                    }
                    out.push(normalize_flat_stmt(&stmts[idx], inner_d));
                    idx += 1;
                }
                vals.push(Region::Block(out));
            }
            NormTask::FinishSubRegion { results, stmts, next_idx, inner_d, mut out } => {
                let sub = vals.pop().unwrap_or_else(|| Region::Block(Vec::new()));
                out.push(Stmt::Region { results: results.to_vec(), region: sub });
                tasks.push(NormTask::StepBlock { stmts, idx: next_idx, inner_d, out });
            }
            NormTask::BuildIfElse { cond, results } => {
                let else_r = vals.pop().unwrap_or_else(|| Region::Block(Vec::new()));
                let then_r = vals.pop().unwrap_or_else(|| Region::Block(Vec::new()));
                vals.push(Region::IfElse {
                    cond,
                    results: results.to_vec(),
                    then_region: Box::new(then_r),
                    else_region: Box::new(else_r),
                });
            }
            NormTask::BuildBounded { max_iters, init_vars, state_vars } => {
                let body_r = vals.pop().unwrap_or_else(|| Region::Block(Vec::new()));
                vals.push(Region::BoundedLoop {
                    max_iters,
                    init_vars: init_vars.to_vec(),
                    state_vars: state_vars.to_vec(),
                    body: Box::new(body_r),
                });
            }
            NormTask::BuildInv { init_vars, state_vars, cond, inv, fuel } => {
                let body_r = vals.pop().unwrap_or_else(|| Region::Block(Vec::new()));
                vals.push(Region::InvariantLoop {
                    init_vars: init_vars.to_vec(),
                    state_vars: state_vars.to_vec(),
                    cond: Box::new(cond.clone()),
                    invariant_pred: Box::new(inv.clone()),
                    fuel_measure: Box::new(fuel.clone()),
                    body: Box::new(body_r),
                });
            }
        }
    }
    vals.pop().unwrap_or_else(|| Region::Block(Vec::new()))
}

fn push_unique_param(loop_params: &mut Vec<(ValId, ValType)>, id: ValId, ty: ValType) {
    let exists = match loop_params.as_slice() {
        [] => false,
        [(s0, _)] => *s0 == id,
        [(s0, _), (s1, _)] => *s0 == id || *s1 == id,
        s => {
            let mut i = 0;
            let mut hit = false;
            while i < s.len() {
                if s[i].0 == id {
                    hit = true;
                    break;
                }
                i += 1;
            }
            hit
        }
    };
    if !exists {
        loop_params.push((id, ty));
    }
}

/// Splits an `InvariantLoop` deterministically into `VC_Init`, `VC_Preservation`, and `VC_Exit`.
pub fn split_invariant_loop(
    init_params: Vec<(ValId, ValType)>,
    precondition: Option<Region>,
    loop_region: &Region,
    postcondition: Region,
) -> Result<LoopVcs, VcError> {
    let Region::InvariantLoop { init_vars, state_vars, cond, invariant_pred, fuel_measure, body } = loop_region
    else {
        return Err(VcError::NotAnInvariantLoop);
    };
    if init_vars.len() != state_vars.len() {
        return Err(VcError::ArityMismatch);
    }
    if !precondition.as_ref().is_none_or(validate_read_only)
        || !validate_read_only(cond)
        || !validate_read_only(invariant_pred)
        || !validate_read_only(fuel_measure)
        || !validate_read_only(&postcondition)
    {
        return Err(VcError::ImpureSpecificationRegion);
    }
    if precondition.as_ref().is_some_and(|p| has_escaping_flow(p, 0, false, false))
        || has_escaping_flow(cond, 0, false, false)
        || has_escaping_flow(invariant_pred, 0, false, false)
        || has_escaping_flow(fuel_measure, 0, false, false)
        || has_escaping_flow(&postcondition, 0, false, false)
        || has_escaping_flow(body, 0, true, true)
    {
        return Err(VcError::UnstructuredControlFlow);
    }

    let mut max_param_id = 0u32;
    bump_typed(&init_params, &mut max_param_id);
    bump_ids(init_vars, &mut max_param_id);
    bump_typed(state_vars, &mut max_param_id);
    let mut next_fresh = 1u32
        .max(max_param_id)
        .max(precondition.as_ref().map_or(0, max_val_id_in_region))
        .max(max_val_id_in_region(cond))
        .max(max_val_id_in_region(invariant_pred))
        .max(max_val_id_in_region(fuel_measure))
        .max(max_val_id_in_region(body))
        .max(max_val_id_in_region(&postcondition));
    let fresh = |nf: &mut u32| {
        let id = ValId(*nf);
        *nf = nf.saturating_add(1);
        id
    };

    let mut loop_params = match state_vars.as_slice() {
        [] => Vec::new(),
        [p0] => vec![*p0],
        [p0, p1] => vec![*p0, *p1],
        sv => sv.to_vec(),
    };
    match init_params.as_slice() {
        [] => {}
        [(id0, ty0)] => push_unique_param(&mut loop_params, *id0, *ty0),
        [(id0, ty0), (id1, ty1)] => {
            push_unique_param(&mut loop_params, *id0, *ty0);
            push_unique_param(&mut loop_params, *id1, *ty1);
        }
        ip => {
            let mut i = 0;
            while i < ip.len() {
                push_unique_param(&mut loop_params, ip[i].0, ip[i].1);
                i += 1;
            }
        }
    }

    let init_map: Vec<(ValId, ValId)> = match (state_vars.as_slice(), init_vars.as_slice()) {
        ([], []) => Vec::new(),
        ([(s0, _)], [i0]) => vec![(*s0, *i0)],
        ([(s0, _), (s1, _)], [i0, i1]) => vec![(*s0, *i0), (*s1, *i1)],
        (sv, iv) => {
            let mut m = Vec::with_capacity(sv.len());
            let mut idx = 0;
            while idx < sv.len() {
                m.push((sv[idx].0, iv[idx]));
                idx += 1;
            }
            m
        }
    };
    let init = VcObligation {
        kind: VcKind::Init,
        params: init_params,
        assumptions: match precondition {
            Some(p) => vec![p],
            None => Vec::new(),
        },
        goal: remap_region_vals(invariant_pred, &init_map, &mut next_fresh),
    };

    let (c_val, ok_val, one, zero, f_before, f_after, inv_after, fuel_dec, chk_raw) = (
        fresh(&mut next_fresh), fresh(&mut next_fresh), fresh(&mut next_fresh),
        fresh(&mut next_fresh), fresh(&mut next_fresh), fresh(&mut next_fresh),
        fresh(&mut next_fresh), fresh(&mut next_fresh), fresh(&mut next_fresh),
    );
    let (s_next, after_map): (Vec<(ValId, ValType)>, Vec<(ValId, ValId)>) = match state_vars.as_slice() {
        [] => (Vec::new(), Vec::new()),
        [(s0, ty0)] => {
            let n0 = fresh(&mut next_fresh);
            (vec![(n0, *ty0)], vec![(*s0, n0)])
        }
        [(s0, ty0), (s1, ty1)] => {
            let (n0, n1) = (fresh(&mut next_fresh), fresh(&mut next_fresh));
            (vec![(n0, *ty0), (n1, *ty1)], vec![(*s0, n0), (*s1, n1)])
        }
        sv => {
            let mut sn = Vec::with_capacity(sv.len());
            let mut am = Vec::with_capacity(sv.len());
            let mut idx = 0;
            while idx < sv.len() {
                let n = fresh(&mut next_fresh);
                sn.push((n, sv[idx].1));
                am.push((sv[idx].0, n));
                idx += 1;
            }
            (sn, am)
        }
    };

    let norm_body = normalize_loop_body_for_vc(body, 0, true);
    let body_block = match norm_body {
        Region::Block(_) => remap_region_vals(&norm_body, &[], &mut next_fresh),
        other => {
            let tmp: Vec<(ValId, ValType)> = state_vars.iter().map(|&(_, ty)| (fresh(&mut next_fresh), ty)).collect();
            let tmp_ids: Vec<ValId> = tmp.iter().map(|&(id, _)| id).collect();
            let remapped = remap_region_vals(&other, &[], &mut next_fresh);
            Region::Block(vec![Stmt::Region { results: tmp, region: remapped }, Stmt::Yield(tmp_ids)])
        }
    };

    let slet = |dst, op| Stmt::Let { dst, ty: ValType::I32, op };
    let sreg = |res, reg| Stmt::Region { results: res, region: reg };
    let then_branch = Region::Block(vec![
        sreg(vec![(f_before, ValType::I64)], remap_region_vals(fuel_measure, &[], &mut next_fresh)),
        sreg(s_next, body_block),
        sreg(vec![(inv_after, ValType::I32)], remap_region_vals(invariant_pred, &after_map, &mut next_fresh)),
        sreg(vec![(f_after, ValType::I64)], remap_region_vals(fuel_measure, &after_map, &mut next_fresh)),
        slet(zero, Op::ConstI32(0)),
        slet(fuel_dec, Op::Bin(BinOp::I64LtU, f_after, f_before)),
        slet(chk_raw, Op::Select { cond: inv_after, true_val: fuel_dec, false_val: zero }),
        Stmt::Yield(vec![chk_raw]),
    ]);
    let else_branch = Region::Block(vec![slet(one, Op::ConstI32(1)), Stmt::Yield(vec![one])]);
    let loop_params_pres = match loop_params.as_slice() {
        [] => Vec::new(),
        [p0] => vec![*p0],
        [p0, p1] => vec![*p0, *p1],
        lp => lp.to_vec(),
    };
    let preservation = VcObligation {
        kind: VcKind::Preservation,
        params: loop_params_pres,
        assumptions: vec![remap_region_vals(invariant_pred, &[], &mut next_fresh)],
        goal: Region::Block(vec![
            sreg(vec![(c_val, ValType::I32)], remap_region_vals(cond, &[], &mut next_fresh)),
            sreg(vec![(ok_val, ValType::I32)], Region::IfElse {
                cond: c_val,
                then_region: Box::new(then_branch),
                else_region: Box::new(else_branch),
                results: vec![ValType::I32],
            }),
            Stmt::Yield(vec![ok_val]),
        ]),
    };

    let (ec, ez) = (fresh(&mut next_fresh), fresh(&mut next_fresh));
    let not_cond = Region::Block(vec![
        sreg(vec![(ec, ValType::I32)], remap_region_vals(cond, &[], &mut next_fresh)),
        slet(ez, Op::Un(UnOp::I32Eqz, ec)),
        Stmt::Yield(vec![ez]),
    ]);
    let exit = VcObligation {
        kind: VcKind::Exit,
        params: loop_params,
        assumptions: vec![remap_region_vals(invariant_pred, &[], &mut next_fresh), not_cond],
        goal: remap_region_vals(&postcondition, &[], &mut next_fresh),
    };
    Ok(LoopVcs { init, preservation, exit })
}

fn eval_assumption_holds(
    module: &Module,
    registry: &StratumRegistry,
    assumption: &Region,
    bindings: &[(ValId, Val)],
    heap: &HeapState,
) -> bool {
    let mut h_chk = if heap.memories.is_empty() && heap.globals.is_empty() {
        HeapState { memories: Vec::new(), globals: Vec::new(), fuel_remaining: heap.fuel_remaining }
    } else {
        heap.clone()
    };
    matches!(
        eval_region_first(module, registry, assumption, bindings, &mut h_chk),
        Ok(Some(v)) if v.as_i32().unwrap_or(0) != 0
    )
}

/// Evaluates a concrete test point against one loop-free `VcObligation`.
pub fn eval_vc(module: &Module, registry: &StratumRegistry, vc: &VcObligation, args: &[Val], mut heap: HeapState) -> VcEvalResult {
    if args.len() != vc.params.len() {
        return VcEvalResult::Violated(None);
    }
    let mut inline_binds = [(ValId(0), Val::I32(0)); 8];
    let spill_binds: Vec<(ValId, Val)>;
    let bindings: &[(ValId, Val)] = match (vc.params.as_slice(), args) {
        ([], []) => &[],
        ([(id0, ty0)], [v0]) => {
            if v0.val_type() != *ty0 {
                return VcEvalResult::Violated(None);
            }
            inline_binds[0] = (*id0, *v0);
            &inline_binds[..1]
        }
        ([(id0, ty0), (id1, ty1)], [v0, v1]) => {
            if v0.val_type() != *ty0 || v1.val_type() != *ty1 {
                return VcEvalResult::Violated(None);
            }
            inline_binds[0] = (*id0, *v0);
            inline_binds[1] = (*id1, *v1);
            &inline_binds[..2]
        }
        (ps, vs) if ps.len() <= 8 => {
            let mut i = 0;
            while i < ps.len() {
                if vs[i].val_type() != ps[i].1 {
                    return VcEvalResult::Violated(None);
                }
                inline_binds[i] = (ps[i].0, vs[i]);
                i += 1;
            }
            &inline_binds[..ps.len()]
        }
        (ps, vs) => {
            let mut sb = Vec::with_capacity(ps.len());
            let mut i = 0;
            while i < ps.len() {
                if vs[i].val_type() != ps[i].1 {
                    return VcEvalResult::Violated(None);
                }
                sb.push((ps[i].0, vs[i]));
                i += 1;
            }
            spill_binds = sb;
            &spill_binds
        }
    };
    match vc.assumptions.as_slice() {
        [] => {}
        [a0] => {
            if !eval_assumption_holds(module, registry, a0, bindings, &heap) {
                return VcEvalResult::Vacuous;
            }
        }
        [a0, a1] => {
            if !eval_assumption_holds(module, registry, a0, bindings, &heap)
                || !eval_assumption_holds(module, registry, a1, bindings, &heap)
            {
                return VcEvalResult::Vacuous;
            }
        }
        assumps => {
            let mut i = 0;
            while i < assumps.len() {
                if !eval_assumption_holds(module, registry, &assumps[i], bindings, &heap) {
                    return VcEvalResult::Vacuous;
                }
                i += 1;
            }
        }
    }
    match eval_region_first(module, registry, &vc.goal, bindings, &mut heap) {
        Err(trap) => VcEvalResult::Violated(Some(trap)),
        Ok(Some(Val::I32(v))) if v != 0 => VcEvalResult::Holds,
        Ok(Some(Val::I64(v))) if v != 0 => VcEvalResult::Holds,
        Ok(_) => VcEvalResult::Violated(None),
    }
}
