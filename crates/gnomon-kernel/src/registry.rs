//! Stratum admission checker and Layer-0 DAG lowering gate.

use alloc::{boxed::Box, string::String, vec::Vec};
use crate::ir::*;
use crate::vc::{max_val_id_in_region, remap_region_vals, validate_read_only_with_registry};

#[derive(Clone, Copy, PartialEq, Eq, Debug)] pub enum LawKind { Algebraic, MemoryFrame { untouched_mem: MemId } }

/// Machine-proved rewrite or memory-frame law bundled with a promoted `Stratum`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Law {
    pub name: String, pub kind: LawKind, pub params: Vec<(ValId, ValType)>,
    pub precondition: Option<Region>, pub lhs: Region, pub rhs: Region, pub proof_digest: [u8; 32],
}

/// Named typed operation defined acyclically over Layer `0 .. layer - 1`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StratumOp {
    pub id: StratumId, pub name: String, pub layer: u16,
    pub params: Vec<(ValId, ValType)>, pub results: Vec<ValType>, pub body: Region, pub docstring: String,
}

/// Paired sub-abstraction: acyclic Layer-`k` op + proved shortcut/frame law(s).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stratum { pub op: StratumOp, pub laws: Vec<Law> }

impl Drop for Stratum {
    fn drop(&mut self) {
        if !self.laws.is_empty() && self.laws.len() <= 2 {
            let _ = self.laws.pop();
            let _ = self.laws.pop();
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum RegistryError {
    InvalidLayerZero, DuplicateName, DuplicateId, UnknownStratum(StratumId),
    NonAcyclicLayer { caller_layer: u16, callee: StratumId, callee_layer: u16 },
    MissingProvedLaw, EmptyProofDigest, TypeMismatch, UndefinedVal(ValId),
}

fn check_layer_non_zero(layer: u16) -> Result<(), RegistryError> {
    if layer == 0 { Err(RegistryError::InvalidLayerZero) } else { Ok(()) }
}

fn check_law_digest(d: &[u8; 32]) -> Result<(), RegistryError> {
    let nz = (d[0] | d[1] | d[2] | d[3] | d[4] | d[5] | d[6] | d[7])
        | (d[8] | d[9] | d[10] | d[11] | d[12] | d[13] | d[14] | d[15])
        | (d[16] | d[17] | d[18] | d[19] | d[20] | d[21] | d[22] | d[23])
        | (d[24] | d[25] | d[26] | d[27] | d[28] | d[29] | d[30] | d[31]);
    if nz == 0 { Err(RegistryError::EmptyProofDigest) } else { Ok(()) }
}

fn check_callee_layer(caller_layer: u16, callee: StratumId, callee_layer: u16) -> Result<(), RegistryError> {
    if callee_layer >= caller_layer {
        Err(RegistryError::NonAcyclicLayer { caller_layer, callee, callee_layer })
    } else {
        Ok(())
    }
}

#[derive(Clone)]
struct RetTys {
    tys: [ValType; 8],
    len: usize,
    spill: Vec<ValType>,
}

impl Default for RetTys {
    fn default() -> Self {
        Self { tys: [ValType::I32; 8], len: 0, spill: Vec::new() }
    }
}

impl PartialEq for RetTys {
    fn eq(&self, other: &Self) -> bool {
        self.eq_slice(other.as_slice())
    }
}
impl Eq for RetTys {}

impl RetTys {
    fn push(&mut self, ty: ValType) {
        if (self.len >> 3) == 0 {
            self.tys[self.len & 7] = ty;
            self.len += 1;
        } else {
            if self.len == 8 {
                self.spill.extend_from_slice(&self.tys);
            }
            self.spill.push(ty);
            self.len += 1;
        }
    }
    fn as_slice(&self) -> &[ValType] {
        if (self.len >> 3) == 0 || self.len == 8 {
            &self.tys[..self.len.min(8)]
        } else {
            self.spill.as_slice()
        }
    }
    fn from_slice(s: &[ValType]) -> Self {
        let mut r = Self::default();
        match s {
            [] => {}
            [a] => r.push(*a),
            [a, b] => { r.push(*a); r.push(*b); }
            _ => {
                let mut i = 0;
                while i < s.len() { r.push(s[i]); i += 1; }
            }
        }
        r
    }
    fn from_pairs(s: &[(ValId, ValType)]) -> Self {
        let mut r = Self::default();
        match s {
            [] => {}
            [(_, a)] => r.push(*a),
            [(_, a), (_, b)] => { r.push(*a); r.push(*b); }
            _ => {
                let mut i = 0;
                while i < s.len() { r.push(s[i].1); i += 1; }
            }
        }
        r
    }
    fn eq_slice(&self, s: &[ValType]) -> bool {
        let a = self.as_slice();
        if a.len() != s.len() {
            return false;
        }
        match (a, s) {
            ([], []) => true,
            ([x], [y]) => x == y,
            ([x0, x1], [y0, y1]) => x0 == y0 && x1 == y1,
            _ => {
                let mut i = 0;
                while i < a.len() {
                    if a[i] != s[i] { return false; }
                    i += 1;
                }
                true
            }
        }
    }
    fn eq_pairs(&self, s: &[(ValId, ValType)]) -> bool {
        let a = self.as_slice();
        if a.len() != s.len() {
            return false;
        }
        match (a, s) {
            ([], []) => true,
            ([x], [(_, y)]) => x == y,
            ([x0, x1], [(_, y0), (_, y1)]) => x0 == y0 && x1 == y1,
            _ => {
                let mut i = 0;
                while i < a.len() {
                    if a[i] != s[i].1 { return false; }
                    i += 1;
                }
                true
            }
        }
    }
}

struct TypeEnv {
    entries: [(ValId, ValType); 16],
    len: usize,
    spill: Vec<(ValId, ValType)>,
}

impl Default for TypeEnv {
    fn default() -> Self {
        Self { entries: [(ValId(0), ValType::I32); 16], len: 0, spill: Vec::new() }
    }
}

impl TypeEnv {
    fn from_slice(params: &[(ValId, ValType)]) -> Self {
        let mut e = Self::default();
        e.extend_slice(params);
        e
    }
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
    fn push(&mut self, id: ValId, ty: ValType) {
        if (self.len >> 4) == 0 {
            self.entries[self.len & 15] = (id, ty);
            self.len += 1;
        } else {
            self.spill.push((id, ty));
            self.len += 1;
        }
    }
    fn extend_slice(&mut self, pairs: &[(ValId, ValType)]) {
        match pairs {
            [] => {}
            [p0] => self.push(p0.0, p0.1),
            [p0, p1] => { self.push(p0.0, p0.1); self.push(p1.0, p1.1); }
            _ => {
                let mut i = 0;
                while i < pairs.len() {
                    self.push(pairs[i].0, pairs[i].1);
                    i += 1;
                }
            }
        }
    }
    fn lookup(&self, id: ValId) -> Result<ValType, RegistryError> {
        if self.len == 0 {
            return Err(RegistryError::UndefinedVal(id));
        }
        if self.len == 1 {
            return if self.entries[0].0 == id { Ok(self.entries[0].1) } else { Err(RegistryError::UndefinedVal(id)) };
        }
        if self.len == 2 {
            if self.entries[1].0 == id { return Ok(self.entries[1].1); }
            if self.entries[0].0 == id { return Ok(self.entries[0].1); }
            return Err(RegistryError::UndefinedVal(id));
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
        Err(RegistryError::UndefinedVal(id))
    }
}

/// TCB registry gating all candidate and promoted Strata.
#[derive(Clone, Debug, Default)]
pub struct StratumRegistry {
    candidates: Vec<StratumOp>,
    promoted: Vec<Stratum>,
    read_only_ids: Vec<StratumId>,
}

impl Drop for StratumRegistry {
    fn drop(&mut self) {
        if !self.promoted.is_empty() && self.promoted.len() <= 2 {
            let _ = self.promoted.pop();
            let _ = self.promoted.pop();
        }
        if !self.candidates.is_empty() && self.candidates.len() <= 2 {
            let _ = self.candidates.pop();
            let _ = self.candidates.pop();
        }
    }
}

impl StratumRegistry {
    pub fn new() -> Self { Self::default() }
    pub fn promoted(&self) -> &[Stratum] { &self.promoted }
    pub fn candidates(&self) -> &[StratumOp] { &self.candidates }
    pub fn get_stratum(&self, id: StratumId) -> Option<&Stratum> {
        match self.promoted.as_slice() {
            [] => None,
            [s0] => (s0.op.id == id).then_some(s0),
            [s0, s1] => if s0.op.id == id { Some(s0) } else if s1.op.id == id { Some(s1) } else { None },
            _ => self.promoted.iter().find(|s| s.op.id == id),
        }
    }
    pub fn get_op(&self, id: StratumId) -> Option<&StratumOp> {
        if let Some(s) = self.get_stratum(id) { return Some(&s.op); }
        match self.candidates.as_slice() {
            [] => None,
            [c0] => (c0.id == id).then_some(c0),
            _ => self.candidates.iter().find(|o| o.id == id),
        }
    }
    pub fn is_stratum_read_only(&self, id: StratumId) -> bool {
        match self.read_only_ids.as_slice() {
            [] => false,
            [r0] => *r0 == id,
            [r0, r1] => *r0 == id || *r1 == id,
            _ => self.read_only_ids.contains(&id),
        }
    }

    /// Registers an unpromoted candidate op after validating layer `>= 1`, acyclicity, and SSA types.
    pub fn register_candidate_op(&mut self, op: StratumOp) -> Result<StratumId, RegistryError> {
        self.validate_op(&op, false)?;
        let id = op.id;
        if validate_read_only_with_registry(&op.body, self) && !self.is_stratum_read_only(id) {
            self.read_only_ids.push(id);
        }
        self.candidates.push(op);
        Ok(id)
    }

    fn check_one_law(&self, law: &Law, stratum_op: &StratumOp) -> Result<(), RegistryError> {
        check_law_digest(&law.proof_digest)?;
        if let Some(pre) = &law.precondition {
            if !validate_read_only_with_registry(pre, self) {
                return Err(RegistryError::TypeMismatch);
            }
            let mut env = TypeEnv::from_slice(&law.params);
            if !self.check_region_entry(pre, &mut env, u16::MAX, true, Some(stratum_op))?.eq_slice(&[ValType::I32]) {
                return Err(RegistryError::TypeMismatch);
            }
        }
        let mut lhs_env = TypeEnv::from_slice(&law.params);
        let lhs_tys = self.check_region_entry(&law.lhs, &mut lhs_env, u16::MAX, true, Some(stratum_op))?;
        let mut rhs_env = TypeEnv::from_slice(&law.params);
        let rhs_tys = self.check_region_entry(&law.rhs, &mut rhs_env, u16::MAX, true, Some(stratum_op))?;
        if lhs_tys != rhs_tys { return Err(RegistryError::TypeMismatch); }
        Ok(())
    }

    /// Admits a verified `Stratum` (acyclic op over already-promoted callees + >= 1 non-empty proved law).
    pub fn promote_stratum(&mut self, stratum: Stratum) -> Result<StratumId, RegistryError> {
        match stratum.laws.as_slice() {
            [] => return Err(RegistryError::MissingProvedLaw),
            [law] => {
                self.validate_op(&stratum.op, true)?;
                self.check_one_law(law, &stratum.op)?;
            }
            laws => {
                self.validate_op(&stratum.op, true)?;
                for law in laws { self.check_one_law(law, &stratum.op)?; }
            }
        }
        let id = stratum.op.id;
        let cand_pos = match self.candidates.as_slice() {
            [] => None,
            [c0] => (c0.id == id).then_some(0),
            _ => self.candidates.iter().position(|c| c.id == id),
        };
        if let Some(pos) = cand_pos {
            self.candidates.remove(pos);
        }
        let ro_pos = match self.read_only_ids.as_slice() {
            [] => None,
            [r0] => (*r0 == id).then_some(0),
            [r0, r1] => if *r0 == id { Some(0) } else if *r1 == id { Some(1) } else { None },
            _ => self.read_only_ids.iter().position(|&rid| rid == id),
        };
        if let Some(pos) = ro_pos {
            self.read_only_ids.remove(pos);
        }
        if validate_read_only_with_registry(&stratum.op.body, self) {
            self.read_only_ids.push(id);
        }
        self.promoted.push(stratum);
        Ok(id)
    }

    fn validate_op(&self, op: &StratumOp, promoted_only: bool) -> Result<(), RegistryError> {
        check_layer_non_zero(op.layer)?;
        let dup_id = self.get_stratum(op.id).is_some()
            || (!promoted_only && self.get_op(op.id).is_some());
        if dup_id { return Err(RegistryError::DuplicateId); }
        let dup_prom_name = match self.promoted.as_slice() {
            [] => false,
            [s0] => s0.op.name == op.name,
            _ => self.promoted.iter().any(|s| s.op.name == op.name),
        };
        let dup_cand_name = match self.candidates.as_slice() {
            [] => false,
            [c0] => (!promoted_only || c0.id != op.id) && c0.name == op.name,
            _ => self.candidates.iter().any(|c| (!promoted_only || c.id != op.id) && c.name == op.name),
        };
        if dup_prom_name || dup_cand_name { return Err(RegistryError::DuplicateName); }
        let mut env = TypeEnv::from_slice(&op.params);
        if !self.check_region_entry(&op.body, &mut env, op.layer, promoted_only, None)?.eq_slice(&op.results) {
            return Err(RegistryError::TypeMismatch);
        }
        Ok(())
    }

    fn resolve_callee<'a>(
        &'a self,
        sid: StratumId,
        promoted_only: bool,
        self_op: Option<&'a StratumOp>,
    ) -> Result<&'a StratumOp, RegistryError> {
        if let Some(op) = self_op
            && op.id == sid
        {
            return Ok(op);
        }
        if promoted_only {
            self.get_stratum(sid).map(|s| &s.op).ok_or(RegistryError::UnknownStratum(sid))
        } else {
            self.get_op(sid).ok_or(RegistryError::UnknownStratum(sid))
        }
    }

    fn lookup_ty(id: ValId, env: &TypeEnv) -> Result<ValType, RegistryError> {
        env.lookup(id)
    }

    fn expect_ty(id: ValId, ty: ValType, env: &TypeEnv) -> Result<(), RegistryError> {
        if Self::lookup_ty(id, env)? == ty { Ok(()) } else { Err(RegistryError::TypeMismatch) }
    }

    #[inline(never)]
    fn check_op(op: &Op, declared_ty: ValType, env: &TypeEnv) -> Result<ValType, RegistryError> {
        match op {
            Op::ConstI32(_) | Op::MemorySize(_) => Ok(ValType::I32),
            Op::ConstI64(_) => Ok(ValType::I64),
            Op::Copy(v) => Self::lookup_ty(*v, env),
            Op::Select { cond, true_val, false_val } => {
                Self::expect_ty(*cond, ValType::I32, env)?;
                let t = Self::lookup_ty(*true_val, env)?;
                Self::expect_ty(*false_val, t, env)?;
                Ok(t)
            }
            Op::GlobalGet(_) => Ok(declared_ty),
            Op::Un(u, v) => { Self::expect_ty(*v, u.input_ty(), env)?; Ok(u.output_ty()) }
            Op::Bin(b, l, r) => { Self::expect_ty(*l, b.operand_ty(), env)?; Self::expect_ty(*r, b.operand_ty(), env)?; Ok(b.output_ty()) }
            Op::Load { addr, width, result_ty, .. } => {
                Self::expect_ty(*addr, ValType::I32, env)?;
                if *width == MemWidth::B8 && *result_ty != ValType::I64 {
                    return Err(RegistryError::TypeMismatch);
                }
                Ok(*result_ty)
            }
            Op::MemoryGrow { delta, .. } => { Self::expect_ty(*delta, ValType::I32, env)?; Ok(ValType::I32) }
        }
    }

    #[inline(never)]
    fn check_effect(eff: &EffectOp, env: &TypeEnv) -> Result<(), RegistryError> {
        match eff {
            EffectOp::Store { addr, val, width, .. } => {
                Self::expect_ty(*addr, ValType::I32, env)?;
                let vty = Self::lookup_ty(*val, env)?;
                if *width == MemWidth::B8 && vty != ValType::I64 { return Err(RegistryError::TypeMismatch); }
            }
            EffectOp::MemoryCopy { dst, src, len, .. } | EffectOp::MemoryFill { dst, val: src, len, .. } => {
                Self::expect_ty(*dst, ValType::I32, env)?;
                Self::expect_ty(*src, ValType::I32, env)?;
                Self::expect_ty(*len, ValType::I32, env)?;
            }
            EffectOp::GlobalSet { val, .. } => { Self::lookup_ty(*val, env)?; }
            EffectOp::Trap(_) | EffectOp::Nop => {}
        }
        Ok(())
    }

    fn record_exit_tys(
        yielded: &mut Option<RetTys>,
        vs: &[ValId],
        env: &TypeEnv,
    ) -> Result<(), RegistryError> {
        let mut cur = RetTys::default();
        match vs {
            [] => {}
            [v0] => cur.push(Self::lookup_ty(*v0, env)?),
            [v0, v1] => { cur.push(Self::lookup_ty(*v0, env)?); cur.push(Self::lookup_ty(*v1, env)?); }
            _ => {
                let mut i = 0;
                while i < vs.len() {
                    cur.push(Self::lookup_ty(vs[i], env)?);
                    i += 1;
                }
            }
        }
        match yielded {
            None => *yielded = Some(cur),
            Some(prev) if *prev == cur => {}
            Some(_) => return Err(RegistryError::TypeMismatch),
        }
        Ok(())
    }

    fn check_vals_defined(vs: &[ValId], env: &TypeEnv) -> Result<(), RegistryError> {
        match vs {
            [] => Ok(()),
            [v0] => Self::lookup_ty(*v0, env).map(|_| ()),
            [v0, v1] => { Self::lookup_ty(*v0, env)?; Self::lookup_ty(*v1, env).map(|_| ()) }
            _ => {
                let mut i = 0;
                while i < vs.len() {
                    Self::lookup_ty(vs[i], env)?;
                    i += 1;
                }
                Ok(())
            }
        }
    }

    fn check_flat_stmt(
        &self,
        stmt: &Stmt,
        env: &mut TypeEnv,
        yielded: &mut Option<RetTys>,
        caller_layer: u16,
        promoted_only: bool,
        self_op: Option<&StratumOp>,
    ) -> Result<(), RegistryError> {
        match stmt {
            Stmt::Let { dst, ty, op } => {
                if Self::check_op(op, *ty, env)? != *ty { return Err(RegistryError::TypeMismatch); }
                env.push(*dst, *ty);
            }
            Stmt::Effect(eff) => Self::check_effect(eff, env)?,
            Stmt::Call { results, target, args } => match target {
                CallTarget::Stratum(sid) => {
                    let callee = self.resolve_callee(*sid, promoted_only, self_op)?;
                    check_callee_layer(caller_layer, *sid, callee.layer)?;
                    if args.len() != callee.params.len() || results.len() != callee.results.len() {
                        return Err(RegistryError::TypeMismatch);
                    }
                    match results.as_slice() {
                        [] => {}
                        [r0] => if r0.1 != callee.results[0] { return Err(RegistryError::TypeMismatch); },
                        _ => {
                            let mut i = 0;
                            while i < results.len() {
                                if results[i].1 != callee.results[i] { return Err(RegistryError::TypeMismatch); }
                                i += 1;
                            }
                        }
                    }
                    env.extend_slice(results);
                    match args.as_slice() {
                        [] => {}
                        [a0] => Self::expect_ty(*a0, callee.params[0].1, env)?,
                        _ => {
                            let mut j = 0;
                            while j < args.len() {
                                Self::expect_ty(args[j], callee.params[j].1, env)?;
                                j += 1;
                            }
                        }
                    }
                }
                _ => {
                    Self::check_vals_defined(args, env)?;
                    env.extend_slice(results);
                }
            },
            Stmt::Yield(vs) | Stmt::Return(vs) => Self::record_exit_tys(yielded, vs, env)?,
            Stmt::Break { depth, cond, values } => {
                if let Some(c) = cond { Self::expect_ty(*c, ValType::I32, env)?; }
                if *depth == 0 {
                    Self::record_exit_tys(yielded, values, env)?;
                } else {
                    Self::check_vals_defined(values, env)?;
                }
            }
            Stmt::Continue { cond, values, .. } => {
                if let Some(c) = cond { Self::expect_ty(*c, ValType::I32, env)?; }
                Self::check_vals_defined(values, env)?;
            }
            Stmt::Region { .. } => unreachable!(),
        }
        Ok(())
    }

    fn check_region_entry(
        &self,
        region: &Region,
        env: &mut TypeEnv,
        caller_layer: u16,
        promoted_only: bool,
        self_op: Option<&StratumOp>,
    ) -> Result<RetTys, RegistryError> {
        if let Region::Block(stmts) = region {
            match stmts.as_slice() {
                [] => return Ok(RetTys::default()),
                [s0] if !matches!(s0, Stmt::Region { .. }) => {
                    let saved = env.len();
                    let mut yielded = None;
                    let res = self.check_flat_stmt(s0, env, &mut yielded, caller_layer, promoted_only, self_op);
                    env.truncate(saved);
                    res?;
                    return Ok(yielded.unwrap_or_default());
                }
                _ => {}
            }
        }
        self.check_region(region, env, caller_layer, promoted_only, self_op)
    }

    fn check_region(
        &self,
        root: &Region,
        env: &mut TypeEnv,
        root_caller_layer: u16,
        promoted_only: bool,
        self_op: Option<&StratumOp>,
    ) -> Result<RetTys, RegistryError> {
        enum CheckTask<'a> {
            Enter { region: &'a Region, caller_layer: u16 },
            StepBlock {
                stmts: &'a [Stmt],
                idx: usize,
                saved: usize,
                yielded: Option<RetTys>,
                caller_layer: u16,
            },
            FinishSubRegion {
                results: &'a [(ValId, ValType)],
                stmts: &'a [Stmt],
                next_idx: usize,
                saved: usize,
                yielded: Option<RetTys>,
                caller_layer: u16,
            },
            FinishIf { results: &'a [ValType] },
            RestoreEnv { saved: usize },
            FinishInv { state_vars: &'a [(ValId, ValType)], saved: usize },
        }

        let mut tasks = Stack2::with_first(CheckTask::Enter { region: root, caller_layer: root_caller_layer });
        let mut vals = Stack2::<RetTys>::new();
        'outer: while let Some(task) = tasks.pop() {
            match task {
                CheckTask::Enter { region, caller_layer } => match region {
                    Region::Block(stmts) => tasks.push(CheckTask::StepBlock {
                        stmts,
                        idx: 0,
                        saved: env.len(),
                        yielded: None,
                        caller_layer,
                    }),
                    Region::IfElse { cond, then_region, else_region, results } => {
                        Self::expect_ty(*cond, ValType::I32, env)?;
                        tasks.push(CheckTask::FinishIf { results });
                        tasks.push(CheckTask::Enter { region: else_region, caller_layer });
                        tasks.push(CheckTask::Enter { region: then_region, caller_layer });
                    }
                    Region::BoundedLoop { init_vars, state_vars, body, .. } => {
                        if init_vars.len() != state_vars.len() {
                            return Err(RegistryError::TypeMismatch);
                        }
                        let mut i = 0;
                        while i < init_vars.len() {
                            Self::expect_ty(init_vars[i], state_vars[i].1, env)?;
                            i += 1;
                        }
                        let saved = env.len();
                        env.extend_slice(state_vars);
                        tasks.push(CheckTask::RestoreEnv { saved });
                        tasks.push(CheckTask::Enter { region: body, caller_layer });
                    }
                    Region::InvariantLoop { init_vars, state_vars, cond, invariant_pred, fuel_measure, body } => {
                        if init_vars.len() != state_vars.len() {
                            return Err(RegistryError::TypeMismatch);
                        }
                        let mut i = 0;
                        while i < init_vars.len() {
                            Self::expect_ty(init_vars[i], state_vars[i].1, env)?;
                            i += 1;
                        }
                        let saved = env.len();
                        env.extend_slice(state_vars);
                        tasks.push(CheckTask::FinishInv { state_vars, saved });
                        tasks.push(CheckTask::Enter { region: body, caller_layer });
                        tasks.push(CheckTask::Enter { region: fuel_measure, caller_layer });
                        tasks.push(CheckTask::Enter { region: invariant_pred, caller_layer });
                        tasks.push(CheckTask::Enter { region: cond, caller_layer });
                    }
                },
                CheckTask::StepBlock { stmts, mut idx, saved, mut yielded, caller_layer } => {
                    while idx < stmts.len() {
                        if let Stmt::Region { results, region: sub } = &stmts[idx] {
                            tasks.push(CheckTask::FinishSubRegion {
                                results,
                                stmts,
                                next_idx: idx + 1,
                                saved,
                                yielded,
                                caller_layer,
                            });
                            tasks.push(CheckTask::Enter { region: sub, caller_layer });
                            continue 'outer;
                        }
                        if let Err(e) = self.check_flat_stmt(
                            &stmts[idx],
                            env,
                            &mut yielded,
                            caller_layer,
                            promoted_only,
                            self_op,
                        ) {
                            env.truncate(saved);
                            return Err(e);
                        }
                        idx += 1;
                    }
                    env.truncate(saved);
                    vals.push(yielded.unwrap_or_default());
                }
                CheckTask::FinishSubRegion { results, stmts, next_idx, saved, yielded, caller_layer } => {
                    let tys = vals.pop().unwrap_or_default();
                    if !tys.eq_pairs(results) {
                        env.truncate(saved);
                        return Err(RegistryError::TypeMismatch);
                    }
                    env.extend_slice(results);
                    tasks.push(CheckTask::StepBlock { stmts, idx: next_idx, saved, yielded, caller_layer });
                }
                CheckTask::FinishIf { results } => {
                    let else_tys = vals.pop().unwrap_or_default();
                    let then_tys = vals.pop().unwrap_or_default();
                    if !then_tys.eq_slice(results) || !else_tys.eq_slice(results) {
                        return Err(RegistryError::TypeMismatch);
                    }
                    vals.push(RetTys::from_slice(results));
                }
                CheckTask::RestoreEnv { saved } => {
                    env.truncate(saved);
                }
                CheckTask::FinishInv { state_vars, saved } => {
                    let _body_tys = vals.pop().unwrap_or_default();
                    let fuel_tys = vals.pop().unwrap_or_default();
                    let inv_tys = vals.pop().unwrap_or_default();
                    let cond_tys = vals.pop().unwrap_or_default();
                    env.truncate(saved);
                    if !cond_tys.eq_slice(&[ValType::I32])
                        || !inv_tys.eq_slice(&[ValType::I32])
                        || !fuel_tys.eq_slice(&[ValType::I64])
                    {
                        return Err(RegistryError::TypeMismatch);
                    }
                    vals.push(RetTys::from_pairs(state_vars));
                }
            }
        }
        Ok(vals.pop().unwrap_or_default())
    }

    /// Expands all `CallTarget::Stratum` calls into Layer-0 primitives.
    pub fn lower_region_to_layer0(&self, region: &Region, next_val: &mut u32) -> Result<Region, RegistryError> {
        *next_val = (*next_val).max(max_val_id_in_region(region));
        self.lower_inner(region, next_val)
    }

    fn lower_inner(&self, root: &Region, next_val: &mut u32) -> Result<Region, RegistryError> {
        enum LowerTask<'a> {
            Enter(&'a Region),
            StepBlock { stmts: &'a [Stmt], idx: usize, out: Vec<Stmt> },
            FinishSubRegion { results: &'a [(ValId, ValType)], stmts: &'a [Stmt], next_idx: usize, out: Vec<Stmt> },
            FinishStratumCall {
                results: &'a [(ValId, ValType)],
                args: &'a [ValId],
                params: &'a [(ValId, ValType)],
                stmts: &'a [Stmt],
                next_idx: usize,
                out: Vec<Stmt>,
            },
            BuildIf { cond: ValId, results: &'a [ValType] },
            BuildBounded { max_iters: u32, init_vars: &'a [ValId], state_vars: &'a [(ValId, ValType)] },
            BuildInv { init_vars: &'a [ValId], state_vars: &'a [(ValId, ValType)] },
        }

        let mut tasks = Stack2::with_first(LowerTask::Enter(root));
        let mut vals = Stack2::<Region>::new();
        'outer_low: while let Some(task) = tasks.pop() {
            match task {
                LowerTask::Enter(region) => match region {
                    Region::Block(stmts) => tasks.push(LowerTask::StepBlock {
                        stmts,
                        idx: 0,
                        out: Vec::new(),
                    }),
                    Region::IfElse { cond, then_region, else_region, results } => {
                        tasks.push(LowerTask::BuildIf { cond: *cond, results });
                        tasks.push(LowerTask::Enter(else_region));
                        tasks.push(LowerTask::Enter(then_region));
                    }
                    Region::BoundedLoop { max_iters, init_vars, state_vars, body } => {
                        tasks.push(LowerTask::BuildBounded { max_iters: *max_iters, init_vars, state_vars });
                        tasks.push(LowerTask::Enter(body));
                    }
                    Region::InvariantLoop { init_vars, state_vars, cond, invariant_pred, fuel_measure, body } => {
                        tasks.push(LowerTask::BuildInv { init_vars, state_vars });
                        tasks.push(LowerTask::Enter(body));
                        tasks.push(LowerTask::Enter(fuel_measure));
                        tasks.push(LowerTask::Enter(invariant_pred));
                        tasks.push(LowerTask::Enter(cond));
                    }
                },
                LowerTask::StepBlock { stmts, mut idx, mut out } => {
                    while idx < stmts.len() {
                        match &stmts[idx] {
                            Stmt::Call { results, target: CallTarget::Stratum(sid), args } => {
                                let op = self.get_op(*sid).ok_or(RegistryError::UnknownStratum(*sid))?;
                                if args.len() != op.params.len() {
                                    return Err(RegistryError::TypeMismatch);
                                }
                                tasks.push(LowerTask::FinishStratumCall {
                                    results,
                                    args,
                                    params: &op.params,
                                    stmts,
                                    next_idx: idx + 1,
                                    out,
                                });
                                tasks.push(LowerTask::Enter(&op.body));
                                continue 'outer_low;
                            }
                            Stmt::Region { results, region: sub } => {
                                tasks.push(LowerTask::FinishSubRegion { results, stmts, next_idx: idx + 1, out });
                                tasks.push(LowerTask::Enter(sub));
                                continue 'outer_low;
                            }
                            other => {
                                out.push(other.clone());
                                idx += 1;
                            }
                        }
                    }
                    vals.push(Region::Block(out));
                }
                LowerTask::FinishSubRegion { results, stmts, next_idx, mut out } => {
                    let sub = vals.pop().unwrap_or_else(|| Region::Block(Vec::new()));
                    out.push(Stmt::Region { results: results.to_vec(), region: sub });
                    tasks.push(LowerTask::StepBlock { stmts, idx: next_idx, out });
                }
                LowerTask::FinishStratumCall { results, args, params, stmts, next_idx, mut out } => {
                    let lowered = vals.pop().unwrap_or_else(|| Region::Block(Vec::new()));
                    let map: Vec<(ValId, ValId)> = params.iter().map(|&(p, _)| p).zip(args.iter().copied()).collect();
                    let remapped = remap_region_vals(&lowered, &map, next_val);
                    out.push(Stmt::Region { results: results.to_vec(), region: remapped });
                    tasks.push(LowerTask::StepBlock { stmts, idx: next_idx, out });
                }
                LowerTask::BuildIf { cond, results } => {
                    let else_r = vals.pop().unwrap_or_else(|| Region::Block(Vec::new()));
                    let then_r = vals.pop().unwrap_or_else(|| Region::Block(Vec::new()));
                    vals.push(Region::IfElse {
                        cond,
                        results: results.to_vec(),
                        then_region: Box::new(then_r),
                        else_region: Box::new(else_r),
                    });
                }
                LowerTask::BuildBounded { max_iters, init_vars, state_vars } => {
                    let body_r = vals.pop().unwrap_or_else(|| Region::Block(Vec::new()));
                    vals.push(Region::BoundedLoop {
                        max_iters,
                        init_vars: init_vars.to_vec(),
                        state_vars: state_vars.to_vec(),
                        body: Box::new(body_r),
                    });
                }
                LowerTask::BuildInv { init_vars, state_vars } => {
                    let body_r = vals.pop().unwrap_or_else(|| Region::Block(Vec::new()));
                    let fuel_r = vals.pop().unwrap_or_else(|| Region::Block(Vec::new()));
                    let inv_r = vals.pop().unwrap_or_else(|| Region::Block(Vec::new()));
                    let cond_r = vals.pop().unwrap_or_else(|| Region::Block(Vec::new()));
                    vals.push(Region::InvariantLoop {
                        init_vars: init_vars.to_vec(),
                        state_vars: state_vars.to_vec(),
                        cond: Box::new(cond_r),
                        invariant_pred: Box::new(inv_r),
                        fuel_measure: Box::new(fuel_r),
                        body: Box::new(body_r),
                    });
                }
            }
        }
        Ok(vals.pop().unwrap_or_else(|| Region::Block(Vec::new())))
    }
}
