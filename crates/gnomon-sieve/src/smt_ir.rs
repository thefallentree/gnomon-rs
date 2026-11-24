//! Shared `GnomonIR` -> `QF_ABV` symbolic execution and verification condition encoder.

use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use gnomon_kernel::{
    BinOp, CallTarget, EffectOp, FuncId, GlobalId, HostContract, MAX_CALL_DEPTH, MAX_WASM_PAGES,
    MemId, MemWidth, Module, Op, Region, RegionNode, RegionRef, SliceBound, Span, Stmt, StratumId,
    StratumRegistry, TrapCode, UnOp, Val, ValId, ValType, VcObligation, WASM_PAGE_SIZE,
    validate_read_only_with_registry,
};

use crate::{
    ContractSpec, EquivOptions, SieveError, SliceBoundExpr, SmtModel, SmtResult, StackRefinement,
};

const MAX_CONST_MEM_OP_BYTES: usize = 1024;
const MAX_SYM_MEM_OP_BYTES: usize = 64;
pub(crate) const MAX_SMT_LOOP_UNROLL: u32 = 64;
const MAX_UF_CALLS_PER_STRATUM: usize = 64;
const MAX_SMT_CALLS: usize = 256;
const MAX_SMT_STEPS: usize = 20_000;
const MAX_TRACKED_MEM_ADDRS: usize = 512;

/// Shared total symbolic encoding budget across all control-flow branches, calls, and
/// loop iterations within a single SMT query.
///
/// Backed by `Rc<Cell<_>>` so cloning `ExecState` across `IfElse` branches, host-contract
/// pre/post checks, and equivalence LHS/RHS evaluations shares one aggregate budget,
/// preventing exponential call-tree or nested-loop blowup before `check_sat()`.
#[derive(Clone)]
struct SymBudget {
    calls: Rc<Cell<usize>>,
    steps: Rc<Cell<usize>>,
    exceeded: Rc<Cell<bool>>,
}

impl SymBudget {
    fn new() -> Self {
        Self {
            calls: Rc::new(Cell::new(0)),
            steps: Rc::new(Cell::new(0)),
            exceeded: Rc::new(Cell::new(false)),
        }
    }

    fn is_exceeded(&self) -> bool {
        self.exceeded.get()
    }

    fn charge_call(&self) -> bool {
        if self.exceeded.get() {
            return false;
        }
        let next = self.calls.get().saturating_add(1);
        self.calls.set(next);
        if next > MAX_SMT_CALLS {
            self.exceeded.set(true);
            return false;
        }
        true
    }

    fn charge_steps(&self, n: usize) -> bool {
        if self.exceeded.get() {
            return false;
        }
        let next = self.steps.get().saturating_add(n);
        self.steps.set(next);
        if next > MAX_SMT_STEPS {
            self.exceeded.set(true);
            return false;
        }
        true
    }
}

/// Shared Ackermann Uninterpreted-Function (UF) congruence table for pure-total Strata.
///
/// Soundness: every `StratumId` in `abstract_strata` is statically verified to be pure,
/// state-independent, deterministic, and trap-free (`is_pure_total_stratum`). Therefore
/// the concrete function satisfies all Ackermann congruence axioms; an `UNSAT` result under
/// UF abstraction strictly implies `UNSAT` under exact Layer-0 inlining. A `SAT` result may
/// be spurious and triggers exact concrete Layer-0 fallback (CEGAR).
type UfCallRecord<T> = (Vec<SymVal<T>>, Vec<SymVal<T>>);

struct UfTable<T> {
    abstract_strata: BTreeSet<StratumId>,
    prefix: String,
    next_id: u32,
    calls: BTreeMap<StratumId, Vec<UfCallRecord<T>>>,
    overflow: bool,
}

impl<T: Clone> UfTable<T> {
    fn new(abstract_strata: BTreeSet<StratumId>, prefix: String) -> Rc<RefCell<Self>> {
        Rc::new(RefCell::new(Self {
            abstract_strata,
            prefix,
            next_id: 0,
            calls: BTreeMap::new(),
            overflow: false,
        }))
    }

    fn apply<B: SmtTarget<Term = T>>(
        &mut self,
        b: &mut B,
        sid: StratumId,
        args: &[SymVal<T>],
        result_tys: &[ValType],
    ) -> Vec<SymVal<T>> {
        let cid = self.next_id;
        self.next_id += 1;
        let outs: Vec<SymVal<T>> = result_tys
            .iter()
            .enumerate()
            .map(|(r, &ty)| SymVal {
                ty,
                term: b.fresh_bv(&format!("{}_uf_{}_{}_{}", self.prefix, sid.0, cid, r), bits_of(ty)),
                konst: None,
            })
            .collect();
        let entry = self.calls.entry(sid).or_default();
        if entry.len() >= MAX_UF_CALLS_PER_STRATUM {
            self.overflow = true;
        } else {
            entry.push((args.to_vec(), outs.clone()));
        }
        outs
    }

    fn assert_congruence_axioms<B: SmtTarget<Term = T>>(&self, b: &mut B) -> Result<(), SieveError> {
        for records in self.calls.values() {
            for i in 0..records.len() {
                for j in (i + 1)..records.len() {
                    let (args_i, outs_i) = &records[i];
                    let (args_j, outs_j) = &records[j];
                    if args_i.len() != args_j.len() || outs_i.len() != outs_j.len() {
                        continue;
                    }
                    let mut all_args_eq = SymBool::from_const(b, true);
                    for (ai, aj) in args_i.iter().zip(args_j.iter()) {
                        let eq_t = b.eq(&ai.term, &aj.term);
                        all_args_eq = all_args_eq.and(b, &SymBool::symbolic(eq_t));
                    }
                    let mut all_outs_eq = SymBool::from_const(b, true);
                    for (oi, oj) in outs_i.iter().zip(outs_j.iter()) {
                        let eq_t = b.eq(&oi.term, &oj.term);
                        all_outs_eq = all_outs_eq.and(b, &SymBool::symbolic(eq_t));
                    }
                    let not_args = all_args_eq.not(b);
                    let axiom = not_args.or(b, &all_outs_eq);
                    b.assert_formula(&axiom.term)?;
                }
            }
        }
        Ok(())
    }
}

/// Deterministic 8-bit encoding of `TrapCode` (`0` means no trap).
pub(crate) fn trap_code_byte(code: TrapCode) -> u8 {
    match code {
        TrapCode::DivByZero => 1,
        TrapCode::IntOverflow => 2,
        TrapCode::OutOfBoundsMem => 3,
        TrapCode::OutOfFuel => 4,
        TrapCode::HostContractViolation => 5,
        TrapCode::Unreachable => 6,
    }
}

/// Abstract `QF_ABV` term builder and solver backend implemented by both the
/// native `bitwuzla` API backend and the persistent SMT-LIB2 pipe backend.
pub(crate) trait SmtTarget {
    type Term: Clone;

    fn bool_const(&mut self, v: bool) -> Self::Term;
    fn bv_const(&mut self, bits: u8, v: u64) -> Self::Term;
    fn const_array_bool(&mut self, v: bool) -> Self::Term;
    fn const_array_bv8(&mut self, v: u8) -> Self::Term;

    fn fresh_bv(&mut self, name: &str, bits: u8) -> Self::Term;
    fn fresh_mem(&mut self, name: &str) -> Self::Term;

    fn not(&mut self, a: &Self::Term) -> Self::Term;
    fn and(&mut self, a: &Self::Term, b: &Self::Term) -> Self::Term;
    fn or(&mut self, a: &Self::Term, b: &Self::Term) -> Self::Term;
    fn eq(&mut self, a: &Self::Term, b: &Self::Term) -> Self::Term;
    fn ite(&mut self, cond: &Self::Term, t: &Self::Term, f: &Self::Term) -> Self::Term;

    fn array_select(&mut self, arr: &Self::Term, idx: &Self::Term) -> Self::Term;
    fn array_store(&mut self, arr: &Self::Term, idx: &Self::Term, val: &Self::Term) -> Self::Term;

    fn bv_add(&mut self, bits: u8, a: &Self::Term, b: &Self::Term) -> Self::Term;
    fn bv_sub(&mut self, bits: u8, a: &Self::Term, b: &Self::Term) -> Self::Term;
    fn bv_mul(&mut self, bits: u8, a: &Self::Term, b: &Self::Term) -> Self::Term;
    fn bv_sdiv(&mut self, bits: u8, a: &Self::Term, b: &Self::Term) -> Self::Term;
    fn bv_udiv(&mut self, bits: u8, a: &Self::Term, b: &Self::Term) -> Self::Term;
    fn bv_srem(&mut self, bits: u8, a: &Self::Term, b: &Self::Term) -> Self::Term;
    fn bv_urem(&mut self, bits: u8, a: &Self::Term, b: &Self::Term) -> Self::Term;
    fn bv_and(&mut self, bits: u8, a: &Self::Term, b: &Self::Term) -> Self::Term;
    fn bv_or(&mut self, bits: u8, a: &Self::Term, b: &Self::Term) -> Self::Term;
    fn bv_xor(&mut self, bits: u8, a: &Self::Term, b: &Self::Term) -> Self::Term;
    fn bv_shl(&mut self, bits: u8, a: &Self::Term, b: &Self::Term) -> Self::Term;
    fn bv_lshr(&mut self, bits: u8, a: &Self::Term, b: &Self::Term) -> Self::Term;
    fn bv_ashr(&mut self, bits: u8, a: &Self::Term, b: &Self::Term) -> Self::Term;
    fn bv_rotl(&mut self, bits: u8, a: &Self::Term, b: &Self::Term) -> Self::Term;
    fn bv_rotr(&mut self, bits: u8, a: &Self::Term, b: &Self::Term) -> Self::Term;

    fn bv_ult(&mut self, bits: u8, a: &Self::Term, b: &Self::Term) -> Self::Term;
    fn bv_ule(&mut self, bits: u8, a: &Self::Term, b: &Self::Term) -> Self::Term;
    fn bv_ugt(&mut self, bits: u8, a: &Self::Term, b: &Self::Term) -> Self::Term;
    fn bv_uge(&mut self, bits: u8, a: &Self::Term, b: &Self::Term) -> Self::Term;
    fn bv_slt(&mut self, bits: u8, a: &Self::Term, b: &Self::Term) -> Self::Term;
    fn bv_sle(&mut self, bits: u8, a: &Self::Term, b: &Self::Term) -> Self::Term;
    fn bv_sgt(&mut self, bits: u8, a: &Self::Term, b: &Self::Term) -> Self::Term;
    fn bv_sge(&mut self, bits: u8, a: &Self::Term, b: &Self::Term) -> Self::Term;

    fn bv_extract(&mut self, hi: u32, lo: u32, x: &Self::Term) -> Self::Term;
    fn bv_zext(&mut self, src_bits: u8, extra_bits: u8, x: &Self::Term) -> Self::Term;
    fn bv_sext(&mut self, src_bits: u8, extra_bits: u8, x: &Self::Term) -> Self::Term;
    fn bv_concat(&mut self, hi_bits: u8, lo_bits: u8, hi: &Self::Term, lo: &Self::Term) -> Self::Term;

    fn assert_formula(&mut self, cond: &Self::Term) -> Result<(), SieveError>;
    fn push(&mut self) -> Result<(), SieveError>;
    fn pop(&mut self) -> Result<(), SieveError>;
    fn check_sat(&mut self) -> Result<RawSat, SieveError>;
    fn get_bv_u64(&mut self, term: &Self::Term, bits: u8) -> Result<u64, SieveError>;
    fn get_bool(&mut self, term: &Self::Term) -> Result<bool, SieveError>;
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum RawSat {
    Unsat,
    Sat,
    Unknown(String),
}

/// Bit-vector term paired with an optional statically folded constant value.
#[derive(Clone, Debug)]
struct SymVal<T> {
    ty: ValType,
    term: T,
    konst: Option<u64>,
}

/// Boolean term paired with an optional statically folded constant boolean.
#[derive(Clone, Debug)]
struct SymBool<T> {
    term: T,
    konst: Option<bool>,
}

impl<T: Clone> SymBool<T> {
    fn from_const<B: SmtTarget<Term = T>>(b: &mut B, v: bool) -> Self {
        Self { term: b.bool_const(v), konst: Some(v) }
    }

    fn symbolic(term: T) -> Self {
        Self { term, konst: None }
    }

    fn not<B: SmtTarget<Term = T>>(&self, b: &mut B) -> Self {
        match self.konst {
            Some(v) => Self::from_const(b, !v),
            None => Self::symbolic(b.not(&self.term)),
        }
    }

    fn and<B: SmtTarget<Term = T>>(&self, b: &mut B, other: &Self) -> Self {
        match (self.konst, other.konst) {
            (Some(false), _) | (_, Some(false)) => Self::from_const(b, false),
            (Some(true), _) => other.clone(),
            (_, Some(true)) => self.clone(),
            _ => Self::symbolic(b.and(&self.term, &other.term)),
        }
    }

    fn or<B: SmtTarget<Term = T>>(&self, b: &mut B, other: &Self) -> Self {
        match (self.konst, other.konst) {
            (Some(true), _) | (_, Some(true)) => Self::from_const(b, true),
            (Some(false), _) => other.clone(),
            (_, Some(false)) => self.clone(),
            _ => Self::symbolic(b.or(&self.term, &other.term)),
        }
    }

    fn implies<B: SmtTarget<Term = T>>(&self, b: &mut B, other: &Self) -> Self {
        let not_self = self.not(b);
        not_self.or(b, other)
    }

    fn ite<B: SmtTarget<Term = T>>(&self, b: &mut B, t: &Self, f: &Self) -> Self {
        match self.konst {
            Some(true) => t.clone(),
            Some(false) => f.clone(),
            None => {
                let konst = match (t.konst, f.konst) {
                    (Some(a), Some(c)) if a == c => Some(a),
                    _ => None,
                };
                Self { term: b.ite(&self.term, &t.term, &f.term), konst }
            }
        }
    }
}

fn bits_of(ty: ValType) -> u8 {
    match ty {
        ValType::I32 => 32,
        ValType::I64 => 64,
    }
}

fn mask_for_ty(ty: ValType, v: u64) -> u64 {
    match ty {
        ValType::I32 => (v as u32) as u64,
        ValType::I64 => v,
    }
}

#[derive(Clone)]
struct MemSym<T> {
    init_array: T,
    array: T,
    init_bytes: T,
    pages: T,
    bytes: T,
    max_pages: u64,
    written: Option<T>,
    touched_by_write_or_grow: bool,
    /// Shared per-memory diagnostic read-address log for `extract_model`, capped at
    /// `MAX_TRACKED_MEM_ADDRS` so branching clones in O(1) with zero merge duplication.
    read_addrs: Rc<RefCell<Vec<(T, MemWidth)>>>,
    /// Shared per-memory write-address log populated only while executing a host
    /// contract's `sim_body` (used for sound `write_footprints` frame checking).
    write_addrs: Rc<RefCell<Vec<T>>>,
}

impl<T> MemSym<T> {
    fn record_read(&self, addr: T, width: MemWidth) {
        let mut reads = self.read_addrs.borrow_mut();
        if reads.len() < MAX_TRACKED_MEM_ADDRS {
            reads.push((addr, width));
        }
    }

    fn record_write(&self, addr: T) {
        self.write_addrs.borrow_mut().push(addr);
    }
}

#[derive(Clone)]
struct GlobalSym<T> {
    ty: ValType,
    mutable: bool,
    val: SymVal<T>,
}

#[derive(Clone)]
struct ExecState<T> {
    trapped: SymBool<T>,
    trap_code: T,
    assert_failed: SymBool<T>,
    path_active: SymBool<T>,
    path_assumptions: SymBool<T>,
    unroll_overflow: SymBool<T>,
    mems: BTreeMap<MemId, MemSym<T>>,
    globals: BTreeMap<GlobalId, GlobalSym<T>>,
    env: BTreeMap<ValId, SymVal<T>>,
    fresh_counter: u32,
    uf_table: Option<Rc<RefCell<UfTable<T>>>>,
    budget: SymBudget,
    track_writes: bool,
}

#[derive(Clone)]
struct FlowOutcome<T> {
    active: SymBool<T>,
    values: Vec<SymVal<T>>,
}

impl<T: Clone> FlowOutcome<T> {
    fn empty<B: SmtTarget<Term = T>>(b: &mut B) -> Self {
        Self { active: SymBool::from_const(b, false), values: Vec::new() }
    }
}

#[derive(Clone)]
struct FlowTargets<T> {
    normal: FlowOutcome<T>,
    returns: FlowOutcome<T>,
    breaks: BTreeMap<u32, FlowOutcome<T>>,
    continues: BTreeMap<u32, FlowOutcome<T>>,
}

impl<T: Clone> FlowTargets<T> {
    fn empty<B: SmtTarget<Term = T>>(b: &mut B) -> Self {
        Self {
            normal: FlowOutcome::empty(b),
            returns: FlowOutcome::empty(b),
            breaks: BTreeMap::new(),
            continues: BTreeMap::new(),
        }
    }
}

fn merge_sym_val<B: SmtTarget>(
    b: &mut B,
    cond: &SymBool<B::Term>,
    t: &SymVal<B::Term>,
    f: &SymVal<B::Term>,
) -> Result<SymVal<B::Term>, SieveError> {
    if t.ty != f.ty {
        return Err(SieveError::EncodingError("type mismatch during control-flow merge".into()));
    }
    Ok(match cond.konst {
        Some(true) => t.clone(),
        Some(false) => f.clone(),
        None => {
            let konst = match (t.konst, f.konst) {
                (Some(a), Some(c)) if a == c => Some(a),
                _ => None,
            };
            SymVal { ty: t.ty, term: b.ite(&cond.term, &t.term, &f.term), konst }
        }
    })
}

fn merge_outcome<B: SmtTarget>(
    b: &mut B,
    acc: &mut FlowOutcome<B::Term>,
    cond: &SymBool<B::Term>,
    vals: &[SymVal<B::Term>],
) -> Result<(), SieveError> {
    if matches!(cond.konst, Some(false)) {
        return Ok(());
    }
    if matches!(acc.active.konst, Some(false)) {
        acc.active = cond.clone();
        acc.values = vals.to_vec();
        return Ok(());
    }
    if acc.values.len() != vals.len() {
        return Err(SieveError::EncodingError("arity mismatch across merged control-flow paths".into()));
    }
    let mut merged = Vec::with_capacity(vals.len());
    for (old, new) in acc.values.iter().zip(vals) {
        merged.push(merge_sym_val(b, cond, new, old)?);
    }
    acc.values = merged;
    acc.active = acc.active.or(b, cond);
    Ok(())
}

impl<T: Clone> ExecState<T> {
    fn from_module<B: SmtTarget<Term = T>>(b: &mut B, module: &Module, prefix: &str) -> Result<Self, SieveError> {
        Self::from_module_with_mode(b, module, prefix, false)
    }

    fn from_module_with_mode<B: SmtTarget<Term = T>>(
        b: &mut B,
        module: &Module,
        prefix: &str,
        use_initial_state: bool,
    ) -> Result<Self, SieveError> {
        let mut mems = BTreeMap::new();
        for m in &module.memories {
            let limit = m.max_pages.unwrap_or(MAX_WASM_PAGES).min(MAX_WASM_PAGES);
            if m.min_pages > limit {
                return Err(SieveError::EncodingError(format!(
                    "memory {:?} has min_pages {} > max_pages {}",
                    m.id, m.min_pages, limit
                )));
            }
            let (init_array, pages, bytes) = if use_initial_state {
                let min_bytes = (m.min_pages as u64)
                    .checked_mul(WASM_PAGE_SIZE as u64)
                    .ok_or_else(|| {
                        SieveError::EncodingError(format!(
                            "memory {:?} min_pages byte size overflow",
                            m.id
                        ))
                    })?;
                let mut init_bytes_map: BTreeMap<u32, u8> = BTreeMap::new();
                for (off, data) in &m.init_data {
                    let end = (*off as u64)
                        .checked_add(data.len() as u64)
                        .ok_or_else(|| {
                            SieveError::EncodingError(format!(
                                "memory {:?} init_data offset overflow",
                                m.id
                            ))
                        })?;
                    if end > min_bytes {
                        return Err(SieveError::EncodingError(format!(
                            "memory {:?} init_data segment [{}..{}] exceeds min_pages ({} bytes)",
                            m.id, off, end, min_bytes
                        )));
                    }
                    for (i, &byte) in data.iter().enumerate() {
                        init_bytes_map.insert(*off + i as u32, byte);
                    }
                }
                let mut arr = b.const_array_bv8(0);
                for (addr, byte) in init_bytes_map {
                    if byte != 0 {
                        let idx = b.bv_const(32, addr as u64);
                        let val = b.bv_const(8, byte as u64);
                        arr = b.array_store(&arr, &idx, &val);
                    }
                }
                let pages = b.bv_const(64, m.min_pages as u64);
                let bytes = b.bv_const(64, min_bytes);
                (arr, pages, bytes)
            } else {
                let init_array = b.fresh_mem(&format!("{prefix}_mem_{}", m.id.0));
                let pages = if m.min_pages == limit {
                    b.bv_const(64, m.min_pages as u64)
                } else {
                    let p = b.fresh_bv(&format!("{prefix}_mem_{}_pages", m.id.0), 64);
                    let min_t = b.bv_const(64, m.min_pages as u64);
                    let max_t = b.bv_const(64, limit as u64);
                    let ge_min = b.bv_uge(64, &p, &min_t);
                    let le_max = b.bv_ule(64, &p, &max_t);
                    b.assert_formula(&ge_min)?;
                    b.assert_formula(&le_max)?;
                    p
                };
                let page_sz = b.bv_const(64, WASM_PAGE_SIZE as u64);
                let bytes = b.bv_mul(64, &pages, &page_sz);
                (init_array, pages, bytes)
            };
            mems.insert(
                m.id,
                MemSym {
                    init_array: init_array.clone(),
                    array: init_array,
                    init_bytes: bytes.clone(),
                    pages,
                    bytes,
                    max_pages: limit as u64,
                    written: None,
                    touched_by_write_or_grow: false,
                    read_addrs: Rc::new(RefCell::new(Vec::new())),
                    write_addrs: Rc::new(RefCell::new(Vec::new())),
                },
            );
        }

        let mut globals = BTreeMap::new();
        for g in &module.globals {
            let val = if g.mutable && !use_initial_state {
                let bits = bits_of(g.ty);
                let term = b.fresh_bv(&format!("{prefix}_g_{}", g.id.0), bits);
                SymVal { ty: g.ty, term, konst: None }
            } else {
                match g.init {
                    Val::I32(v) => SymVal {
                        ty: ValType::I32,
                        term: b.bv_const(32, (v as u32) as u64),
                        konst: Some((v as u32) as u64),
                    },
                    Val::I64(v) => SymVal {
                        ty: ValType::I64,
                        term: b.bv_const(64, v as u64),
                        konst: Some(v as u64),
                    },
                }
            };
            globals.insert(g.id, GlobalSym { ty: g.ty, mutable: g.mutable, val });
        }

        Ok(Self {
            trapped: SymBool::from_const(b, false),
            trap_code: b.bv_const(8, 0),
            assert_failed: SymBool::from_const(b, false),
            path_active: SymBool::from_const(b, true),
            path_assumptions: SymBool::from_const(b, true),
            unroll_overflow: SymBool::from_const(b, false),
            mems,
            globals,
            env: BTreeMap::new(),
            fresh_counter: 0,
            uf_table: None,
            budget: SymBudget::new(),
            track_writes: false,
        })
    }

    fn mark_budget_overflow<B: SmtTarget<Term = T>>(&mut self, b: &mut B) {
        self.unroll_overflow = self.unroll_overflow.or(b, &self.path_active);
        self.path_active = SymBool::from_const(b, false);
    }

    fn charge_call<B: SmtTarget<Term = T>>(&mut self, b: &mut B) -> bool {
        if matches!(self.path_active.konst, Some(false)) {
            return false;
        }
        if !self.budget.charge_call() {
            self.mark_budget_overflow(b);
            return false;
        }
        true
    }

    fn charge_step<B: SmtTarget<Term = T>>(&mut self, b: &mut B) -> bool {
        self.charge_steps(b, 1)
    }

    fn charge_steps<B: SmtTarget<Term = T>>(&mut self, b: &mut B, n: usize) -> bool {
        if matches!(self.path_active.konst, Some(false)) {
            return false;
        }
        if !self.budget.charge_steps(n) {
            self.mark_budget_overflow(b);
            return false;
        }
        true
    }

    fn next_fresh_name(&mut self, tag: &str) -> String {
        let id = self.fresh_counter;
        self.fresh_counter += 1;
        format!("sym_{tag}_{id}")
    }

    fn trap_if<B: SmtTarget<Term = T>>(
        &mut self,
        b: &mut B,
        cond: &SymBool<T>,
        code: TrapCode,
    ) {
        let fire = self.path_active.and(b, cond);
        if matches!(fire.konst, Some(false)) {
            return;
        }
        let code_t = b.bv_const(8, trap_code_byte(code) as u64);
        self.trap_code = match fire.konst {
            Some(true) => code_t,
            _ => b.ite(&fire.term, &code_t, &self.trap_code),
        };
        self.trapped = self.trapped.or(b, &fire);
        let not_cond = cond.not(b);
        self.path_active = self.path_active.and(b, &not_cond);
    }

    fn get_val(&self, id: ValId) -> Result<SymVal<T>, SieveError> {
        self.env
            .get(&id)
            .cloned()
            .ok_or_else(|| SieveError::EncodingError(format!("unbound ValId({})", id.0)))
    }

    fn get_u32(&self, id: ValId) -> Result<SymVal<T>, SieveError> {
        let v = self.get_val(id)?;
        if v.ty != ValType::I32 {
            return Err(SieveError::EncodingError(format!(
                "expected I32 for ValId({}), found {:?}",
                id.0, v.ty
            )));
        }
        Ok(v)
    }

    fn is_nonzero<B: SmtTarget<Term = T>>(
        &self,
        b: &mut B,
        v: &SymVal<T>,
    ) -> SymBool<T> {
        if let Some(k) = v.konst {
            return SymBool::from_const(b, k != 0);
        }
        let zero = b.bv_const(bits_of(v.ty), 0);
        let eq_z = b.eq(&v.term, &zero);
        SymBool::symbolic(b.not(&eq_z))
    }

    fn merge_from<B: SmtTarget<Term = T>>(
        &mut self,
        b: &mut B,
        cond: &SymBool<T>,
        then_state: ExecState<T>,
        else_state: ExecState<T>,
    ) -> Result<(), SieveError> {
        self.trapped = cond.ite(b, &then_state.trapped, &else_state.trapped);
        self.trap_code = match cond.konst {
            Some(true) => then_state.trap_code,
            Some(false) => else_state.trap_code,
            None => b.ite(&cond.term, &then_state.trap_code, &else_state.trap_code),
        };
        self.assert_failed = cond.ite(b, &then_state.assert_failed, &else_state.assert_failed);
        self.path_assumptions =
            cond.ite(b, &then_state.path_assumptions, &else_state.path_assumptions);
        self.unroll_overflow = cond.ite(b, &then_state.unroll_overflow, &else_state.unroll_overflow);

        for (mid, mem_acc) in &mut self.mems {
            let t = then_state.mems.get(mid).expect("memory present");
            let e = else_state.mems.get(mid).expect("memory present");
            mem_acc.touched_by_write_or_grow =
                t.touched_by_write_or_grow || e.touched_by_write_or_grow;
            mem_acc.array = match cond.konst {
                Some(true) => t.array.clone(),
                Some(false) => e.array.clone(),
                None => b.ite(&cond.term, &t.array, &e.array),
            };
            mem_acc.pages = match cond.konst {
                Some(true) => t.pages.clone(),
                Some(false) => e.pages.clone(),
                None => b.ite(&cond.term, &t.pages, &e.pages),
            };
            mem_acc.bytes = match cond.konst {
                Some(true) => t.bytes.clone(),
                Some(false) => e.bytes.clone(),
                None => b.ite(&cond.term, &t.bytes, &e.bytes),
            };
            mem_acc.written = match (&t.written, &e.written) {
                (None, None) => None,
                (Some(tw), Some(ew)) => Some(match cond.konst {
                    Some(true) => tw.clone(),
                    Some(false) => ew.clone(),
                    None => b.ite(&cond.term, tw, ew),
                }),
                (Some(tw), None) => match cond.konst {
                    Some(true) => Some(tw.clone()),
                    Some(false) => None,
                    None => {
                        let f_arr = b.const_array_bool(false);
                        Some(b.ite(&cond.term, tw, &f_arr))
                    }
                },
                (None, Some(ew)) => match cond.konst {
                    Some(true) => None,
                    Some(false) => Some(ew.clone()),
                    None => {
                        let f_arr = b.const_array_bool(false);
                        Some(b.ite(&cond.term, &f_arr, ew))
                    }
                },
            };
        }

        for (gid, g_acc) in &mut self.globals {
            let t = then_state.globals.get(gid).expect("global present");
            let e = else_state.globals.get(gid).expect("global present");
            g_acc.val = merge_sym_val(b, cond, &t.val, &e.val)?;
        }
        Ok(())
    }
}

fn eval_mem_byte<B: SmtTarget>(
    b: &mut B,
    mem: &MemSym<B::Term>,
    idx32: &B::Term,
) -> B::Term {
    let raw = b.array_select(&mem.array, idx32);
    match &mem.written {
        None => raw,
        Some(written) => {
            let idx64 = b.bv_zext(32, 32, idx32);
            let lt_init = b.bv_ult(64, &idx64, &mem.init_bytes);
            let was_written = b.array_select(written, idx32);
            let valid = b.or(&was_written, &lt_init);
            let zero8 = b.bv_const(8, 0);
            b.ite(&valid, &raw, &zero8)
        }
    }
}

/// Conditionally stores a single byte into `mem_sym` using scalar `BV8`/`Bool` ITEs
/// inside `array_store` (eliminating nested Array-level ITE chains) and logs `idx32`
/// when write tracking is enabled (`sim_body` frame checking).
fn store_mem_byte_cond<B: SmtTarget>(
    b: &mut B,
    mem_sym: &mut MemSym<B::Term>,
    idx32: &B::Term,
    byte: &B::Term,
    cond: &SymBool<B::Term>,
    track_writes: bool,
) {
    if matches!(cond.konst, Some(false)) {
        return;
    }
    mem_sym.touched_by_write_or_grow = true;
    if track_writes {
        mem_sym.record_write(idx32.clone());
    }
    match cond.konst {
        Some(true) => {
            mem_sym.array = b.array_store(&mem_sym.array, idx32, byte);
            if let Some(w) = &mem_sym.written {
                let true_t = b.bool_const(true);
                mem_sym.written = Some(b.array_store(w, idx32, &true_t));
            }
        }
        Some(false) => {}
        None => {
            let old_byte = b.array_select(&mem_sym.array, idx32);
            let new_byte = b.ite(&cond.term, byte, &old_byte);
            mem_sym.array = b.array_store(&mem_sym.array, idx32, &new_byte);
            if let Some(w) = &mem_sym.written {
                let old_w = b.array_select(w, idx32);
                let new_w = b.or(&cond.term, &old_w);
                mem_sym.written = Some(b.array_store(w, idx32, &new_w));
            }
        }
    }
}

fn check_mem_ea<B: SmtTarget>(
    b: &mut B,
    state: &mut ExecState<B::Term>,
    mem_id: MemId,
    addr: &SymVal<B::Term>,
    offset: u32,
    len_term: &B::Term,
    len_const: Option<u64>,
) -> Option<(B::Term, SymBool<B::Term>)> {
    let Some(mem) = state.mems.get(&mem_id) else {
        let t = SymBool::from_const(b, true);
        state.trap_if(b, &t, TrapCode::OutOfBoundsMem);
        return None;
    };
    let addr64 = b.bv_zext(32, 32, &addr.term);
    let off64 = b.bv_const(64, offset as u64);
    let ea64 = b.bv_add(64, &addr64, &off64);
    let end64 = b.bv_add(64, &ea64, len_term);
    let in_bounds = b.bv_ule(64, &end64, &mem.bytes);
    let oob = b.not(&in_bounds);
    let mut oob_sym = SymBool::symbolic(oob);
    if let (Some(a_c), Some(l_c)) = (addr.konst, len_const) {
        let sum = a_c + (offset as u64) + l_c;
        if sum > mem.max_pages * (WASM_PAGE_SIZE as u64) {
            oob_sym = SymBool::from_const(b, true);
        }
    }
    state.trap_if(b, &oob_sym, TrapCode::OutOfBoundsMem);
    let ea32 = b.bv_extract(31, 0, &ea64);
    Some((ea32, state.path_active.clone()))
}

fn eval_clz<B: SmtTarget>(b: &mut B, x: &B::Term, bits: u8) -> B::Term {
    let one1 = b.bv_const(1, 1);
    let mut acc = b.bv_const(bits, bits as u64);
    for bit_idx in 0..(bits as u32) {
        let bit = b.bv_extract(bit_idx, bit_idx, x);
        let is_set = b.eq(&bit, &one1);
        let lz = b.bv_const(bits, (bits as u32 - 1 - bit_idx) as u64);
        acc = b.ite(&is_set, &lz, &acc);
    }
    acc
}

fn eval_ctz<B: SmtTarget>(b: &mut B, x: &B::Term, bits: u8) -> B::Term {
    let one1 = b.bv_const(1, 1);
    let mut acc = b.bv_const(bits, bits as u64);
    for bit_idx in (0..(bits as u32)).rev() {
        let bit = b.bv_extract(bit_idx, bit_idx, x);
        let is_set = b.eq(&bit, &one1);
        let tz = b.bv_const(bits, bit_idx as u64);
        acc = b.ite(&is_set, &tz, &acc);
    }
    acc
}

fn eval_popcnt<B: SmtTarget>(b: &mut B, x: &B::Term, bits: u8) -> B::Term {
    // Balanced pairwise tree sum so adder bit-widths grow logarithmically (1 -> 2 -> ... -> 7).
    let mut layer: Vec<B::Term> = (0..(bits as u32))
        .map(|i| b.bv_extract(i, i, x))
        .collect();
    let mut cur_width: u8 = 1;
    while layer.len() > 1 {
        let next_width = cur_width + 1;
        let mut next = Vec::with_capacity(layer.len().div_ceil(2));
        for pair in layer.chunks(2) {
            if pair.len() == 2 {
                let a = b.bv_zext(cur_width, 1, &pair[0]);
                let c = b.bv_zext(cur_width, 1, &pair[1]);
                next.push(b.bv_add(next_width, &a, &c));
            } else {
                next.push(b.bv_zext(cur_width, 1, &pair[0]));
            }
        }
        layer = next;
        cur_width = next_width;
    }
    let sum = layer.into_iter().next().expect("non-empty bit vector");
    if cur_width < bits {
        b.bv_zext(cur_width, bits - cur_width, &sum)
    } else {
        sum
    }
}

fn eval_unop<B: SmtTarget>(
    b: &mut B,
    op: UnOp,
    arg: &SymVal<B::Term>,
) -> Result<SymVal<B::Term>, SieveError> {
    if arg.ty != op.input_ty() {
        return Err(SieveError::EncodingError(format!(
            "UnOp {:?} expected {:?}, got {:?}",
            op,
            op.input_ty(),
            arg.ty
        )));
    }
    let out_ty = op.output_ty();
    if let Some(k) = arg.konst {
        let v: u64 = match op {
            UnOp::I32Eqz => u64::from((k as u32) == 0),
            UnOp::I64Eqz => u64::from(k == 0),
            UnOp::I32Clz => (k as u32).leading_zeros() as u64,
            UnOp::I32Ctz => (k as u32).trailing_zeros() as u64,
            UnOp::I32Popcnt => (k as u32).count_ones() as u64,
            UnOp::I64Clz => k.leading_zeros() as u64,
            UnOp::I64Ctz => k.trailing_zeros() as u64,
            UnOp::I64Popcnt => k.count_ones() as u64,
            UnOp::I32WrapI64 => (k as u32) as u64,
            UnOp::I64ExtendI32S => ((k as i32) as i64) as u64,
            UnOp::I64ExtendI32U => (k as u32) as u64,
            UnOp::I32Extend8S => (((k as i8) as i32) as u32) as u64,
            UnOp::I32Extend16S => (((k as i16) as i32) as u32) as u64,
            UnOp::I64Extend8S => ((k as i8) as i64) as u64,
            UnOp::I64Extend16S => ((k as i16) as i64) as u64,
            UnOp::I64Extend32S => ((k as i32) as i64) as u64,
        };
        let masked = mask_for_ty(out_ty, v);
        return Ok(SymVal {
            ty: out_ty,
            term: b.bv_const(bits_of(out_ty), masked),
            konst: Some(masked),
        });
    }

    let term = match op {
        UnOp::I32Eqz => {
            let z = b.bv_const(32, 0);
            let cond = b.eq(&arg.term, &z);
            let one = b.bv_const(32, 1);
            b.ite(&cond, &one, &z)
        }
        UnOp::I64Eqz => {
            let z64 = b.bv_const(64, 0);
            let cond = b.eq(&arg.term, &z64);
            let one = b.bv_const(32, 1);
            let z32 = b.bv_const(32, 0);
            b.ite(&cond, &one, &z32)
        }
        UnOp::I32Clz => eval_clz(b, &arg.term, 32),
        UnOp::I32Ctz => eval_ctz(b, &arg.term, 32),
        UnOp::I32Popcnt => eval_popcnt(b, &arg.term, 32),
        UnOp::I64Clz => eval_clz(b, &arg.term, 64),
        UnOp::I64Ctz => eval_ctz(b, &arg.term, 64),
        UnOp::I64Popcnt => eval_popcnt(b, &arg.term, 64),
        UnOp::I32WrapI64 => b.bv_extract(31, 0, &arg.term),
        UnOp::I64ExtendI32S => b.bv_sext(32, 32, &arg.term),
        UnOp::I64ExtendI32U => b.bv_zext(32, 32, &arg.term),
        UnOp::I32Extend8S => {
            let lo = b.bv_extract(7, 0, &arg.term);
            b.bv_sext(8, 24, &lo)
        }
        UnOp::I32Extend16S => {
            let lo = b.bv_extract(15, 0, &arg.term);
            b.bv_sext(16, 16, &lo)
        }
        UnOp::I64Extend8S => {
            let lo = b.bv_extract(7, 0, &arg.term);
            b.bv_sext(8, 56, &lo)
        }
        UnOp::I64Extend16S => {
            let lo = b.bv_extract(15, 0, &arg.term);
            b.bv_sext(16, 48, &lo)
        }
        UnOp::I64Extend32S => {
            let lo = b.bv_extract(31, 0, &arg.term);
            b.bv_sext(32, 32, &lo)
        }
    };
    Ok(SymVal { ty: out_ty, term, konst: None })
}

fn eval_binop<B: SmtTarget>(
    b: &mut B,
    state: &mut ExecState<B::Term>,
    op: BinOp,
    lhs: &SymVal<B::Term>,
    rhs: &SymVal<B::Term>,
) -> Result<SymVal<B::Term>, SieveError> {
    let op_ty = op.operand_ty();
    let out_ty = op.output_ty();
    if lhs.ty != op_ty || rhs.ty != op_ty {
        return Err(SieveError::EncodingError(format!(
            "BinOp {:?} expected {:?}, got ({:?}, {:?})",
            op, op_ty, lhs.ty, rhs.ty
        )));
    }
    let bits = bits_of(op_ty);

    // Handle div/rem trap conditions identically to gnomon_kernel::eval.
    let zero = b.bv_const(bits, 0);
    let minus_one = b.bv_const(bits, if bits == 32 { 0xFFFF_FFFF } else { u64::MAX });
    let min_signed = b.bv_const(bits, if bits == 32 { 0x8000_0000 } else { 1u64 << 63 });

    match op {
        BinOp::I32DivS | BinOp::I64DivS => {
            let is_zero = match rhs.konst {
                Some(r) => SymBool::from_const(b, r == 0),
                None => SymBool::symbolic(b.eq(&rhs.term, &zero)),
            };
            state.trap_if(b, &is_zero, TrapCode::DivByZero);

            let is_min = match lhs.konst {
                Some(l) => SymBool::from_const(b, l == if bits == 32 { 0x8000_0000 } else { 1u64 << 63 }),
                None => SymBool::symbolic(b.eq(&lhs.term, &min_signed)),
            };
            let is_neg1 = match rhs.konst {
                Some(r) => SymBool::from_const(b, r == mask_for_ty(op_ty, u64::MAX)),
                None => SymBool::symbolic(b.eq(&rhs.term, &minus_one)),
            };
            let overflow = is_min.and(b, &is_neg1);
            state.trap_if(b, &overflow, TrapCode::IntOverflow);

            if let (Some(l), Some(r)) = (lhs.konst, rhs.konst) {
                let res = if bits == 32 {
                    let (a, c) = (l as i32, r as i32);
                    if c == 0 || (a == i32::MIN && c == -1) { 0 } else { (a.wrapping_div(c) as u32) as u64 }
                } else {
                    let (a, c) = (l as i64, r as i64);
                    if c == 0 || (a == i64::MIN && c == -1) { 0 } else { a.wrapping_div(c) as u64 }
                };
                return Ok(SymVal { ty: out_ty, term: b.bv_const(bits, res), konst: Some(res) });
            }
            let div = b.bv_sdiv(bits, &lhs.term, &rhs.term);
            let bad = is_zero.or(b, &overflow);
            let term = match bad.konst {
                Some(true) => zero,
                Some(false) => div,
                None => b.ite(&bad.term, &zero, &div),
            };
            return Ok(SymVal { ty: out_ty, term, konst: None });
        }
        BinOp::I32DivU | BinOp::I64DivU => {
            let is_zero = match rhs.konst {
                Some(r) => SymBool::from_const(b, r == 0),
                None => SymBool::symbolic(b.eq(&rhs.term, &zero)),
            };
            state.trap_if(b, &is_zero, TrapCode::DivByZero);

            if let (Some(l), Some(r)) = (lhs.konst, rhs.konst) {
                let res = l.checked_div(r).map_or(0, |q| mask_for_ty(op_ty, q));
                return Ok(SymVal { ty: out_ty, term: b.bv_const(bits, res), konst: Some(res) });
            }
            let div = b.bv_udiv(bits, &lhs.term, &rhs.term);
            let term = match is_zero.konst {
                Some(true) => zero,
                Some(false) => div,
                None => b.ite(&is_zero.term, &zero, &div),
            };
            return Ok(SymVal { ty: out_ty, term, konst: None });
        }
        BinOp::I32RemS | BinOp::I64RemS => {
            let is_zero = match rhs.konst {
                Some(r) => SymBool::from_const(b, r == 0),
                None => SymBool::symbolic(b.eq(&rhs.term, &zero)),
            };
            state.trap_if(b, &is_zero, TrapCode::DivByZero);

            if let (Some(l), Some(r)) = (lhs.konst, rhs.konst) {
                let res = if bits == 32 {
                    let (a, c) = (l as i32, r as i32);
                    if c == 0 || (a == i32::MIN && c == -1) { 0 } else { (a.wrapping_rem(c) as u32) as u64 }
                } else {
                    let (a, c) = (l as i64, r as i64);
                    if c == 0 || (a == i64::MIN && c == -1) { 0 } else { a.wrapping_rem(c) as u64 }
                };
                return Ok(SymVal { ty: out_ty, term: b.bv_const(bits, res), konst: Some(res) });
            }
            let is_min = match lhs.konst {
                Some(l) => SymBool::from_const(b, l == if bits == 32 { 0x8000_0000 } else { 1u64 << 63 }),
                None => SymBool::symbolic(b.eq(&lhs.term, &min_signed)),
            };
            let is_neg1 = match rhs.konst {
                Some(r) => SymBool::from_const(b, r == mask_for_ty(op_ty, u64::MAX)),
                None => SymBool::symbolic(b.eq(&rhs.term, &minus_one)),
            };
            let rem = b.bv_srem(bits, &lhs.term, &rhs.term);
            let min_neg1 = is_min.and(b, &is_neg1);
            let special = is_zero.or(b, &min_neg1);
            let term = match special.konst {
                Some(true) => zero,
                Some(false) => rem,
                None => b.ite(&special.term, &zero, &rem),
            };
            return Ok(SymVal { ty: out_ty, term, konst: None });
        }
        BinOp::I32RemU | BinOp::I64RemU => {
            let is_zero = match rhs.konst {
                Some(r) => SymBool::from_const(b, r == 0),
                None => SymBool::symbolic(b.eq(&rhs.term, &zero)),
            };
            state.trap_if(b, &is_zero, TrapCode::DivByZero);

            if let (Some(l), Some(r)) = (lhs.konst, rhs.konst) {
                let res = if r == 0 { 0 } else { mask_for_ty(op_ty, l % r) };
                return Ok(SymVal { ty: out_ty, term: b.bv_const(bits, res), konst: Some(res) });
            }
            let rem = b.bv_urem(bits, &lhs.term, &rhs.term);
            let term = match is_zero.konst {
                Some(true) => zero,
                Some(false) => rem,
                None => b.ite(&is_zero.term, &zero, &rem),
            };
            return Ok(SymVal { ty: out_ty, term, konst: None });
        }
        _ => {}
    }

    // Constant fold all non-trapping binary operations.
    if let (Some(l), Some(r)) = (lhs.konst, rhs.konst) {
        let v: u64 = if op_ty == ValType::I32 {
            let (a, c) = (l as i32, r as i32);
            let (ua, uc) = (l as u32, r as u32);
            match op {
                BinOp::I32Eq => u64::from(a == c),
                BinOp::I32Ne => u64::from(a != c),
                BinOp::I32LtS => u64::from(a < c),
                BinOp::I32LtU => u64::from(ua < uc),
                BinOp::I32GtS => u64::from(a > c),
                BinOp::I32GtU => u64::from(ua > uc),
                BinOp::I32LeS => u64::from(a <= c),
                BinOp::I32LeU => u64::from(ua <= uc),
                BinOp::I32GeS => u64::from(a >= c),
                BinOp::I32GeU => u64::from(ua >= uc),
                BinOp::I32Add => (a.wrapping_add(c) as u32) as u64,
                BinOp::I32Sub => (a.wrapping_sub(c) as u32) as u64,
                BinOp::I32Mul => (a.wrapping_mul(c) as u32) as u64,
                BinOp::I32And => (ua & uc) as u64,
                BinOp::I32Or => (ua | uc) as u64,
                BinOp::I32Xor => (ua ^ uc) as u64,
                BinOp::I32Shl => (a.wrapping_shl(uc) as u32) as u64,
                BinOp::I32ShrS => (a.wrapping_shr(uc) as u32) as u64,
                BinOp::I32ShrU => ua.wrapping_shr(uc) as u64,
                BinOp::I32Rotl => ua.rotate_left(uc & 31) as u64,
                BinOp::I32Rotr => ua.rotate_right(uc & 31) as u64,
                _ => unreachable!(),
            }
        } else {
            let (a, c) = (l as i64, r as i64);
            let (ua, uc) = (l, r);
            match op {
                BinOp::I64Eq => u64::from(a == c),
                BinOp::I64Ne => u64::from(a != c),
                BinOp::I64LtS => u64::from(a < c),
                BinOp::I64LtU => u64::from(ua < uc),
                BinOp::I64GtS => u64::from(a > c),
                BinOp::I64GtU => u64::from(ua > uc),
                BinOp::I64LeS => u64::from(a <= c),
                BinOp::I64LeU => u64::from(ua <= uc),
                BinOp::I64GeS => u64::from(a >= c),
                BinOp::I64GeU => u64::from(ua >= uc),
                BinOp::I64Add => a.wrapping_add(c) as u64,
                BinOp::I64Sub => a.wrapping_sub(c) as u64,
                BinOp::I64Mul => a.wrapping_mul(c) as u64,
                BinOp::I64And => ua & uc,
                BinOp::I64Or => ua | uc,
                BinOp::I64Xor => ua ^ uc,
                BinOp::I64Shl => a.wrapping_shl(uc as u32) as u64,
                BinOp::I64ShrS => a.wrapping_shr(uc as u32) as u64,
                BinOp::I64ShrU => ua.wrapping_shr(uc as u32),
                BinOp::I64Rotl => ua.rotate_left((uc as u32) & 63),
                BinOp::I64Rotr => ua.rotate_right((uc as u32) & 63),
                _ => unreachable!(),
            }
        };
        let masked = mask_for_ty(out_ty, v);
        return Ok(SymVal {
            ty: out_ty,
            term: b.bv_const(bits_of(out_ty), masked),
            konst: Some(masked),
        });
    }

    let one32 = b.bv_const(32, 1);
    let zero32 = b.bv_const(32, 0);
    let bool_to_i32 = |b: &mut B, cond: B::Term| b.ite(&cond, &one32, &zero32);
    let shift_mask = b.bv_const(bits, (bits - 1) as u64);

    let term = match op {
        BinOp::I32Eq | BinOp::I64Eq => {
            let c = b.eq(&lhs.term, &rhs.term);
            bool_to_i32(b, c)
        }
        BinOp::I32Ne | BinOp::I64Ne => {
            let eq = b.eq(&lhs.term, &rhs.term);
            let ne = b.not(&eq);
            bool_to_i32(b, ne)
        }
        BinOp::I32LtS | BinOp::I64LtS => {
            let c = b.bv_slt(bits, &lhs.term, &rhs.term);
            bool_to_i32(b, c)
        }
        BinOp::I32LtU | BinOp::I64LtU => {
            let c = b.bv_ult(bits, &lhs.term, &rhs.term);
            bool_to_i32(b, c)
        }
        BinOp::I32GtS | BinOp::I64GtS => {
            let c = b.bv_sgt(bits, &lhs.term, &rhs.term);
            bool_to_i32(b, c)
        }
        BinOp::I32GtU | BinOp::I64GtU => {
            let c = b.bv_ugt(bits, &lhs.term, &rhs.term);
            bool_to_i32(b, c)
        }
        BinOp::I32LeS | BinOp::I64LeS => {
            let c = b.bv_sle(bits, &lhs.term, &rhs.term);
            bool_to_i32(b, c)
        }
        BinOp::I32LeU | BinOp::I64LeU => {
            let c = b.bv_ule(bits, &lhs.term, &rhs.term);
            bool_to_i32(b, c)
        }
        BinOp::I32GeS | BinOp::I64GeS => {
            let c = b.bv_sge(bits, &lhs.term, &rhs.term);
            bool_to_i32(b, c)
        }
        BinOp::I32GeU | BinOp::I64GeU => {
            let c = b.bv_uge(bits, &lhs.term, &rhs.term);
            bool_to_i32(b, c)
        }
        BinOp::I32Add | BinOp::I64Add => b.bv_add(bits, &lhs.term, &rhs.term),
        BinOp::I32Sub | BinOp::I64Sub => b.bv_sub(bits, &lhs.term, &rhs.term),
        BinOp::I32Mul | BinOp::I64Mul => b.bv_mul(bits, &lhs.term, &rhs.term),
        BinOp::I32And | BinOp::I64And => b.bv_and(bits, &lhs.term, &rhs.term),
        BinOp::I32Or | BinOp::I64Or => b.bv_or(bits, &lhs.term, &rhs.term),
        BinOp::I32Xor | BinOp::I64Xor => b.bv_xor(bits, &lhs.term, &rhs.term),
        BinOp::I32Shl | BinOp::I64Shl => {
            let s = b.bv_and(bits, &rhs.term, &shift_mask);
            b.bv_shl(bits, &lhs.term, &s)
        }
        BinOp::I32ShrS | BinOp::I64ShrS => {
            let s = b.bv_and(bits, &rhs.term, &shift_mask);
            b.bv_ashr(bits, &lhs.term, &s)
        }
        BinOp::I32ShrU | BinOp::I64ShrU => {
            let s = b.bv_and(bits, &rhs.term, &shift_mask);
            b.bv_lshr(bits, &lhs.term, &s)
        }
        BinOp::I32Rotl | BinOp::I64Rotl => {
            let s = b.bv_and(bits, &rhs.term, &shift_mask);
            b.bv_rotl(bits, &lhs.term, &s)
        }
        BinOp::I32Rotr | BinOp::I64Rotr => {
            let s = b.bv_and(bits, &rhs.term, &shift_mask);
            b.bv_rotr(bits, &lhs.term, &s)
        }
        BinOp::I32DivS
        | BinOp::I64DivS
        | BinOp::I32DivU
        | BinOp::I64DivU
        | BinOp::I32RemS
        | BinOp::I64RemS
        | BinOp::I32RemU
        | BinOp::I64RemU => unreachable!(),
    };
    Ok(SymVal { ty: out_ty, term, konst: None })
}

fn eval_op<B: SmtTarget>(
    b: &mut B,
    state: &mut ExecState<B::Term>,
    op: &Op,
) -> Result<SymVal<B::Term>, SieveError> {
    match op {
        Op::ConstI32(v) => {
            let k = (*v as u32) as u64;
            Ok(SymVal { ty: ValType::I32, term: b.bv_const(32, k), konst: Some(k) })
        }
        Op::ConstI64(v) => {
            let k = *v as u64;
            Ok(SymVal { ty: ValType::I64, term: b.bv_const(64, k), konst: Some(k) })
        }
        Op::Copy(id) => state.get_val(*id),
        Op::Select { cond, true_val, false_val } => {
            let c = state.get_u32(*cond)?;
            let t = state.get_val(*true_val)?;
            let f = state.get_val(*false_val)?;
            let c_nz = state.is_nonzero(b, &c);
            merge_sym_val(b, &c_nz, &t, &f)
        }
        Op::GlobalGet(gid) => match state.globals.get(gid) {
            Some(g) => Ok(g.val.clone()),
            None => {
                let t = SymBool::from_const(b, true);
                state.trap_if(b, &t, TrapCode::Unreachable);
                Ok(SymVal { ty: ValType::I32, term: b.bv_const(32, 0), konst: Some(0) })
            }
        },
        Op::Un(u, a) => {
            let av = state.get_val(*a)?;
            eval_unop(b, *u, &av)
        }
        Op::Bin(bin, l, r) => {
            let lv = state.get_val(*l)?;
            let rv = state.get_val(*r)?;
            eval_binop(b, state, *bin, &lv, &rv)
        }
        Op::Load { mem, addr, offset, width, signed, result_ty } => {
            if *width == MemWidth::B8 && *result_ty == ValType::I32 {
                let t = SymBool::from_const(b, true);
                state.trap_if(b, &t, TrapCode::Unreachable);
                return Ok(SymVal { ty: ValType::I32, term: b.bv_const(32, 0), konst: Some(0) });
            }
            let addr_v = state.get_u32(*addr)?;
            let w_bytes = width.bytes();
            let w_term = b.bv_const(64, w_bytes);
            let Some((ea32, _can_read)) =
                check_mem_ea(b, state, *mem, &addr_v, *offset, &w_term, Some(w_bytes))
            else {
                return Ok(SymVal {
                    ty: *result_ty,
                    term: b.bv_const(bits_of(*result_ty), 0),
                    konst: Some(0),
                });
            };
            let mem_sym = state.mems.get_mut(mem).expect("checked");
            mem_sym.record_read(ea32.clone(), *width);
            let mut bytes = Vec::with_capacity(w_bytes as usize);
            for i in 0..w_bytes {
                let off32 = b.bv_const(32, i);
                let idx = if i == 0 { ea32.clone() } else { b.bv_add(32, &ea32, &off32) };
                bytes.push(eval_mem_byte(b, mem_sym, &idx));
            }
            // Assemble little-endian: byte[w-1] .. byte[0]
            let mut raw = bytes[0].clone();
            let mut raw_bits = 8u8;
            for byte in bytes.iter().skip(1) {
                raw = b.bv_concat(8, raw_bits, byte, &raw);
                raw_bits += 8;
            }
            let out_bits = bits_of(*result_ty);
            let extended = if raw_bits < out_bits {
                if *signed {
                    b.bv_sext(raw_bits, out_bits - raw_bits, &raw)
                } else {
                    b.bv_zext(raw_bits, out_bits - raw_bits, &raw)
                }
            } else {
                raw
            };
            Ok(SymVal { ty: *result_ty, term: extended, konst: None })
        }
        Op::MemorySize(mem) => {
            let Some(m) = state.mems.get(mem) else {
                let t = SymBool::from_const(b, true);
                state.trap_if(b, &t, TrapCode::OutOfBoundsMem);
                return Ok(SymVal { ty: ValType::I32, term: b.bv_const(32, 0), konst: Some(0) });
            };
            Ok(SymVal { ty: ValType::I32, term: b.bv_extract(31, 0, &m.pages), konst: None })
        }
        Op::MemoryGrow { mem, delta } => {
            let delta_v = state.get_u32(*delta)?;
            let Some(m) = state.mems.get_mut(mem) else {
                let t = SymBool::from_const(b, true);
                state.trap_if(b, &t, TrapCode::OutOfBoundsMem);
                return Ok(SymVal { ty: ValType::I32, term: b.bv_const(32, 0), konst: Some(0) });
            };
            let delta64 = b.bv_zext(32, 32, &delta_v.term);
            let new_pages = b.bv_add(64, &m.pages, &delta64);
            let limit = b.bv_const(64, m.max_pages);
            let fits = b.bv_ule(64, &new_pages, &limit);
            let ok = state.path_active.and(b, &SymBool::symbolic(fits));
            let old_pages32 = b.bv_extract(31, 0, &m.pages);
            let neg1 = b.bv_const(32, 0xFFFF_FFFF);
            let ret = b.ite(&ok.term, &old_pages32, &neg1);

            if !matches!(ok.konst, Some(false)) {
                m.touched_by_write_or_grow = true;
                if m.written.is_none() {
                    m.written = Some(b.const_array_bool(false));
                }
                m.pages = b.ite(&ok.term, &new_pages, &m.pages);
                let page_sz = b.bv_const(64, WASM_PAGE_SIZE as u64);
                m.bytes = b.bv_mul(64, &m.pages, &page_sz);
            }
            Ok(SymVal { ty: ValType::I32, term: ret, konst: None })
        }
    }
}

fn eval_effect<B: SmtTarget>(
    b: &mut B,
    module: &Module,
    registry: &StratumRegistry,
    state: &mut ExecState<B::Term>,
    eff: &EffectOp,
    depth: u32,
) -> Result<(), SieveError> {
    let _ = (module, registry, depth);
    match eff {
        EffectOp::Nop => Ok(()),
        EffectOp::Trap(code) => {
            let t = SymBool::from_const(b, true);
            state.trap_if(b, &t, *code);
            Ok(())
        }
        EffectOp::GlobalSet { id, val } => {
            let v = state.get_val(*val)?;
            let Some(g) = state.globals.get_mut(id) else {
                let t = SymBool::from_const(b, true);
                state.trap_if(b, &t, TrapCode::Unreachable);
                return Ok(());
            };
            if !g.mutable || v.ty != g.ty {
                let t = SymBool::from_const(b, true);
                state.trap_if(b, &t, TrapCode::Unreachable);
                return Ok(());
            }
            let active = state.path_active.clone();
            g.val = merge_sym_val(b, &active, &v, &g.val)?;
            Ok(())
        }
        EffectOp::Store { mem, addr, offset, width, val } => {
            let addr_v = state.get_u32(*addr)?;
            let val_v = state.get_val(*val)?;
            if *width == MemWidth::B8 && val_v.ty == ValType::I32 {
                let t = SymBool::from_const(b, true);
                state.trap_if(b, &t, TrapCode::Unreachable);
                return Ok(());
            }
            let w_bytes = width.bytes();
            let w_term = b.bv_const(64, w_bytes);
            let Some((ea32, can_write)) =
                check_mem_ea(b, state, *mem, &addr_v, *offset, &w_term, Some(w_bytes))
            else {
                return Ok(());
            };
            if matches!(can_write.konst, Some(false)) {
                return Ok(());
            }
            let track_writes = state.track_writes;
            let mem_sym = state.mems.get_mut(mem).expect("checked");
            for i in 0..w_bytes {
                let lo = (i as u32) * 8;
                let byte = b.bv_extract(lo + 7, lo, &val_v.term);
                let off32 = b.bv_const(32, i);
                let idx = if i == 0 { ea32.clone() } else { b.bv_add(32, &ea32, &off32) };
                store_mem_byte_cond(b, mem_sym, &idx, &byte, &can_write, track_writes);
            }
            Ok(())
        }
        EffectOp::MemoryFill { mem, dst, val, len } => {
            let dst_v = state.get_u32(*dst)?;
            let val_v = state.get_u32(*val)?;
            let len_v = state.get_u32(*len)?;
            let len64 = b.bv_zext(32, 32, &len_v.term);
            let Some((ea32, can_write)) =
                check_mem_ea(b, state, *mem, &dst_v, 0, &len64, len_v.konst)
            else {
                return Ok(());
            };
            if matches!(can_write.konst, Some(false)) {
                return Ok(());
            }
            let byte = b.bv_extract(7, 0, &val_v.term);
            if let Some(n) = len_v.konst {
                let n_usize = n as usize;
                if n_usize > MAX_CONST_MEM_OP_BYTES {
                    state.unroll_overflow = state.unroll_overflow.or(b, &can_write);
                    return Ok(());
                }
                if n_usize == 0 {
                    return Ok(());
                }
                if !state.charge_steps(b, n_usize) {
                    return Ok(());
                }
                let track_writes = state.track_writes;
                let mem_sym = state.mems.get_mut(mem).expect("checked");
                for i in 0..n_usize {
                    let off32 = b.bv_const(32, i as u64);
                    let idx = if i == 0 { ea32.clone() } else { b.bv_add(32, &ea32, &off32) };
                    store_mem_byte_cond(b, mem_sym, &idx, &byte, &can_write, track_writes);
                }
            } else {
                if !state.charge_steps(b, MAX_SYM_MEM_OP_BYTES) {
                    return Ok(());
                }
                let max_t = b.bv_const(32, MAX_SYM_MEM_OP_BYTES as u64);
                let too_big = b.bv_ugt(32, &len_v.term, &max_t);
                let over = can_write.and(b, &SymBool::symbolic(too_big));
                state.unroll_overflow = state.unroll_overflow.or(b, &over);

                let track_writes = state.track_writes;
                let mem_sym = state.mems.get_mut(mem).expect("checked");
                for i in 0..MAX_SYM_MEM_OP_BYTES {
                    let i32_t = b.bv_const(32, i as u64);
                    let in_len = SymBool::symbolic(b.bv_ult(32, &i32_t, &len_v.term));
                    let do_i = can_write.and(b, &in_len);
                    let idx = if i == 0 { ea32.clone() } else { b.bv_add(32, &ea32, &i32_t) };
                    store_mem_byte_cond(b, mem_sym, &idx, &byte, &do_i, track_writes);
                }
            }
            Ok(())
        }
        EffectOp::MemoryCopy { dst_mem, src_mem, dst, src, len } => {
            let dst_v = state.get_u32(*dst)?;
            let src_v = state.get_u32(*src)?;
            let len_v = state.get_u32(*len)?;
            let len64 = b.bv_zext(32, 32, &len_v.term);
            let Some((dst_ea32, _)) =
                check_mem_ea(b, state, *dst_mem, &dst_v, 0, &len64, len_v.konst)
            else {
                return Ok(());
            };
            let Some((src_ea32, can_write)) =
                check_mem_ea(b, state, *src_mem, &src_v, 0, &len64, len_v.konst)
            else {
                return Ok(());
            };
            if matches!(can_write.konst, Some(false)) {
                return Ok(());
            }
            // Snapshot source memory BEFORE writing so intra-memory overlapping copies match `copy_within`.
            let src_snapshot = state.mems.get(src_mem).expect("checked").clone();
            if let Some(n) = len_v.konst {
                let n_usize = n as usize;
                if n_usize > MAX_CONST_MEM_OP_BYTES {
                    state.unroll_overflow = state.unroll_overflow.or(b, &can_write);
                    return Ok(());
                }
                if n_usize == 0 {
                    return Ok(());
                }
                if !state.charge_steps(b, n_usize) {
                    return Ok(());
                }
                let mut bytes = Vec::with_capacity(n_usize);
                for i in 0..n_usize {
                    let off32 = b.bv_const(32, i as u64);
                    let s_idx = if i == 0 { src_ea32.clone() } else { b.bv_add(32, &src_ea32, &off32) };
                    bytes.push(eval_mem_byte(b, &src_snapshot, &s_idx));
                }
                let track_writes = state.track_writes;
                let dst_sym = state.mems.get_mut(dst_mem).expect("checked");
                for (i, byte) in bytes.iter().enumerate() {
                    let off32 = b.bv_const(32, i as u64);
                    let d_idx = if i == 0 { dst_ea32.clone() } else { b.bv_add(32, &dst_ea32, &off32) };
                    store_mem_byte_cond(b, dst_sym, &d_idx, byte, &can_write, track_writes);
                }
            } else {
                if !state.charge_steps(b, MAX_SYM_MEM_OP_BYTES) {
                    return Ok(());
                }
                let max_t = b.bv_const(32, MAX_SYM_MEM_OP_BYTES as u64);
                let too_big = b.bv_ugt(32, &len_v.term, &max_t);
                let over = can_write.and(b, &SymBool::symbolic(too_big));
                state.unroll_overflow = state.unroll_overflow.or(b, &over);

                let mut src_bytes = Vec::with_capacity(MAX_SYM_MEM_OP_BYTES);
                for i in 0..MAX_SYM_MEM_OP_BYTES {
                    let i32_t = b.bv_const(32, i as u64);
                    let s_idx = if i == 0 { src_ea32.clone() } else { b.bv_add(32, &src_ea32, &i32_t) };
                    src_bytes.push(eval_mem_byte(b, &src_snapshot, &s_idx));
                }
                let track_writes = state.track_writes;
                let dst_sym = state.mems.get_mut(dst_mem).expect("checked");
                for (i, byte) in src_bytes.iter().enumerate() {
                    let i32_t = b.bv_const(32, i as u64);
                    let in_len = SymBool::symbolic(b.bv_ult(32, &i32_t, &len_v.term));
                    let do_i = can_write.and(b, &in_len);
                    let d_idx = if i == 0 { dst_ea32.clone() } else { b.bv_add(32, &dst_ea32, &i32_t) };
                    store_mem_byte_cond(b, dst_sym, &d_idx, byte, &do_i, track_writes);
                }
            }
            Ok(())
        }
    }
}

fn bind_params<B: SmtTarget>(
    b: &mut B,
    state: &mut ExecState<B::Term>,
    params: &[(ValId, ValType)],
    vals: &[SymVal<B::Term>],
) -> Result<bool, SieveError> {
    if params.len() != vals.len() {
        let t = SymBool::from_const(b, true);
        state.trap_if(b, &t, TrapCode::Unreachable);
        return Ok(false);
    }
    for (&(id, ty), v) in params.iter().zip(vals) {
        if v.ty != ty {
            let t = SymBool::from_const(b, true);
            state.trap_if(b, &t, TrapCode::Unreachable);
            return Ok(false);
        }
        state.env.insert(id, v.clone());
    }
    Ok(true)
}

fn check_result_types(vals: &[SymVal<impl Clone>], tys: &[ValType]) -> bool {
    vals.len() == tys.len() && vals.iter().zip(tys).all(|(v, &t)| v.ty == t)
}

#[allow(clippy::too_many_arguments)]
fn eval_body<B: SmtTarget>(
    b: &mut B,
    module: &Module,
    registry: &StratumRegistry,
    state: &mut ExecState<B::Term>,
    params: &[(ValId, ValType)],
    results: &[ValType],
    body: &Region,
    args: &[SymVal<B::Term>],
    depth: u32,
) -> Result<Vec<SymVal<B::Term>>, SieveError> {
    if !state.charge_call(b) {
        return Ok(results
            .iter()
            .map(|&ty| SymVal { ty, term: b.bv_const(bits_of(ty), 0), konst: Some(0) })
            .collect());
    }
    if depth >= MAX_CALL_DEPTH {
        let t = SymBool::from_const(b, true);
        state.trap_if(b, &t, TrapCode::OutOfFuel);
        return Ok(results
            .iter()
            .map(|&ty| SymVal { ty, term: b.bv_const(bits_of(ty), 0), konst: Some(0) })
            .collect());
    }
    let saved_env = std::mem::take(&mut state.env);
    if !bind_params(b, state, params, args)? {
        state.env = saved_env;
        return Ok(results
            .iter()
            .map(|&ty| SymVal { ty, term: b.bv_const(bits_of(ty), 0), konst: Some(0) })
            .collect());
    }
    let flow = eval_region_flow(b, module, registry, state, body.as_ref(), depth)?;
    state.env = saved_env;

    // Any escaping Break/Continue from a function/stratum traps Unreachable.
    for out in flow.breaks.values().chain(flow.continues.values()) {
        state.trap_if(b, &out.active, TrapCode::Unreachable);
    }
    let mut combined = FlowOutcome::empty(b);
    merge_outcome(b, &mut combined, &flow.normal.active, &flow.normal.values)?;
    merge_outcome(b, &mut combined, &flow.returns.active, &flow.returns.values)?;
    if !matches!(combined.active.konst, Some(false)) && !check_result_types(&combined.values, results) {
        state.trap_if(b, &combined.active, TrapCode::Unreachable);
        return Ok(results
            .iter()
            .map(|&ty| SymVal { ty, term: b.bv_const(bits_of(ty), 0), konst: Some(0) })
            .collect());
    }
    state.path_active = combined.active;
    if combined.values.is_empty() && !results.is_empty() {
        Ok(results
            .iter()
            .map(|&ty| SymVal { ty, term: b.bv_const(bits_of(ty), 0), konst: Some(0) })
            .collect())
    } else {
        Ok(combined.values)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum GnomonIntrinsic {
    Assume,
    Assert,
}

fn classify_gnomon_intrinsic(hc: &HostContract) -> Option<GnomonIntrinsic> {
    if hc.params.len() != 1 || hc.params[0].1 != ValType::I32 || !hc.results.is_empty() {
        return None;
    }
    let m = hc.module_name.as_str();
    let f = hc.field_name.as_str();
    if (m == "gnomon" && matches!(f, "assume" | "gnomon_assume"))
        || matches!(f, "gnomon::assume" | "gnomon_assume" | "assume")
    {
        return Some(GnomonIntrinsic::Assume);
    }
    if (m == "gnomon" && matches!(f, "assert" | "gnomon_assert"))
        || matches!(f, "gnomon::assert" | "gnomon_assert" | "assert")
    {
        return Some(GnomonIntrinsic::Assert);
    }
    None
}

fn eval_host_call<B: SmtTarget>(
    b: &mut B,
    module: &Module,
    registry: &StratumRegistry,
    state: &mut ExecState<B::Term>,
    hc: &HostContract,
    args: &[SymVal<B::Term>],
    depth: u32,
) -> Result<Vec<SymVal<B::Term>>, SieveError> {
    if let Some(intrinsic) = classify_gnomon_intrinsic(hc) {
        if args.len() != 1 || args[0].ty != ValType::I32 {
            let t = SymBool::from_const(b, true);
            state.trap_if(b, &t, TrapCode::HostContractViolation);
            return Ok(Vec::new());
        }
        let arg_nz = state.is_nonzero(b, &args[0]);
        let not_trapped = state.trapped.not(b);
        match intrinsic {
            GnomonIntrinsic::Assume => {
                // Soundness: guard with `path_active && !trapped && !unroll_overflow` so an
                // `assume(false)` after an earlier trap or unroll overflow can never mask it.
                let not_overflow = state.unroll_overflow.not(b);
                let active_clean = state
                    .path_active
                    .and(b, &not_trapped)
                    .and(b, &not_overflow);
                let assume_cond = active_clean.implies(b, &arg_nz);
                state.path_assumptions = state.path_assumptions.and(b, &assume_cond);
            }
            GnomonIntrinsic::Assert => {
                let is_zero = arg_nz.not(b);
                let fire = state.path_active.and(b, &not_trapped).and(b, &is_zero);
                state.assert_failed = state.assert_failed.or(b, &fire);
                state.trap_if(b, &is_zero, TrapCode::HostContractViolation);
            }
        }
        return Ok(Vec::new());
    }

    if !state.charge_call(b) {
        return Ok(hc
            .results
            .iter()
            .map(|&(_, ty)| SymVal { ty, term: b.bv_const(bits_of(ty), 0), konst: Some(0) })
            .collect());
    }

    if !validate_read_only_with_registry(&hc.precondition, registry)
        || !validate_read_only_with_registry(&hc.postcondition, registry)
    {
        let t = SymBool::from_const(b, true);
        state.trap_if(b, &t, TrapCode::HostContractViolation);
        return Ok(hc
            .results
            .iter()
            .map(|&(_, ty)| SymVal { ty, term: b.bv_const(bits_of(ty), 0), konst: Some(0) })
            .collect());
    }
    let saved_env = std::mem::take(&mut state.env);
    if args.len() != hc.params.len()
        || args.iter().zip(&hc.params).any(|(a, &(_, pt))| a.ty != pt)
    {
        state.env = saved_env;
        let t = SymBool::from_const(b, true);
        state.trap_if(b, &t, TrapCode::HostContractViolation);
        return Ok(hc
            .results
            .iter()
            .map(|&(_, ty)| SymVal { ty, term: b.bv_const(bits_of(ty), 0), konst: Some(0) })
            .collect());
    }
    for (&(id, _), a) in hc.params.iter().zip(args) {
        state.env.insert(id, a.clone());
    }

    // Check precondition on read-only snapshot.
    let mut pre_state = state.clone();
    let pre_flow =
        eval_region_flow(b, module, registry, &mut pre_state, hc.precondition.as_ref(), depth + 1)?;
    state.unroll_overflow = state.unroll_overflow.or(b, &pre_state.unroll_overflow);
    let pre_not_over = pre_state.unroll_overflow.not(b);
    let pre_violated = if pre_state.trapped.konst == Some(true)
        || matches!(pre_flow.normal.active.konst, Some(false))
    {
        SymBool::from_const(b, true)
    } else {
        let pre_nz = match pre_flow.normal.values.first() {
            Some(v) if v.ty == ValType::I32 => state.is_nonzero(b, v),
            _ => SymBool::from_const(b, false),
        };
        let ok_norm = pre_flow.normal.active.and(b, &pre_nz);
        let not_ok = ok_norm.not(b);
        pre_state.trapped.or(b, &not_ok)
    };
    let pre_violated_clean = pre_violated.and(b, &pre_not_over);
    state.trap_if(b, &pre_violated_clean, TrapCode::HostContractViolation);
    state.path_active = state.path_active.and(b, &pre_not_over);

    // Check footprint bounds and record write-footprint intervals for frame checking.
    let eval_slice_bound = |b: &mut B, sb: SliceBound| -> Option<SymVal<B::Term>> {
        match sb {
            SliceBound::Const(c) => Some(SymVal {
                ty: ValType::I32,
                term: b.bv_const(32, c as u64),
                konst: Some(c as u64),
            }),
            SliceBound::Arg(i) => args.get(i as usize).filter(|a| a.ty == ValType::I32).cloned(),
        }
    };
    let mut write_fp_bounds: Vec<(MemId, B::Term, B::Term)> = Vec::new();
    for (is_write, &(mid, range)) in hc
        .read_footprints
        .iter()
        .map(|fp| (false, fp))
        .chain(hc.write_footprints.iter().map(|fp| (true, fp)))
    {
        let (Some(base_v), Some(len_v)) =
            (eval_slice_bound(b, range.base), eval_slice_bound(b, range.len))
        else {
            let t = SymBool::from_const(b, true);
            state.trap_if(b, &t, TrapCode::HostContractViolation);
            continue;
        };
        let len64 = b.bv_zext(32, 32, &len_v.term);
        let Some(m) = state.mems.get(&mid) else {
            let t = SymBool::from_const(b, true);
            state.trap_if(b, &t, TrapCode::OutOfBoundsMem);
            continue;
        };
        let base64 = b.bv_zext(32, 32, &base_v.term);
        let end64 = b.bv_add(64, &base64, &len64);
        let in_b = b.bv_ule(64, &end64, &m.bytes);
        let oob = SymBool::symbolic(b.not(&in_b));
        state.trap_if(b, &oob, TrapCode::OutOfBoundsMem);
        if is_write {
            write_fp_bounds.push((mid, base64, end64));
        }
    }

    let res_vals = if let Some(sim_body) = &hc.sim_body {
        let before_mems = state.mems.clone();
        let write_starts: BTreeMap<MemId, usize> =
            before_mems.iter().map(|(&mid, m)| (mid, m.write_addrs.borrow().len())).collect();
        let prev_track_writes = state.track_writes;
        state.track_writes = true;
        let flow_res = eval_region_flow(b, module, registry, state, sim_body.as_ref(), depth + 1);
        state.track_writes = prev_track_writes;
        let flow = flow_res?;
        for out in flow.breaks.values().chain(flow.continues.values()) {
            state.trap_if(b, &out.active, TrapCode::HostContractViolation);
        }
        let mut combined = FlowOutcome::empty(b);
        merge_outcome(b, &mut combined, &flow.normal.active, &flow.normal.values)?;
        merge_outcome(b, &mut combined, &flow.returns.active, &flow.returns.values)?;
        state.path_active = combined.active;

        // Enforce write_footprints + memory-size frame integrity (matching gnomon-kernel/src/eval.rs).
        if !matches!(state.path_active.konst, Some(false)) {
            let mut frame_bad = SymBool::from_const(b, false);
            for (mid, before_m) in &before_mems {
                let after_m = state.mems.get(mid).expect("memory present");
                let sz_eq = b.eq(&after_m.bytes, &before_m.bytes);
                let sz_changed = SymBool::symbolic(b.not(&sz_eq));
                frame_bad = frame_bad.or(b, &sz_changed);

                let start = write_starts.get(mid).copied().unwrap_or(0);
                let writes = after_m.write_addrs.borrow();
                for idx32 in &writes[start..] {
                    let idx64 = b.bv_zext(32, 32, idx32);
                    let in_mem = b.bv_ult(64, &idx64, &after_m.bytes);
                    let before_b = eval_mem_byte(b, before_m, idx32);
                    let after_b = eval_mem_byte(b, after_m, idx32);
                    let eq_b = b.eq(&before_b, &after_b);
                    let neq_b = b.not(&eq_b);
                    let changed = b.and(&in_mem, &neq_b);

                    let mut in_fp = b.bool_const(false);
                    for (fp_mid, base64, end64) in &write_fp_bounds {
                        if fp_mid == mid {
                            let ge_base = b.bv_uge(64, &idx64, base64);
                            let lt_end = b.bv_ult(64, &idx64, end64);
                            let in_range = b.and(&ge_base, &lt_end);
                            in_fp = b.or(&in_fp, &in_range);
                        }
                    }
                    let outside_fp = b.not(&in_fp);
                    let bad_byte = SymBool::symbolic(b.and(&changed, &outside_fp));
                    frame_bad = frame_bad.or(b, &bad_byte);
                }
            }
            state.trap_if(b, &frame_bad, TrapCode::HostContractViolation);
        }
        if !prev_track_writes {
            for mem in state.mems.values() {
                mem.write_addrs.borrow_mut().clear();
            }
        }

        let expected_tys: Vec<ValType> = hc.results.iter().map(|&(_, t)| t).collect();
        if !matches!(state.path_active.konst, Some(false)) && !check_result_types(&combined.values, &expected_tys) {
            let t = SymBool::from_const(b, true);
            state.trap_if(b, &t, TrapCode::HostContractViolation);
            expected_tys
                .into_iter()
                .map(|ty| SymVal { ty, term: b.bv_const(bits_of(ty), 0), konst: Some(0) })
                .collect()
        } else if combined.values.is_empty() && !expected_tys.is_empty() {
            expected_tys
                .into_iter()
                .map(|ty| SymVal { ty, term: b.bv_const(bits_of(ty), 0), konst: Some(0) })
                .collect()
        } else {
            combined.values
        }
    } else {
        if !hc.write_footprints.is_empty() {
            state.env = saved_env;
            return Err(SieveError::EncodingError(format!(
                "host contract '{}' has write_footprints without sim_body",
                hc.field_name
            )));
        }
        hc.results
            .iter()
            .map(|&(_, ty)| {
                let name = state.next_fresh_name("host_res");
                SymVal { ty, term: b.fresh_bv(&name, bits_of(ty)), konst: None }
            })
            .collect()
    };

    // Bind results and validate/assume postcondition.
    for (&(id, _), v) in hc.results.iter().zip(&res_vals) {
        state.env.insert(id, v.clone());
    }
    let mut post_state = state.clone();
    let post_flow = eval_region_flow(
        b,
        module,
        registry,
        &mut post_state,
        hc.postcondition.as_ref(),
        depth + 1,
    )?;
    state.unroll_overflow = state.unroll_overflow.or(b, &post_state.unroll_overflow);
    let post_not_over = post_state.unroll_overflow.not(b);
    let post_nz = match post_flow.normal.values.first() {
        Some(v) if v.ty == ValType::I32 => state.is_nonzero(b, v),
        _ => SymBool::from_const(b, false),
    };
    let post_active_nz = post_flow.normal.active.and(b, &post_nz);
    let post_not_trapped = post_state.trapped.not(b);
    let post_ok = post_not_trapped.and(b, &post_active_nz);
    if hc.sim_body.is_some() {
        let active = state.path_active.clone();
        let not_post_ok = post_ok.not(b);
        let bad = active.and(b, &not_post_ok).and(b, &post_not_over);
        state.trap_if(b, &bad, TrapCode::HostContractViolation);
        state.path_active = state.path_active.and(b, &post_not_over);
    } else {
        let not_active = state.path_active.not(b);
        let cond = not_active.or(b, &post_ok).or(b, &post_state.unroll_overflow);
        b.assert_formula(&cond.term)?;
        state.path_active = state.path_active.and(b, &post_not_over);
    }

    state.env = saved_env;
    Ok(res_vals)
}

fn eval_block_stmts_raw<B: SmtTarget>(
    b: &mut B,
    module: &Module,
    registry: &StratumRegistry,
    state: &mut ExecState<B::Term>,
    r: RegionRef<'_>,
    stmts: Span,
    depth: u32,
) -> Result<FlowTargets<B::Term>, SieveError> {
    let saved_env = state.env.clone();
    let mut flows = FlowTargets::empty(b);

    for stmt in r.stmts(stmts) {
        if matches!(state.path_active.konst, Some(false)) {
            break;
        }
        if !state.charge_step(b) {
            break;
        }
        match stmt {
            Stmt::Let { dst, ty, op } => {
                let val = eval_op(b, state, &op)?;
                if val.ty != ty {
                    let t = SymBool::from_const(b, true);
                    state.trap_if(b, &t, TrapCode::Unreachable);
                } else {
                    state.env.insert(dst, val);
                }
            }
            Stmt::Effect(eff) => {
                eval_effect(b, module, registry, state, &eff, depth)?;
            }
            Stmt::Region { results, region } => {
                let Some(sub_r) = r.child(region) else {
                    let t = SymBool::from_const(b, true);
                    state.trap_if(b, &t, TrapCode::Unreachable);
                    break;
                };
                let res_vars = r.region.vars_vec(results);
                let inner = eval_region_flow(b, module, registry, state, sub_r, depth)?;
                merge_outcome(b, &mut flows.returns, &inner.returns.active, &inner.returns.values)?;
                for (d, out) in inner.breaks {
                    let entry = flows.breaks.entry(d).or_insert_with(|| FlowOutcome::empty(b));
                    merge_outcome(b, entry, &out.active, &out.values)?;
                }
                for (d, out) in inner.continues {
                    let entry = flows.continues.entry(d).or_insert_with(|| FlowOutcome::empty(b));
                    merge_outcome(b, entry, &out.active, &out.values)?;
                }
                state.path_active = inner.normal.active.clone();
                if !matches!(state.path_active.konst, Some(false)) {
                    bind_params(b, state, &res_vars, &inner.normal.values)?;
                } else {
                    for &(id, ty) in &res_vars {
                        state.env.insert(id, SymVal { ty, term: b.bv_const(bits_of(ty), 0), konst: Some(0) });
                    }
                }
            }
            Stmt::Call { results, target, args } => {
                let arg_vals: Vec<_> = r
                    .vals(args)
                    .map(|id| state.get_val(id))
                    .collect::<Result<_, _>>()?;
                let res_vars = r.region.vars_vec(results);
                let res_vals = match target {
                    CallTarget::Func(fid) => {
                        let Some(f) = module.func(fid) else {
                            let t = SymBool::from_const(b, true);
                            state.trap_if(b, &t, TrapCode::Unreachable);
                            continue;
                        };
                        eval_body(b, module, registry, state, &f.params, &f.results, &f.body, &arg_vals, depth + 1)?
                    }
                    CallTarget::Stratum(sid) => {
                        let Some(op) = registry.get_op(sid) else {
                            let t = SymBool::from_const(b, true);
                            state.trap_if(b, &t, TrapCode::Unreachable);
                            continue;
                        };
                        let use_uf = state.uf_table.as_ref().is_some_and(|rc| {
                            rc.borrow().abstract_strata.contains(&sid)
                        }) && arg_vals.len() == op.params.len()
                            && arg_vals.iter().zip(&op.params).all(|(a, &(_, t))| a.ty == t);
                        if use_uf {
                            let rc = state.uf_table.as_ref().unwrap().clone();
                            rc.borrow_mut().apply(b, sid, &arg_vals, &op.results)
                        } else {
                            eval_body(b, module, registry, state, &op.params, &op.results, &op.body, &arg_vals, depth + 1)?
                        }
                    }
                    CallTarget::Host(hid) => {
                        let Some(hc) = module.host_contract(hid) else {
                            let t = SymBool::from_const(b, true);
                            state.trap_if(b, &t, TrapCode::HostContractViolation);
                            continue;
                        };
                        eval_host_call(b, module, registry, state, hc, &arg_vals, depth)?
                    }
                };
                if !matches!(state.path_active.konst, Some(false)) {
                    bind_params(b, state, &res_vars, &res_vals)?;
                }
            }
            Stmt::Yield(ids) => {
                let vals: Vec<_> = r.vals(ids).map(|id| state.get_val(id)).collect::<Result<_, _>>()?;
                let take = state.path_active.clone();
                merge_outcome(b, &mut flows.normal, &take, &vals)?;
                state.path_active = SymBool::from_const(b, false);
            }
            Stmt::Break { depth: br_d, cond, values } => {
                let (take, remaining) = match cond {
                    None => (state.path_active.clone(), SymBool::from_const(b, false)),
                    Some(cid) => {
                        let cv = state.get_u32(cid)?;
                        let cond_sym = state.is_nonzero(b, &cv);
                        let take = state.path_active.and(b, &cond_sym);
                        let not_cond = cond_sym.not(b);
                        let rem = state.path_active.and(b, &not_cond);
                        (take, rem)
                    }
                };
                if !matches!(take.konst, Some(false)) {
                    let vals: Vec<_> = r.vals(values).map(|id| state.get_val(id)).collect::<Result<_, _>>()?;
                    let entry = flows.breaks.entry(br_d).or_insert_with(|| FlowOutcome::empty(b));
                    merge_outcome(b, entry, &take, &vals)?;
                }
                state.path_active = remaining;
            }
            Stmt::Continue { depth: ct_d, cond, values } => {
                let (take, remaining) = match cond {
                    None => (state.path_active.clone(), SymBool::from_const(b, false)),
                    Some(cid) => {
                        let cv = state.get_u32(cid)?;
                        let cond_sym = state.is_nonzero(b, &cv);
                        let take = state.path_active.and(b, &cond_sym);
                        let not_cond = cond_sym.not(b);
                        let rem = state.path_active.and(b, &not_cond);
                        (take, rem)
                    }
                };
                if !matches!(take.konst, Some(false)) {
                    let vals: Vec<_> = r.vals(values).map(|id| state.get_val(id)).collect::<Result<_, _>>()?;
                    let entry = flows.continues.entry(ct_d).or_insert_with(|| FlowOutcome::empty(b));
                    merge_outcome(b, entry, &take, &vals)?;
                }
                state.path_active = remaining;
            }
            Stmt::Return(ids) => {
                let vals: Vec<_> = r.vals(ids).map(|id| state.get_val(id)).collect::<Result<_, _>>()?;
                let take = state.path_active.clone();
                merge_outcome(b, &mut flows.returns, &take, &vals)?;
                state.path_active = SymBool::from_const(b, false);
            }
        }
    }

    if !matches!(state.path_active.konst, Some(false)) {
        let take = state.path_active.clone();
        merge_outcome(b, &mut flows.normal, &take, &[])?;
        state.path_active = SymBool::from_const(b, false);
    }

    state.env = saved_env;
    Ok(flows)
}

fn eval_region_flow<B: SmtTarget>(
    b: &mut B,
    module: &Module,
    registry: &StratumRegistry,
    state: &mut ExecState<B::Term>,
    region: RegionRef<'_>,
    depth: u32,
) -> Result<FlowTargets<B::Term>, SieveError> {
    match region.node {
        RegionNode::Block(stmts) => {
            let raw = eval_block_stmts_raw(b, module, registry, state, region, stmts, depth)?;
            let mut out = FlowTargets::empty(b);
            let br0_non_empty = raw.breaks.get(&0).is_some_and(|br| !br.values.is_empty());
            if br0_non_empty && raw.normal.values.is_empty() {
                state.trap_if(b, &raw.normal.active, TrapCode::Unreachable);
            } else {
                out.normal = raw.normal;
            }
            out.returns = raw.returns;
            for (d, br) in raw.breaks {
                if d == 0 {
                    merge_outcome(b, &mut out.normal, &br.active, &br.values)?;
                } else {
                    out.breaks.insert(d - 1, br);
                }
            }
            for (d, ct) in raw.continues {
                if d == 0 {
                    state.trap_if(b, &ct.active, TrapCode::Unreachable);
                } else {
                    out.continues.insert(d - 1, ct);
                }
            }
            Ok(out)
        }
        RegionNode::IfElse { cond, then_region, else_region, results } => {
            if !state.charge_step(b) {
                return Ok(FlowTargets::empty(b));
            }
            let (Some(then_r), Some(else_r)) = (region.child(then_region), region.child(else_region)) else {
                let t = SymBool::from_const(b, true);
                state.trap_if(b, &t, TrapCode::Unreachable);
                return Ok(FlowTargets::empty(b));
            };
            let res_tys = region.region.tys_vec(results);
            let c_val = state.get_u32(cond)?;
            let c_nz = state.is_nonzero(b, &c_val);
            let entry_active = state.path_active.clone();

            let mut then_state = state.clone();
            then_state.path_active = entry_active.and(b, &c_nz);
            let then_flow = if matches!(then_state.path_active.konst, Some(false)) {
                FlowTargets::empty(b)
            } else {
                let mut tf = eval_region_flow(b, module, registry, &mut then_state, then_r, depth)?;
                if !matches!(tf.normal.active.konst, Some(false))
                    && !check_result_types(&tf.normal.values, &res_tys)
                {
                    then_state.trap_if(b, &tf.normal.active, TrapCode::Unreachable);
                    tf.normal = FlowOutcome::empty(b);
                }
                tf
            };

            let mut else_state = state.clone();
            let not_c_nz = c_nz.not(b);
            else_state.path_active = entry_active.and(b, &not_c_nz);
            let else_flow = if matches!(else_state.path_active.konst, Some(false)) {
                FlowTargets::empty(b)
            } else {
                let mut ef = eval_region_flow(b, module, registry, &mut else_state, else_r, depth)?;
                if !matches!(ef.normal.active.konst, Some(false))
                    && !check_result_types(&ef.normal.values, &res_tys)
                {
                    else_state.trap_if(b, &ef.normal.active, TrapCode::Unreachable);
                    ef.normal = FlowOutcome::empty(b);
                }
                ef
            };

            state.merge_from(b, &c_nz, then_state, else_state)?;
            let mut merged = FlowTargets::empty(b);
            merge_outcome(b, &mut merged.normal, &then_flow.normal.active, &then_flow.normal.values)?;
            merge_outcome(b, &mut merged.normal, &else_flow.normal.active, &else_flow.normal.values)?;
            merge_outcome(b, &mut merged.returns, &then_flow.returns.active, &then_flow.returns.values)?;
            merge_outcome(b, &mut merged.returns, &else_flow.returns.active, &else_flow.returns.values)?;

            let br_depths: BTreeSet<u32> =
                then_flow.breaks.keys().chain(else_flow.breaks.keys()).copied().collect();
            for d in br_depths {
                let acc = merged.breaks.entry(d).or_insert_with(|| FlowOutcome::empty(b));
                if let Some(o) = then_flow.breaks.get(&d) {
                    merge_outcome(b, acc, &o.active, &o.values)?;
                }
                if let Some(o) = else_flow.breaks.get(&d) {
                    merge_outcome(b, acc, &o.active, &o.values)?;
                }
            }
            let ct_depths: BTreeSet<u32> =
                then_flow.continues.keys().chain(else_flow.continues.keys()).copied().collect();
            for d in ct_depths {
                let acc = merged.continues.entry(d).or_insert_with(|| FlowOutcome::empty(b));
                if let Some(o) = then_flow.continues.get(&d) {
                    merge_outcome(b, acc, &o.active, &o.values)?;
                }
                if let Some(o) = else_flow.continues.get(&d) {
                    merge_outcome(b, acc, &o.active, &o.values)?;
                }
            }
            Ok(merged)
        }
        RegionNode::BoundedLoop { max_iters, init_vars, state_vars, body } => {
            let Some(body_r) = region.child(body) else {
                let t = SymBool::from_const(b, true);
                state.trap_if(b, &t, TrapCode::Unreachable);
                return Ok(FlowTargets::empty(b));
            };
            let state_var_defs = region.region.vars_vec(state_vars);
            let mut loop_state: Vec<SymVal<B::Term>> = region
                .vals(init_vars)
                .map(|id| state.get_val(id))
                .collect::<Result<_, _>>()?;
            if loop_state.len() != state_var_defs.len()
                || loop_state.iter().zip(&state_var_defs).any(|(v, &(_, t))| v.ty != t)
            {
                let t = SymBool::from_const(b, true);
                state.trap_if(b, &t, TrapCode::Unreachable);
                return Ok(FlowTargets::empty(b));
            }

            let saved_env = state.env.clone();
            let mut iter_active = state.path_active.clone();
            let mut loop_exits = FlowTargets::empty(b);

            let unroll_limit = max_iters.min(MAX_SMT_LOOP_UNROLL);
            for _ in 0..unroll_limit {
                if matches!(iter_active.konst, Some(false)) {
                    break;
                }
                for (&(sid, _), val) in state_var_defs.iter().zip(&loop_state) {
                    state.env.insert(sid, val.clone());
                }
                state.path_active = iter_active.clone();
                if !state.charge_step(b) {
                    iter_active = SymBool::from_const(b, false);
                    break;
                }
                let body_flow = match body_r.node {
                    RegionNode::Block(stmts) => {
                        eval_block_stmts_raw(b, module, registry, state, body_r, stmts, depth)?
                    }
                    _ => eval_region_flow(b, module, registry, state, body_r, depth)?,
                };

                merge_outcome(b, &mut loop_exits.normal, &body_flow.normal.active, &body_flow.normal.values)?;
                merge_outcome(b, &mut loop_exits.returns, &body_flow.returns.active, &body_flow.returns.values)?;

                for (d, br) in body_flow.breaks {
                    if d == 0 {
                        merge_outcome(b, &mut loop_exits.normal, &br.active, &br.values)?;
                    } else {
                        let entry = loop_exits.breaks.entry(d - 1).or_insert_with(|| FlowOutcome::empty(b));
                        merge_outcome(b, entry, &br.active, &br.values)?;
                    }
                }

                let mut next_active = SymBool::from_const(b, false);
                for (d, ct) in body_flow.continues {
                    if d == 0 {
                        if ct.values.len() != state_var_defs.len()
                            || ct.values.iter().zip(&state_var_defs).any(|(v, &(_, t))| v.ty != t)
                        {
                            state.path_active = ct.active.clone();
                            let t = SymBool::from_const(b, true);
                            state.trap_if(b, &t, TrapCode::Unreachable);
                        } else {
                            loop_state = ct.values;
                            next_active = ct.active;
                        }
                    } else {
                        let entry = loop_exits.continues.entry(d - 1).or_insert_with(|| FlowOutcome::empty(b));
                        merge_outcome(b, entry, &ct.active, &ct.values)?;
                    }
                }
                iter_active = next_active;
            }

            if !matches!(iter_active.konst, Some(false)) {
                if max_iters <= MAX_SMT_LOOP_UNROLL {
                    state.path_active = iter_active.clone();
                    let t = SymBool::from_const(b, true);
                    state.trap_if(b, &t, TrapCode::OutOfFuel);
                } else {
                    state.unroll_overflow = state.unroll_overflow.or(b, &iter_active);
                    state.path_active = SymBool::from_const(b, false);
                }
            }
            state.env = saved_env;
            Ok(loop_exits)
        }
        RegionNode::InvariantLoop { .. } => Err(SieveError::EncodingError(
            "InvariantLoop must be split via split_invariant_loop before SMT encoding".into(),
        )),
    }
}

/// Evaluates a top-level region under `eval_region` semantics (Normal/Return succeed;
/// escaping Break/Continue trap `Unreachable`).
fn eval_top_region<B: SmtTarget>(
    b: &mut B,
    module: &Module,
    registry: &StratumRegistry,
    state: &mut ExecState<B::Term>,
    region: &Region,
) -> Result<Vec<SymVal<B::Term>>, SieveError> {
    let flow = eval_region_flow(b, module, registry, state, region.as_ref(), 0)?;
    for out in flow.breaks.values().chain(flow.continues.values()) {
        state.trap_if(b, &out.active, TrapCode::Unreachable);
    }
    let mut combined = FlowOutcome::empty(b);
    merge_outcome(b, &mut combined, &flow.normal.active, &flow.normal.values)?;
    merge_outcome(b, &mut combined, &flow.returns.active, &flow.returns.values)?;
    state.path_active = combined.active;
    Ok(combined.values)
}

// ── Free-Variable Type Inference for `check_equivalence` ──────────────────

struct FreeVarCollector<'a> {
    module: &'a Module,
    registry: &'a StratumRegistry,
    free_tys: BTreeMap<ValId, Option<ValType>>,
}

impl<'a> FreeVarCollector<'a> {
    fn record(&mut self, id: ValId, bound: &[ValId], ty: Option<ValType>) -> Result<(), SieveError> {
        if bound.contains(&id) {
            return Ok(());
        }
        match self.free_tys.get(&id).copied() {
            None => {
                self.free_tys.insert(id, ty);
            }
            Some(None) => {
                if ty.is_some() {
                    self.free_tys.insert(id, ty);
                }
            }
            Some(Some(existing)) => {
                if let Some(new_ty) = ty
                    && existing != new_ty
                {
                    return Err(SieveError::EncodingError(format!(
                        "conflicting inferred types for free ValId({}): {:?} vs {:?}",
                        id.0, existing, new_ty
                    )));
                }
            }
        }
        Ok(())
    }

    fn collect_region(
        &mut self,
        region: RegionRef<'_>,
        bound: &mut Vec<ValId>,
        is_root: bool,
    ) -> Result<Vec<Option<ValType>>, SieveError> {
        let mut local_tys: BTreeMap<ValId, ValType> = BTreeMap::new();
        for &id in bound.iter() {
            if let Some(Some(t)) = self.free_tys.get(&id).copied() {
                local_tys.insert(id, t);
            }
        }
        let mut out_tys = Vec::new();
        match region.node {
            RegionNode::Block(stmts) => {
                let saved_bound = bound.len();
                for stmt in region.stmts(stmts) {
                    match stmt {
                        Stmt::Let { dst, ty, op } => {
                            match op {
                                Op::ConstI32(_) | Op::ConstI64(_) | Op::GlobalGet(_) | Op::MemorySize(_) => {}
                                Op::Copy(v) => self.record(v, bound, Some(ty))?,
                                Op::Select { cond, true_val, false_val } => {
                                    self.record(cond, bound, Some(ValType::I32))?;
                                    self.record(true_val, bound, Some(ty))?;
                                    self.record(false_val, bound, Some(ty))?;
                                }
                                Op::Un(u, v) => self.record(v, bound, Some(u.input_ty()))?,
                                Op::Bin(bin, l, r) => {
                                    self.record(l, bound, Some(bin.operand_ty()))?;
                                    self.record(r, bound, Some(bin.operand_ty()))?;
                                }
                                Op::Load { addr, .. } => self.record(addr, bound, Some(ValType::I32))?,
                                Op::MemoryGrow { delta, .. } => self.record(delta, bound, Some(ValType::I32))?,
                            }
                            bound.push(dst);
                            local_tys.insert(dst, ty);
                        }
                        Stmt::Effect(eff) => match eff {
                            EffectOp::Store { addr, width, val, .. } => {
                                self.record(addr, bound, Some(ValType::I32))?;
                                let expected = if width == MemWidth::B8 { Some(ValType::I64) } else { None };
                                self.record(val, bound, expected)?;
                            }
                            EffectOp::MemoryCopy { dst, src, len, .. }
                            | EffectOp::MemoryFill { dst, val: src, len, .. } => {
                                for v in [dst, src, len] {
                                    self.record(v, bound, Some(ValType::I32))?;
                                }
                            }
                            EffectOp::GlobalSet { id, val } => {
                                let g_ty = self.module.global(id).map(|g| g.ty);
                                self.record(val, bound, g_ty)?;
                            }
                            EffectOp::Trap(_) | EffectOp::Nop => {}
                        },
                        Stmt::Region { results, region: sub_id } => {
                            let Some(sub_r) = region.child(sub_id) else {
                                return Err(SieveError::EncodingError("invalid child region id".into()));
                            };
                            let inner_tys = self.collect_region(sub_r, bound, false)?;
                            for (i, (id, ty)) in region.vars(results).enumerate() {
                                if let Some(Some(it)) = inner_tys.get(i).copied()
                                    && it != ty
                                {
                                    return Err(SieveError::EncodingError("region result type mismatch".into()));
                                }
                                bound.push(id);
                                local_tys.insert(id, ty);
                            }
                        }
                        Stmt::Call { results, target, args } => {
                            let param_tys: Vec<Option<ValType>> = match target {
                                CallTarget::Func(fid) => self
                                    .module
                                    .func(fid)
                                    .map(|f| f.params.iter().map(|&(_, t)| Some(t)).collect())
                                    .unwrap_or_default(),
                                CallTarget::Stratum(sid) => self
                                    .registry
                                    .get_op(sid)
                                    .map(|op| op.params.iter().map(|&(_, t)| Some(t)).collect())
                                    .unwrap_or_default(),
                                CallTarget::Host(hid) => self
                                    .module
                                    .host_contract(hid)
                                    .map(|hc| hc.params.iter().map(|&(_, t)| Some(t)).collect())
                                    .unwrap_or_default(),
                            };
                            for (i, a) in region.vals(args).enumerate() {
                                self.record(a, bound, param_tys.get(i).copied().flatten())?;
                            }
                            for (id, ty) in region.vars(results) {
                                bound.push(id);
                                local_tys.insert(id, ty);
                            }
                        }
                        Stmt::Yield(vs) => {
                            out_tys.clear();
                            for v in region.vals(vs) {
                                self.record(v, bound, None)?;
                                let t = if bound.contains(&v) {
                                    local_tys.get(&v).copied()
                                } else {
                                    self.free_tys.get(&v).copied().flatten()
                                };
                                out_tys.push(t);
                            }
                        }
                        Stmt::Return(vs) => {
                            if is_root {
                                out_tys.clear();
                            }
                            for v in region.vals(vs) {
                                self.record(v, bound, None)?;
                                if is_root {
                                    let t = if bound.contains(&v) {
                                        local_tys.get(&v).copied()
                                    } else {
                                        self.free_tys.get(&v).copied().flatten()
                                    };
                                    out_tys.push(t);
                                }
                            }
                        }
                        Stmt::Break { depth, cond, values } => {
                            if let Some(c) = cond {
                                self.record(c, bound, Some(ValType::I32))?;
                            }
                            if depth == 0 && out_tys.is_empty() {
                                for v in region.vals(values) {
                                    self.record(v, bound, None)?;
                                    let t = if bound.contains(&v) {
                                        local_tys.get(&v).copied()
                                    } else {
                                        self.free_tys.get(&v).copied().flatten()
                                    };
                                    out_tys.push(t);
                                }
                            } else {
                                for v in region.vals(values) {
                                    self.record(v, bound, None)?;
                                }
                            }
                        }
                        Stmt::Continue { cond, values, .. } => {
                            if let Some(c) = cond {
                                self.record(c, bound, Some(ValType::I32))?;
                            }
                            for v in region.vals(values) {
                                self.record(v, bound, None)?;
                            }
                        }
                    }
                }
                bound.truncate(saved_bound);
            }
            RegionNode::IfElse { cond, then_region, else_region, results } => {
                let (Some(then_r), Some(else_r)) = (region.child(then_region), region.child(else_region)) else {
                    return Err(SieveError::EncodingError("invalid IfElse child region".into()));
                };
                self.record(cond, bound, Some(ValType::I32))?;
                let _ = self.collect_region(then_r, bound, false)?;
                let _ = self.collect_region(else_r, bound, false)?;
                out_tys = region.tys(results).map(Some).collect();
            }
            RegionNode::BoundedLoop { init_vars, state_vars, body, .. } => {
                let Some(body_r) = region.child(body) else {
                    return Err(SieveError::EncodingError("invalid BoundedLoop body".into()));
                };
                let state_var_defs = region.region.vars_vec(state_vars);
                for (i, iv) in region.vals(init_vars).enumerate() {
                    self.record(iv, bound, state_var_defs.get(i).map(|&(_, t)| t))?;
                }
                let saved = bound.len();
                for &(sv, _) in &state_var_defs {
                    bound.push(sv);
                }
                out_tys = self.collect_region(body_r, bound, false)?;
                bound.truncate(saved);
            }
            RegionNode::InvariantLoop { .. } => {
                return Err(SieveError::EncodingError(
                    "InvariantLoop must be split via split_invariant_loop before SMT encoding".into(),
                ));
            }
        }
        Ok(out_tys)
    }
}

fn infer_equiv_params(
    module: &Module,
    registry: &StratumRegistry,
    lhs: &Region,
    rhs: &Region,
    precondition: Option<&Region>,
) -> Result<Vec<(ValId, ValType)>, SieveError> {
    let mut collector = FreeVarCollector { module, registry, free_tys: BTreeMap::new() };
    let mut bound = Vec::new();
    if let Some(pre) = precondition {
        let _ = collector.collect_region(pre.as_ref(), &mut bound, true)?;
    }
    let lhs_out = collector.collect_region(lhs.as_ref(), &mut bound, true)?;
    let rhs_out = collector.collect_region(rhs.as_ref(), &mut bound, true)?;

    // Unify direct free-var yield types between LHS and RHS when one side constrains the other.
    fn last_yield(r: &Region, stmts: Span) -> Option<Vec<ValId>> {
        for s in r.stmts(stmts).rev() {
            if let Stmt::Yield(vs) | Stmt::Return(vs) = s {
                return Some(r.vals_vec(vs));
            }
        }
        None
    }
    if let (RegionNode::Block(ls), RegionNode::Block(rs)) = (lhs.root, rhs.root)
        && let (Some(ly), Some(ry)) = (last_yield(lhs, ls), last_yield(rhs, rs))
    {
        for ((&lv, &rv), (&lt, &rt)) in ly.iter().zip(&ry).zip(lhs_out.iter().zip(&rhs_out)) {
            if collector.free_tys.contains_key(&lv)
                && let Some(t) = rt
            {
                collector.record(lv, &[], Some(t))?;
            }
            if collector.free_tys.contains_key(&rv)
                && let Some(t) = lt
            {
                collector.record(rv, &[], Some(t))?;
            }
        }
    }

    Ok(collector
        .free_tys
        .into_iter()
        .map(|(id, ty)| (id, ty.unwrap_or(ValType::I32)))
        .collect())
}

// ── Model Extraction & Query Execution ────────────────────────────────────

struct MemExtraction<'a, T> {
    id: MemId,
    mem: &'a MemSym<T>,
    witness: Option<(T, T)>,
}

fn extract_model<B: SmtTarget>(
    b: &mut B,
    param_syms: &[(ValId, SymVal<B::Term>)],
    global_syms: &[(GlobalId, SymVal<B::Term>)],
    mem_extractions: &[MemExtraction<'_, B::Term>],
) -> Result<SmtModel, SieveError> {
    let mut scalar_values = Vec::with_capacity(param_syms.len());
    for (id, sv) in param_syms {
        let raw = match sv.konst {
            Some(k) => k,
            None => b.get_bv_u64(&sv.term, bits_of(sv.ty))?,
        };
        let val = match sv.ty {
            ValType::I32 => Val::I32(raw as u32 as i32),
            ValType::I64 => Val::I64(raw as i64),
        };
        scalar_values.push((*id, val));
    }

    let mut global_values = Vec::with_capacity(global_syms.len());
    for (gid, sv) in global_syms {
        let raw = match sv.konst {
            Some(k) => k,
            None => b.get_bv_u64(&sv.term, bits_of(sv.ty))?,
        };
        let val = match sv.ty {
            ValType::I32 => Val::I32(raw as u32 as i32),
            ValType::I64 => Val::I64(raw as i64),
        };
        global_values.push((*gid, val));
    }

    let mut memory_bytes = Vec::new();
    for entry in mem_extractions {
        let init_len = b.get_bv_u64(&entry.mem.init_bytes, 64)?;
        let mut offsets: BTreeSet<u32> = BTreeSet::new();
        if let Some((w_term, diff_cond)) = &entry.witness
            && b.get_bool(diff_cond)?
        {
            let w_u32 = b.get_bv_u64(w_term, 32)? as u32;
            if (w_u32 as u64) < init_len {
                offsets.insert(w_u32);
            }
        }
        for (addr_term, width) in entry.mem.read_addrs.borrow().iter() {
            let addr_u32 = b.get_bv_u64(addr_term, 32)? as u32;
            for i in 0..width.bytes() {
                if let Some(off) = addr_u32.checked_add(i as u32)
                    && (off as u64) < init_len
                {
                    offsets.insert(off);
                }
            }
        }
        if !offsets.is_empty() {
            let mut bytes = Vec::with_capacity(offsets.len());
            for off in offsets {
                let off_t = b.bv_const(32, off as u64);
                let byte_sel = b.array_select(&entry.mem.init_array, &off_t);
                let byte_val = b.get_bv_u64(&byte_sel, 8)? as u8;
                bytes.push((off, byte_val));
            }
            memory_bytes.push((entry.id, bytes));
        }
    }

    Ok(SmtModel { scalar_values, global_values, memory_bytes })
}

#[allow(clippy::too_many_arguments)]
fn solve_with_overflow_guard<B: SmtTarget>(
    b: &mut B,
    goal_assertion: &B::Term,
    overflow_flag: &SymBool<B::Term>,
    budget_exceeded: bool,
    param_syms: &[(ValId, SymVal<B::Term>)],
    global_syms: &[(GlobalId, SymVal<B::Term>)],
    mem_extractions: &[MemExtraction<'_, B::Term>],
) -> Result<SmtResult, SieveError> {
    if matches!(overflow_flag.konst, Some(false)) {
        if budget_exceeded {
            return Ok(SmtResult::Unknown(
                "symbolic encoding step/call budget exceeded".into(),
            ));
        }
        b.assert_formula(goal_assertion)?;
        return match b.check_sat()? {
            RawSat::Unsat => Ok(SmtResult::Unsat),
            RawSat::Sat => {
                Ok(SmtResult::Sat(extract_model(b, param_syms, global_syms, mem_extractions)?))
            }
            RawSat::Unknown(msg) => Ok(SmtResult::Unknown(msg)),
        };
    }

    // Phase 1: check for concrete counterexamples within the bounded limit.
    // Skip Phase 1 if overflow is unconditionally true (`!overflow` is trivially false).
    if !matches!(overflow_flag.konst, Some(true)) {
        b.push()?;
        b.assert_formula(goal_assertion)?;
        let no_over = overflow_flag.not(b);
        b.assert_formula(&no_over.term)?;
        let res1 = b.check_sat()?;
        if res1 == RawSat::Sat {
            let model = extract_model(b, param_syms, global_syms, mem_extractions)?;
            b.pop()?;
            return Ok(SmtResult::Sat(model));
        }
        b.pop()?;

        if let RawSat::Unknown(msg) = res1 {
            return Ok(SmtResult::Unknown(msg));
        }
    }

    // Phase 2: check (under assumptions/preconditions ONLY, without goal_assertion)
    // whether the bounded unroll or symbolic encoding budget limit can actually be exceeded.
    b.push()?;
    b.assert_formula(&overflow_flag.term)?;
    let res2 = b.check_sat()?;
    b.pop()?;
    match res2 {
        RawSat::Unsat => Ok(SmtResult::Unsat),
        RawSat::Sat | RawSat::Unknown(_) => {
            let reason = if budget_exceeded {
                "symbolic encoding step/call budget exceeded"
            } else {
                "bounded SMT unroll limit exceeded (MemoryCopy/MemoryFill > 64 bytes or BoundedLoop > 64 iters)"
            };
            Ok(SmtResult::Unknown(reason.into()))
        }
    }
}

pub(crate) fn run_check_vc<B: SmtTarget>(
    b: &mut B,
    module: &Module,
    registry: &StratumRegistry,
    vc: &VcObligation,
    query_prefix: &str,
) -> Result<SmtResult, SieveError> {
    let mut base_state = ExecState::from_module(b, module, query_prefix)?;
    let global_syms: Vec<(GlobalId, SymVal<B::Term>)> =
        base_state.globals.iter().map(|(&gid, g)| (gid, g.val.clone())).collect();
    let mut param_syms = Vec::with_capacity(vc.params.len());
    for &(id, ty) in &vc.params {
        let term = b.fresh_bv(&format!("{query_prefix}_v_{}", id.0), bits_of(ty));
        let sv = SymVal { ty, term, konst: None };
        base_state.env.insert(id, sv.clone());
        param_syms.push((id, sv));
    }

    let mut overflow = SymBool::from_const(b, false);

    for assumption in &vc.assumptions {
        let mut a_state = base_state.clone();
        let vals = eval_top_region(b, module, registry, &mut a_state, assumption)?;
        overflow = overflow.or(b, &a_state.unroll_overflow);
        let not_trapped = a_state.trapped.not(b);
        let ok = match vals.first() {
            Some(v) if v.ty == ValType::I32 => {
                let nz = a_state.is_nonzero(b, v);
                not_trapped.and(b, &a_state.path_active).and(b, &nz)
            }
            _ => SymBool::from_const(b, false),
        };
        let ok_or_over = a_state.unroll_overflow.or(b, &ok);
        let guarded = a_state.path_assumptions.and(b, &ok_or_over);
        b.assert_formula(&guarded.term)?;
    }

    let mut g_state = base_state;
    let g_vals = eval_top_region(b, module, registry, &mut g_state, &vc.goal)?;
    overflow = overflow.or(b, &g_state.unroll_overflow);
    if !matches!(g_state.path_assumptions.konst, Some(true)) {
        b.assert_formula(&g_state.path_assumptions.term)?;
    }

    let g_holds = match g_vals.first() {
        Some(v) => {
            let nz = g_state.is_nonzero(b, v);
            g_state.trapped.not(b).and(b, &g_state.path_active).and(b, &nz)
        }
        None => SymBool::from_const(b, false),
    };
    let violated = g_holds.not(b);

    let mem_extractions: Vec<MemExtraction<'_, B::Term>> = g_state
        .mems
        .iter()
        .filter(|(_, m)| !m.read_addrs.borrow().is_empty())
        .map(|(&id, mem)| MemExtraction { id, mem, witness: None })
        .collect();

    solve_with_overflow_guard(
        b,
        &violated.term,
        &overflow,
        g_state.budget.is_exceeded(),
        &param_syms,
        &global_syms,
        &mem_extractions,
    )
}

fn is_pure_total_region(r: RegionRef<'_>, registry: &StratumRegistry, depth: u32) -> bool {
    if depth > MAX_CALL_DEPTH {
        return false;
    }
    match r.node {
        RegionNode::Block(span) => {
            for i in 0..span.len {
                let Some(stmt) = r.region.try_stmt(span, i) else {
                    return false;
                };
                match stmt {
                    Stmt::Let { op, .. } => match op {
                        Op::ConstI32(_)
                        | Op::ConstI64(_)
                        | Op::Copy(_)
                        | Op::Un(_, _)
                        | Op::Select { .. } => {}
                        Op::Bin(b, _, _) => {
                            if matches!(
                                b,
                                BinOp::I32DivS
                                    | BinOp::I32DivU
                                    | BinOp::I32RemS
                                    | BinOp::I32RemU
                                    | BinOp::I64DivS
                                    | BinOp::I64DivU
                                    | BinOp::I64RemS
                                    | BinOp::I64RemU
                            ) {
                                return false;
                            }
                        }
                        Op::Load { .. }
                        | Op::GlobalGet(_)
                        | Op::MemorySize(_)
                        | Op::MemoryGrow { .. } => return false,
                    },
                    Stmt::Effect(EffectOp::Nop) => {}
                    Stmt::Effect(_) => return false,
                    Stmt::Call { target: CallTarget::Stratum(callee), .. } => {
                        if !is_pure_total_stratum(callee, registry, depth + 1) {
                            return false;
                        }
                    }
                    Stmt::Call { .. } => return false,
                    Stmt::Region { region, .. } => {
                        let Some(sub) = r.child(region) else {
                            return false;
                        };
                        if !is_pure_total_region(sub, registry, depth + 1) {
                            return false;
                        }
                    }
                    Stmt::Yield(_) | Stmt::Return(_) | Stmt::Break { .. } | Stmt::Continue { .. } => {}
                }
            }
            true
        }
        RegionNode::IfElse { then_region, else_region, .. } => {
            r.child(then_region).is_some_and(|s| is_pure_total_region(s, registry, depth + 1))
                && r.child(else_region).is_some_and(|s| is_pure_total_region(s, registry, depth + 1))
        }
        RegionNode::BoundedLoop { max_iters, body, .. } => {
            max_iters <= MAX_SMT_LOOP_UNROLL
                && r.child(body).is_some_and(|s| is_pure_total_region(s, registry, depth + 1))
        }
        RegionNode::InvariantLoop { .. } => false,
    }
}

pub(crate) fn is_pure_total_stratum(sid: StratumId, registry: &StratumRegistry, depth: u32) -> bool {
    if depth > MAX_CALL_DEPTH {
        return false;
    }
    let Some(op) = registry.get_op(sid) else {
        return false;
    };
    if op.results.is_empty() {
        return false;
    }
    is_pure_total_region(op.body.as_ref(), registry, depth + 1)
}

fn collect_pure_total_strata_in_module(
    module: &Module,
    region: &Region,
    registry: &StratumRegistry,
    out: &mut BTreeSet<StratumId>,
) {
    fn walk(
        module: &Module,
        r: RegionRef<'_>,
        registry: &StratumRegistry,
        out: &mut BTreeSet<StratumId>,
        visited_funcs: &mut BTreeSet<FuncId>,
        depth: u32,
    ) {
        if depth > MAX_CALL_DEPTH {
            return;
        }
        match r.node {
            RegionNode::Block(span) => {
                for i in 0..span.len {
                    if let Some(stmt) = r.region.try_stmt(span, i) {
                        match stmt {
                            Stmt::Call { target: CallTarget::Stratum(sid), .. } => {
                                if is_pure_total_stratum(sid, registry, 0) {
                                    out.insert(sid);
                                } else if let Some(op) = registry.get_op(sid) {
                                    walk(module, op.body.as_ref(), registry, out, visited_funcs, depth + 1);
                                }
                            }
                            Stmt::Call { target: CallTarget::Func(fid), .. } => {
                                if visited_funcs.insert(fid)
                                    && let Some(f) = module.func(fid)
                                {
                                    walk(module, f.body.as_ref(), registry, out, visited_funcs, depth + 1);
                                }
                            }
                            Stmt::Region { region, .. } => {
                                if let Some(sub) = r.child(region) {
                                    walk(module, sub, registry, out, visited_funcs, depth + 1);
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }
            RegionNode::IfElse { then_region, else_region, .. } => {
                if let Some(s) = r.child(then_region) {
                    walk(module, s, registry, out, visited_funcs, depth + 1);
                }
                if let Some(s) = r.child(else_region) {
                    walk(module, s, registry, out, visited_funcs, depth + 1);
                }
            }
            RegionNode::BoundedLoop { body, .. } => {
                if let Some(s) = r.child(body) {
                    walk(module, s, registry, out, visited_funcs, depth + 1);
                }
            }
            RegionNode::InvariantLoop { cond, invariant_pred, fuel_measure, body, .. } => {
                for id in [cond, invariant_pred, fuel_measure, body] {
                    if let Some(s) = r.child(id) {
                        walk(module, s, registry, out, visited_funcs, depth + 1);
                    }
                }
            }
        }
    }
    let mut visited_funcs = BTreeSet::new();
    walk(module, region.as_ref(), registry, out, &mut visited_funcs, 0);
}

struct ActiveStackRefinement<T> {
    sp_global: GlobalId,
    stack_mem: MemId,
    sp_in: SymVal<T>,
}

/// Applies shadow-stack pre-state constraints to `base_state` before cloning it into
/// `requires`/`precondition`/`lhs`/`rhs`/`entry`.
///
/// Returns `Ok(None)` when `sr.stack_pointer_global` is not defined in `module.globals`
/// (graceful no-op on modules without a shadow stack).
fn apply_stack_refinement_pre<B: SmtTarget>(
    b: &mut B,
    module: &Module,
    base_state: &mut ExecState<B::Term>,
    sr: StackRefinement,
    use_initial_state: bool,
) -> Result<Option<ActiveStackRefinement<B::Term>>, SieveError> {
    let Some(g_def) = module.global(sr.stack_pointer_global) else {
        return Ok(None);
    };
    if g_def.ty != ValType::I32 {
        return Err(SieveError::EncodingError(format!(
            "StackRefinement stack_pointer_global {:?} must have type I32, got {:?}",
            sr.stack_pointer_global, g_def.ty
        )));
    }
    let init_u32 = g_def.init.as_u32().ok_or_else(|| {
        SieveError::EncodingError(format!(
            "StackRefinement stack_pointer_global {:?} has non-I32 initializer",
            sr.stack_pointer_global
        ))
    })?;

    let mem_upper_bytes: Option<u64> = module.memories.iter().find(|m| m.id == sr.stack_mem).map(|m| {
        if use_initial_state {
            (m.min_pages as u64) * (WASM_PAGE_SIZE as u64)
        } else {
            let limit = m.max_pages.unwrap_or(MAX_WASM_PAGES).min(MAX_WASM_PAGES);
            (limit as u64) * (WASM_PAGE_SIZE as u64)
        }
    });

    let pin_init = sr.pin_initial_sp && init_u32 >= sr.min_stack_bytes;
    let sp_in = if pin_init {
        if let Some(upper) = mem_upper_bytes
            && (init_u32 as u64) > upper
        {
            return Err(SieveError::EncodingError(format!(
                "StackRefinement pinned SP_in ({init_u32}) exceeds memory {:?} maximum size ({upper} bytes)",
                sr.stack_mem
            )));
        }
        let sv = SymVal {
            ty: ValType::I32,
            term: b.bv_const(32, init_u32 as u64),
            konst: Some(init_u32 as u64),
        };
        if let Some(g_sym) = base_state.globals.get_mut(&sr.stack_pointer_global) {
            g_sym.val = sv.clone();
        }
        if let Some(mem) = base_state.mems.get(&sr.stack_mem) {
            let sp64 = b.bv_const(64, init_u32 as u64);
            let le_mem = b.bv_ule(64, &sp64, &mem.init_bytes);
            b.assert_formula(&le_mem)?;
        }
        sv
    } else {
        let g_sym = base_state.globals.get(&sr.stack_pointer_global).expect("global present");
        let sv = g_sym.val.clone();
        if let Some(fixed_sp) = sv.konst {
            let fixed_u32 = fixed_sp as u32;
            if fixed_u32 < sr.min_stack_bytes || (fixed_u32 & 0xf) != 0 {
                return Err(SieveError::EncodingError(format!(
                    "StackRefinement fixed SP_in ({fixed_u32}) violates min_stack_bytes ({}) or 16-byte alignment",
                    sr.min_stack_bytes
                )));
            }
            if let Some(upper) = mem_upper_bytes
                && (fixed_u32 as u64) > upper
            {
                return Err(SieveError::EncodingError(format!(
                    "StackRefinement fixed SP_in ({fixed_u32}) exceeds memory {:?} maximum size ({upper} bytes)",
                    sr.stack_mem
                )));
            }
        } else {
            let min_aligned = ((sr.min_stack_bytes as u64) + 15) & !15;
            if min_aligned > u32::MAX as u64 {
                return Err(SieveError::EncodingError(format!(
                    "StackRefinement min_stack_bytes ({}) has no 16-byte aligned 32-bit SP_in",
                    sr.min_stack_bytes
                )));
            }
            if let Some(upper) = mem_upper_bytes
                && min_aligned > upper
            {
                return Err(SieveError::EncodingError(format!(
                    "StackRefinement min_stack_bytes ({}) has no 16-byte aligned SP_in within memory {:?} maximum size ({upper} bytes)",
                    sr.min_stack_bytes, sr.stack_mem
                )));
            }
            let min_t = b.bv_const(32, sr.min_stack_bytes as u64);
            let ge_min = b.bv_uge(32, &sv.term, &min_t);
            b.assert_formula(&ge_min)?;
            let mask15 = b.bv_const(32, 0xf);
            let zero32 = b.bv_const(32, 0);
            let rem16 = b.bv_and(32, &sv.term, &mask15);
            let aligned = b.eq(&rem16, &zero32);
            b.assert_formula(&aligned)?;
        }
        if let Some(mem) = base_state.mems.get(&sr.stack_mem) {
            let sp64 = b.bv_zext(32, 32, &sv.term);
            let le_mem = b.bv_ule(64, &sp64, &mem.init_bytes);
            b.assert_formula(&le_mem)?;
        }
        sv
    };

    Ok(Some(ActiveStackRefinement {
        sp_global: sr.stack_pointer_global,
        stack_mem: sr.stack_mem,
        sp_in,
    }))
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn run_check_equivalence_with_options<B: SmtTarget>(
    b: &mut B,
    module: &Module,
    registry: &StratumRegistry,
    lhs: &Region,
    rhs: &Region,
    precondition: Option<&Region>,
    opts: &EquivOptions,
    query_prefix: &str,
) -> Result<SmtResult, SieveError> {
    // Stage 2a (CEGAR): if LHS and RHS share pure-total Strata, attempt a fast UF congruence
    // pass first. If UNSAT, equivalence is 100% proved without bit-blasting the Stratum bodies;
    // if SAT or Unknown (possibly spurious), pop and fall back to exact Layer-0 inlining.
    let mut lhs_pure = BTreeSet::new();
    let mut rhs_pure = BTreeSet::new();
    collect_pure_total_strata_in_module(module, lhs, registry, &mut lhs_pure);
    collect_pure_total_strata_in_module(module, rhs, registry, &mut rhs_pure);
    let shared_uf: BTreeSet<StratumId> = lhs_pure.intersection(&rhs_pure).copied().collect();

    if !shared_uf.is_empty() {
        b.push()?;
        let uf_prefix = format!("{query_prefix}_uf");
        let uf_res = run_check_equivalence_inner(
            b,
            module,
            registry,
            lhs,
            rhs,
            precondition,
            opts,
            &uf_prefix,
            Some(shared_uf),
        );
        b.pop()?;
        if let Ok(SmtResult::Unsat) = uf_res {
            return Ok(SmtResult::Unsat);
        }
    }

    run_check_equivalence_inner(
        b,
        module,
        registry,
        lhs,
        rhs,
        precondition,
        opts,
        query_prefix,
        None,
    )
}

#[allow(clippy::too_many_arguments)]
fn run_check_equivalence_inner<B: SmtTarget>(
    b: &mut B,
    module: &Module,
    registry: &StratumRegistry,
    lhs: &Region,
    rhs: &Region,
    precondition: Option<&Region>,
    opts: &EquivOptions,
    query_prefix: &str,
    uf_strata: Option<BTreeSet<StratumId>>,
) -> Result<SmtResult, SieveError> {
    let params = infer_equiv_params(module, registry, lhs, rhs, precondition)?;
    let mut base_state = ExecState::from_module(b, module, query_prefix)?;
    let active_stack = match opts.stack_refinement {
        Some(sr) => apply_stack_refinement_pre(b, module, &mut base_state, sr, false)?,
        None => None,
    };
    let global_syms: Vec<(GlobalId, SymVal<B::Term>)> =
        base_state.globals.iter().map(|(&gid, g)| (gid, g.val.clone())).collect();
    let uf_table = uf_strata.map(|set| UfTable::new(set, query_prefix.to_string()));
    base_state.uf_table = uf_table.clone();
    let mut param_syms = Vec::with_capacity(params.len());
    for &(id, ty) in &params {
        let term = b.fresh_bv(&format!("{query_prefix}_v_{}", id.0), bits_of(ty));
        let sv = SymVal { ty, term, konst: None };
        base_state.env.insert(id, sv.clone());
        param_syms.push((id, sv));
    }

    let mut overflow = SymBool::from_const(b, false);
    if let Some(pre) = precondition {
        let mut p_state = base_state.clone();
        let p_vals = eval_top_region(b, module, registry, &mut p_state, pre)?;
        overflow = overflow.or(b, &p_state.unroll_overflow);
        let ok = match p_vals.first() {
            Some(v) => {
                let nz = p_state.is_nonzero(b, v);
                p_state.trapped.not(b).and(b, &p_state.path_active).and(b, &nz)
            }
            None => SymBool::from_const(b, false),
        };
        let ok_or_over = p_state.unroll_overflow.or(b, &ok);
        let guarded = p_state.path_assumptions.and(b, &ok_or_over);
        b.assert_formula(&guarded.term)?;
    }

    let mut lhs_state = base_state.clone();
    let lhs_vals = eval_top_region(b, module, registry, &mut lhs_state, lhs)?;
    let mut rhs_state = base_state;
    let rhs_vals = eval_top_region(b, module, registry, &mut rhs_state, rhs)?;

    overflow = overflow.or(b, &lhs_state.unroll_overflow).or(b, &rhs_state.unroll_overflow);
    if !matches!(lhs_state.path_assumptions.konst, Some(true)) {
        b.assert_formula(&lhs_state.path_assumptions.term)?;
    }
    if !matches!(rhs_state.path_assumptions.konst, Some(true)) {
        b.assert_formula(&rhs_state.path_assumptions.term)?;
    }

    // Build discrepancy formula:
    // (lhs.trapped != rhs.trapped)
    // || (lhs.trapped && rhs.trapped && lhs.trap_code != rhs.trap_code)
    // || sp_leak
    // || (!lhs.trapped && !rhs.trapped && (results_differ || globals_differ || mem_sizes_differ || witness_mem_byte_differs))
    let trap_eq = b.eq(&lhs_state.trapped.term, &rhs_state.trapped.term);
    let trap_mismatch = SymBool::symbolic(b.not(&trap_eq));
    let both_trapped = lhs_state.trapped.and(b, &rhs_state.trapped);
    let tc_eq = b.eq(&lhs_state.trap_code, &rhs_state.trap_code);
    let tc_neq = SymBool::symbolic(b.not(&tc_eq));
    let trap_code_diff = both_trapped.and(b, &tc_neq);

    let lhs_not_trapped = lhs_state.trapped.not(b);
    let rhs_not_trapped = rhs_state.trapped.not(b);
    let neither_trapped = lhs_not_trapped.and(b, &rhs_not_trapped);
    let mut non_trap_diff = SymBool::from_const(b, false);

    // Shadow-stack preservation: on every active non-trapping path, BOTH lhs and rhs must
    // restore `stack_pointer_global` to `SP_in` (even if both leak SP by the exact same delta
    // or neither touches memory).
    let mut sp_leak = SymBool::from_const(b, false);
    if let Some(ref active_sr) = active_stack {
        if let Some(lhs_sp) = lhs_state.globals.get(&active_sr.sp_global) {
            let lhs_sp_eq = b.eq(&lhs_sp.val.term, &active_sr.sp_in.term);
            let lhs_sp_neq = SymBool::symbolic(b.not(&lhs_sp_eq));
            let lhs_clean = lhs_not_trapped.and(b, &lhs_state.path_active);
            let lhs_leak = lhs_clean.and(b, &lhs_sp_neq);
            sp_leak = sp_leak.or(b, &lhs_leak);
        }
        if let Some(rhs_sp) = rhs_state.globals.get(&active_sr.sp_global) {
            let rhs_sp_eq = b.eq(&rhs_sp.val.term, &active_sr.sp_in.term);
            let rhs_sp_neq = SymBool::symbolic(b.not(&rhs_sp_eq));
            let rhs_clean = rhs_not_trapped.and(b, &rhs_state.path_active);
            let rhs_leak = rhs_clean.and(b, &rhs_sp_neq);
            sp_leak = sp_leak.or(b, &rhs_leak);
        }
    }

    let lhs_reachable = !matches!(lhs_state.path_active.konst, Some(false))
        && !matches!(lhs_state.trapped.konst, Some(true));
    let rhs_reachable = !matches!(rhs_state.path_active.konst, Some(false))
        && !matches!(rhs_state.trapped.konst, Some(true));

    if lhs_reachable
        && rhs_reachable
        && (lhs_vals.len() != rhs_vals.len()
            || lhs_vals.iter().zip(&rhs_vals).any(|(l, r)| l.ty != r.ty))
    {
        return Err(SieveError::EncodingError(format!(
            "LHS and RHS result signature mismatch: {:?} vs {:?}",
            lhs_vals.iter().map(|v| v.ty).collect::<Vec<_>>(),
            rhs_vals.iter().map(|v| v.ty).collect::<Vec<_>>()
        )));
    }
    if lhs_reachable && rhs_reachable {
        for (lv, rv) in lhs_vals.iter().zip(&rhs_vals) {
            let eq_v = b.eq(&lv.term, &rv.term);
            let neq = SymBool::symbolic(b.not(&eq_v));
            non_trap_diff = non_trap_diff.or(b, &neq);
        }
    }

    for (gid, lg) in &lhs_state.globals {
        if lg.mutable
            && let Some(rg) = rhs_state.globals.get(gid)
        {
            let eq_g = b.eq(&lg.val.term, &rg.val.term);
            let neq = SymBool::symbolic(b.not(&eq_g));
            non_trap_diff = non_trap_diff.or(b, &neq);
        }
    }

    let mut mem_witnesses: Vec<MemExtraction<'_, B::Term>> = Vec::new();
    for (&mid, lm) in &lhs_state.mems {
        let rm = rhs_state.mems.get(&mid).expect("memory present in both");
        if lm.touched_by_write_or_grow || rm.touched_by_write_or_grow {
            let eq_sz = b.eq(&lm.bytes, &rm.bytes);
            let size_diff = SymBool::symbolic(b.not(&eq_sz));
            non_trap_diff = non_trap_diff.or(b, &size_diff);

            let witness = b.fresh_bv(&format!("{query_prefix}_witness_mem_{}", mid.0), 32);
            let w64 = b.bv_zext(32, 32, &witness);
            let mut in_live = SymBool::symbolic(b.bv_ult(64, &w64, &lm.bytes));
            if let Some(ref active_sr) = active_stack
                && mid == active_sr.stack_mem
            {
                let ge_sp = SymBool::symbolic(b.bv_uge(32, &witness, &active_sr.sp_in.term));
                in_live = in_live.and(b, &ge_sp);
            }
            let l_byte = eval_mem_byte(b, lm, &witness);
            let r_byte = eval_mem_byte(b, rm, &witness);
            let eq_byte = b.eq(&l_byte, &r_byte);
            let byte_diff = SymBool::symbolic(b.not(&eq_byte));
            let mem_diff = in_live.and(b, &byte_diff);
            non_trap_diff = non_trap_diff.or(b, &mem_diff);
            let active_mem_diff = neither_trapped.and(b, &mem_diff);
            mem_witnesses.push(MemExtraction {
                id: mid,
                mem: lm,
                witness: Some((witness, active_mem_diff.term)),
            });
        } else if !lm.read_addrs.borrow().is_empty() {
            mem_witnesses.push(MemExtraction { id: mid, mem: lm, witness: None });
        }
    }

    let neither_and_diff = neither_trapped.and(b, &non_trap_diff);
    let diff = trap_mismatch.or(b, &trap_code_diff).or(b, &neither_and_diff).or(b, &sp_leak);

    if let Some(ref rc) = uf_table {
        let tbl = rc.borrow();
        if tbl.overflow {
            return Ok(SmtResult::Unknown("uf call cap exceeded".into()));
        }
        tbl.assert_congruence_axioms(b)?;
    }

    solve_with_overflow_guard(
        b,
        &diff.term,
        &overflow,
        rhs_state.budget.is_exceeded(),
        &param_syms,
        &global_syms,
        &mem_witnesses,
    )
}

fn validate_contract_spec(contract: &ContractSpec<'_>) -> Result<(), SieveError> {
    if let Some(req_params) = contract.requires_params
        && (req_params.len() != contract.params.len()
            || req_params.iter().zip(contract.params).any(|(a, b)| a.1 != b.1))
    {
        return Err(SieveError::EncodingError(format!(
            "requires_params signature {:?} does not match entry params {:?}",
            req_params.iter().map(|&(_, t)| t).collect::<Vec<_>>(),
            contract.params.iter().map(|&(_, t)| t).collect::<Vec<_>>()
        )));
    }
    if let Some(ens_params) = contract.ensures_params {
        let total = contract.params.len() + contract.results.len();
        if ens_params.len() == total {
            let expected = contract
                .params
                .iter()
                .map(|&(_, t)| t)
                .chain(contract.results.iter().copied());
            if ens_params.iter().map(|&(_, t)| t).ne(expected) {
                return Err(SieveError::EncodingError(
                    "ensures_params types do not match (entry_params..., entry_results...)".into(),
                ));
            }
        } else if ens_params.len() == contract.results.len() {
            if ens_params.iter().map(|&(_, t)| t).ne(contract.results.iter().copied()) {
                return Err(SieveError::EncodingError(
                    "ensures_params types do not match entry_results".into(),
                ));
            }
        } else if !ens_params.is_empty() {
            return Err(SieveError::EncodingError(format!(
                "ensures_params arity {} does not match params+results ({}), results ({}), or 0",
                ens_params.len(),
                total,
                contract.results.len()
            )));
        }
    }
    if let Some(sf) = &contract.slice_frame {
        for (role, expr) in [("base", sf.base), ("len", sf.len)] {
            if let SliceBoundExpr::Param(vid) = expr {
                match contract.params.iter().find(|(id, _)| *id == vid) {
                    Some((_, ValType::I32)) => {}
                    Some((_, other)) => {
                        return Err(SieveError::EncodingError(format!(
                            "SliceFrame {role} param ValId({}) must be I32, got {:?}",
                            vid.0, other
                        )));
                    }
                    None => {
                        return Err(SieveError::EncodingError(format!(
                            "SliceFrame {role} references unknown param ValId({})",
                            vid.0
                        )));
                    }
                }
            }
        }
    }
    Ok(())
}

fn eval_contract_pred<B: SmtTarget>(
    b: &mut B,
    module: &Module,
    registry: &StratumRegistry,
    state: &mut ExecState<B::Term>,
    pred: &Region,
    role: &str,
) -> Result<SymBool<B::Term>, SieveError> {
    let vals = eval_top_region(b, module, registry, state, pred)?;
    let reachable = !matches!(state.path_active.konst, Some(false))
        && !matches!(state.trapped.konst, Some(true));
    if reachable && (vals.len() != 1 || vals[0].ty != ValType::I32) {
        return Err(SieveError::EncodingError(format!(
            "contract {role} predicate must yield a single I32, got {:?}",
            vals.iter().map(|v| v.ty).collect::<Vec<_>>()
        )));
    }
    Ok(match vals.first() {
        Some(v) if v.ty == ValType::I32 => {
            let nz = state.is_nonzero(b, v);
            state.trapped.not(b).and(b, &state.path_active).and(b, &nz)
        }
        _ => SymBool::from_const(b, false),
    })
}

pub(crate) fn run_check_contract<B: SmtTarget>(
    b: &mut B,
    module: &Module,
    registry: &StratumRegistry,
    contract: &ContractSpec<'_>,
    query_prefix: &str,
) -> Result<SmtResult, SieveError> {
    validate_contract_spec(contract)?;

    // Stage 2a (CEGAR): attempt Ackermann UF abstraction for pure-total Strata referenced
    // across entry/requires/ensures/invariant first. UNSAT under UF strictly implies UNSAT
    // under exact Layer-0 inlining; SAT/Unknown pops and falls back to exact Layer-0.
    let mut pure_strata = BTreeSet::new();
    collect_pure_total_strata_in_module(module, contract.entry, registry, &mut pure_strata);
    if let Some(req) = contract.requires {
        collect_pure_total_strata_in_module(module, req, registry, &mut pure_strata);
    }
    if let Some(ens) = contract.ensures {
        collect_pure_total_strata_in_module(module, ens, registry, &mut pure_strata);
    }
    if let Some(inv) = contract.invariant {
        collect_pure_total_strata_in_module(module, inv, registry, &mut pure_strata);
    }

    if !pure_strata.is_empty() {
        b.push()?;
        let uf_prefix = format!("{query_prefix}_uf");
        let uf_res = run_check_contract_inner(
            b,
            module,
            registry,
            contract,
            &uf_prefix,
            Some(pure_strata),
        );
        b.pop()?;
        if let Ok(SmtResult::Unsat) = uf_res {
            return Ok(SmtResult::Unsat);
        }
    }

    run_check_contract_inner(b, module, registry, contract, query_prefix, None)
}

fn run_check_contract_inner<B: SmtTarget>(
    b: &mut B,
    module: &Module,
    registry: &StratumRegistry,
    contract: &ContractSpec<'_>,
    query_prefix: &str,
    uf_strata: Option<BTreeSet<StratumId>>,
) -> Result<SmtResult, SieveError> {
    let mut base_state =
        ExecState::from_module_with_mode(b, module, query_prefix, contract.use_initial_state)?;
    if let Some(sf) = &contract.slice_frame
        && !base_state.mems.contains_key(&sf.mem)
    {
        return Err(SieveError::EncodingError(format!(
            "SliceFrame references unknown memory {:?}",
            sf.mem
        )));
    }
    let active_stack = match contract.stack_refinement {
        Some(sr) => apply_stack_refinement_pre(
            b,
            module,
            &mut base_state,
            sr,
            contract.use_initial_state,
        )?,
        None => None,
    };
    let global_syms: Vec<(GlobalId, SymVal<B::Term>)> =
        base_state.globals.iter().map(|(&gid, g)| (gid, g.val.clone())).collect();
    let uf_table = uf_strata.map(|set| UfTable::new(set, query_prefix.to_string()));
    base_state.uf_table = uf_table.clone();

    let mut param_syms = Vec::with_capacity(contract.params.len());
    for &(id, ty) in contract.params {
        let term = b.fresh_bv(&format!("{query_prefix}_v_{}", id.0), bits_of(ty));
        let sv = SymVal { ty, term, konst: None };
        base_state.env.insert(id, sv.clone());
        param_syms.push((id, sv));
    }

    let mut overflow = SymBool::from_const(b, false);

    // 1. Pre-state invariant (assumed ONLY for inductive checks, i.e., !use_initial_state).
    if !contract.use_initial_state
        && let Some(inv) = contract.invariant
    {
        let mut inv_pre = base_state.clone();
        inv_pre.env.clear();
        let inv_ok = eval_contract_pred(b, module, registry, &mut inv_pre, inv, "invariant(pre)")?;
        overflow = overflow.or(b, &inv_pre.unroll_overflow);
        // Guard with `unroll_overflow || inv_ok` so Phase 1 (!overflow) strictly enforces `inv_ok`
        // while Phase 2 (overflow) still catches reachable unroll overflow inside `invariant(pre)`.
        let inv_or_over = inv_pre.unroll_overflow.or(b, &inv_ok);
        let pre_cond = inv_pre.path_assumptions.and(b, &inv_or_over);
        b.assert_formula(&pre_cond.term)?;
    }

    // 2. Pre-state `requires` (assumed on pre_state).
    if let Some(req) = contract.requires {
        let mut req_state = base_state.clone();
        if let Some(req_params) = contract.requires_params {
            req_state.env.clear();
            for (&(id, _), (_, sv)) in req_params.iter().zip(&param_syms) {
                req_state.env.insert(id, sv.clone());
            }
        }
        let req_ok = eval_contract_pred(b, module, registry, &mut req_state, req, "requires")?;
        overflow = overflow.or(b, &req_state.unroll_overflow);
        let req_or_over = req_state.unroll_overflow.or(b, &req_ok);
        let req_cond = req_state.path_assumptions.and(b, &req_or_over);
        b.assert_formula(&req_cond.term)?;
    }

    // 3. Execute `entry` from pre_state -> post_state.
    let mut entry_state = base_state;
    let entry_vals = eval_top_region(b, module, registry, &mut entry_state, contract.entry)?;
    overflow = overflow.or(b, &entry_state.unroll_overflow);
    if !matches!(entry_state.path_assumptions.konst, Some(true)) {
        b.assert_formula(&entry_state.path_assumptions.term)?;
    }

    let entry_clean = entry_state.trapped.not(b).and(b, &entry_state.path_active);
    let entry_reachable = !matches!(entry_clean.konst, Some(false));
    let entry_res_vals = if entry_reachable {
        if !check_result_types(&entry_vals, contract.results) {
            return Err(SieveError::EncodingError(format!(
                "contract entry result signature mismatch: expected {:?}, got {:?}",
                contract.results,
                entry_vals.iter().map(|v| v.ty).collect::<Vec<_>>()
            )));
        }
        entry_vals
    } else {
        contract
            .results
            .iter()
            .map(|&ty| SymVal { ty, term: b.bv_const(bits_of(ty), 0), konst: Some(0) })
            .collect()
    };

    // 4. Evaluate post-state obligations (`invariant(post)`, `ensures`, `StackRefinement`,
    //    and `SliceFrame`) on clean paths.
    let mut post_ok = SymBool::from_const(b, true);
    let mut slice_witness: Option<(MemId, B::Term, B::Term)> = None;
    if entry_reachable {
        if let Some(inv) = contract.invariant {
            let mut inv_post = entry_state.clone();
            inv_post.env.clear();
            inv_post.trapped = SymBool::from_const(b, false);
            inv_post.trap_code = b.bv_const(8, 0);
            inv_post.assert_failed = SymBool::from_const(b, false);
            inv_post.path_active = entry_clean.clone();
            inv_post.path_assumptions = SymBool::from_const(b, true);
            let inv_ok =
                eval_contract_pred(b, module, registry, &mut inv_post, inv, "invariant(post)")?;
            overflow = overflow.or(b, &inv_post.unroll_overflow);
            if !matches!(inv_post.path_assumptions.konst, Some(true)) {
                b.assert_formula(&inv_post.path_assumptions.term)?;
            }
            post_ok = post_ok.and(b, &inv_ok);
        }

        if let Some(ens) = contract.ensures {
            let mut ens_state = entry_state.clone();
            ens_state.env.clear();
            if let Some(ens_params) = contract.ensures_params {
                if ens_params.len() == contract.params.len() + contract.results.len() {
                    for (&(id, _), (_, sv)) in ens_params.iter().zip(&param_syms) {
                        ens_state.env.insert(id, sv.clone());
                    }
                    for (&(id, _), rv) in
                        ens_params[contract.params.len()..].iter().zip(&entry_res_vals)
                    {
                        ens_state.env.insert(id, rv.clone());
                    }
                } else if ens_params.len() == contract.results.len() {
                    for (&(id, _), rv) in ens_params.iter().zip(&entry_res_vals) {
                        ens_state.env.insert(id, rv.clone());
                    }
                }
            } else {
                for (id, sv) in &param_syms {
                    ens_state.env.insert(*id, sv.clone());
                }
                let base = contract
                    .params
                    .iter()
                    .map(|(v, _)| v.0.saturating_add(1))
                    .max()
                    .unwrap_or(0);
                for (i, rv) in entry_res_vals.iter().enumerate() {
                    ens_state.env.insert(ValId(base + i as u32), rv.clone());
                }
            }
            ens_state.trapped = SymBool::from_const(b, false);
            ens_state.trap_code = b.bv_const(8, 0);
            ens_state.assert_failed = SymBool::from_const(b, false);
            ens_state.path_active = entry_clean.clone();
            ens_state.path_assumptions = SymBool::from_const(b, true);
            let ens_ok = eval_contract_pred(b, module, registry, &mut ens_state, ens, "ensures")?;
            overflow = overflow.or(b, &ens_state.unroll_overflow);
            if !matches!(ens_state.path_assumptions.konst, Some(true)) {
                b.assert_formula(&ens_state.path_assumptions.term)?;
            }
            post_ok = post_ok.and(b, &ens_ok);
        }

        // Shadow-stack preservation: on every clean path, `entry_sp_out == SP_in`.
        if let Some(ref active_sr) = active_stack
            && let Some(sp_out) = entry_state.globals.get(&active_sr.sp_global)
        {
            let sp_eq = b.eq(&sp_out.val.term, &active_sr.sp_in.term);
            let sp_preserved = SymBool::symbolic(sp_eq);
            post_ok = post_ok.and(b, &sp_preserved);
        }

        // Intra-memory `SliceFrame`: no memory growth and every untouched live byte `w`
        // outside the 64-bit non-wrapping interval `[base, base + len)` is bit-for-bit preserved.
        if let Some(sf) = &contract.slice_frame {
            let mem_post = entry_state.mems.get(&sf.mem).expect("validated");
            if mem_post.touched_by_write_or_grow {
                let resolve_bound =
                    |b: &mut B, expr: SliceBoundExpr| -> Result<B::Term, SieveError> {
                        match expr {
                            SliceBoundExpr::Const(c) => Ok(b.bv_const(32, c as u64)),
                            SliceBoundExpr::Param(vid) => param_syms
                                .iter()
                                .find(|(id, _)| *id == vid)
                                .map(|(_, sv)| sv.term.clone())
                                .ok_or_else(|| {
                                    SieveError::EncodingError(format!(
                                        "SliceFrame references unknown param ValId({})",
                                        vid.0
                                    ))
                                }),
                        }
                    };
                let base32 = resolve_bound(b, sf.base)?;
                let len32 = resolve_bound(b, sf.len)?;
                let w = b.fresh_bv(&format!("{query_prefix}_slice_w_mem_{}", sf.mem.0), 32);
                let w64 = b.bv_zext(32, 32, &w);
                let b64 = b.bv_zext(32, 32, &base32);
                let l64 = b.bv_zext(32, 32, &len32);
                let end64 = b.bv_add(64, &b64, &l64);

                let ge_base = b.bv_uge(64, &w64, &b64);
                let lt_end = b.bv_ult(64, &w64, &end64);
                let in_allowed = b.and(&ge_base, &lt_end);
                let outside_allowed = SymBool::symbolic(b.not(&in_allowed));

                let in_init_mem = SymBool::symbolic(b.bv_ult(64, &w64, &mem_post.init_bytes));
                let in_live = if let Some(ref active_sr) = active_stack
                    && active_sr.stack_mem == sf.mem
                {
                    let ge_sp = SymBool::symbolic(b.bv_uge(32, &w, &active_sr.sp_in.term));
                    in_init_mem.and(b, &ge_sp)
                } else {
                    in_init_mem
                };
                let untouched = in_live.and(b, &outside_allowed);

                let pre_byte = b.array_select(&mem_post.init_array, &w);
                let post_byte = eval_mem_byte(b, mem_post, &w);
                let byte_eq = b.eq(&pre_byte, &post_byte);
                let byte_changed = SymBool::symbolic(b.not(&byte_eq));
                let clobbered = untouched.and(b, &byte_changed);

                let size_unchanged = SymBool::symbolic(b.eq(&mem_post.bytes, &mem_post.init_bytes));
                let no_clobber = clobbered.not(b);
                let slice_ok = size_unchanged.and(b, &no_clobber);
                post_ok = post_ok.and(b, &slice_ok);

                let active_clobber = entry_clean.and(b, &clobbered);
                slice_witness = Some((sf.mem, w, active_clobber.term));
            }
        }
    }

    let holds = if contract.check_trap_free {
        entry_clean.and(b, &post_ok)
    } else {
        // Explicit inline `gnomon_assert(0)` violations must NEVER be masked by `check_trap_free: false`.
        let no_assert_fail = entry_state.assert_failed.not(b);
        let partial_ok = entry_clean.implies(b, &post_ok);
        no_assert_fail.and(b, &partial_ok)
    };
    let violated = holds.not(b);

    let mem_extractions: Vec<MemExtraction<'_, B::Term>> = entry_state
        .mems
        .iter()
        .filter_map(|(&id, mem)| {
            let witness = slice_witness
                .as_ref()
                .filter(|(wid, _, _)| *wid == id)
                .map(|(_, w_term, cond_term)| (w_term.clone(), cond_term.clone()));
            if witness.is_some() || !mem.read_addrs.borrow().is_empty() {
                Some(MemExtraction { id, mem, witness })
            } else {
                None
            }
        })
        .collect();

    if let Some(ref rc) = uf_table {
        let tbl = rc.borrow();
        if tbl.overflow {
            return Ok(SmtResult::Unknown("uf call cap exceeded".into()));
        }
        tbl.assert_congruence_axioms(b)?;
    }

    solve_with_overflow_guard(
        b,
        &violated.term,
        &overflow,
        entry_state.budget.is_exceeded(),
        &param_syms,
        &global_syms,
        &mem_extractions,
    )
}
