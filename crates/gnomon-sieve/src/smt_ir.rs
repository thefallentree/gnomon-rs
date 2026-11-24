//! Shared `GnomonIR` -> `QF_ABVFP` symbolic execution and verification condition encoder.

use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use gnomon_kernel::{
    BinOp, CallTarget, EffectOp, FuncId, GlobalId, HostContract, LaneKind, MAX_CALL_DEPTH,
    MAX_WASM_PAGES, MemId, MemWidth, Module, Op, Region, RegionNode, RegionRef, SliceBound, Span,
    Stmt, StratumId, StratumRegistry, TrapCode, UnOp, Val, ValId, ValType, VcObligation,
    WASM_PAGE_SIZE, fp, validate_read_only_with_registry,
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
            .map(|(r, &ty)| sym_val(
                ty,
                b.fresh_bv(&format!("{}_uf_{}_{}_{}", self.prefix, sid.0, cid, r), bits_of(ty)),
            ))
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

/// IEEE-754 rounding modes used in `QF_ABVFP` SMT terms.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FpRm {
    /// Round to nearest, ties to even (`RNE`).
    Rne,
    /// Round toward +infinity (`RTP` / `ceil`).
    Rtp,
    /// Round toward -infinity (`RTN` / `floor`).
    Rtn,
    /// Round toward zero (`RTZ` / `trunc`).
    Rtz,
}

impl FpRm {
    pub(crate) const fn smt2(self) -> &'static str {
        match self {
            Self::Rne => "RNE",
            Self::Rtp => "RTP",
            Self::Rtn => "RTN",
            Self::Rtz => "RTZ",
        }
    }
}

/// Abstract `QF_ABVFP` term builder and solver backend implemented by both the
/// native `bitwuzla` API backend and the persistent SMT-LIB2 pipe backend.
pub(crate) trait SmtTarget {
    type Term: Clone + PartialEq;

    fn cmp_term(&self, a: &Self::Term, b: &Self::Term) -> std::cmp::Ordering;

    fn bool_const(&mut self, v: bool) -> Self::Term;
    fn bv_const(&mut self, bits: u8, v: u64) -> Self::Term;
    fn bv_const_u128(&mut self, bits: u8, v: u128) -> Self::Term;
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
    fn bv_not(&mut self, bits: u8, a: &Self::Term) -> Self::Term;
    fn bv_neg(&mut self, bits: u8, a: &Self::Term) -> Self::Term;

    fn bv_to_fp(&mut self, eb: u8, sb: u8, bv: &Self::Term) -> Self::Term;
    fn fp_to_bv_canon(
        &mut self,
        eb: u8,
        sb: u8,
        canon_nan_bv: u64,
        fp: &Self::Term,
    ) -> Result<Self::Term, SieveError>;
    fn fp_add(&mut self, eb: u8, sb: u8, rm: FpRm, a: &Self::Term, b: &Self::Term) -> Self::Term;
    fn fp_sub(&mut self, eb: u8, sb: u8, rm: FpRm, a: &Self::Term, b: &Self::Term) -> Self::Term;
    fn fp_mul(&mut self, eb: u8, sb: u8, rm: FpRm, a: &Self::Term, b: &Self::Term) -> Self::Term;
    fn fp_div(&mut self, eb: u8, sb: u8, rm: FpRm, a: &Self::Term, b: &Self::Term) -> Self::Term;
    fn fp_sqrt(&mut self, eb: u8, sb: u8, rm: FpRm, a: &Self::Term) -> Self::Term;
    fn fp_rti(&mut self, eb: u8, sb: u8, rm: FpRm, a: &Self::Term) -> Self::Term;
    fn fp_eq(&mut self, a: &Self::Term, b: &Self::Term) -> Self::Term;
    fn fp_lt(&mut self, a: &Self::Term, b: &Self::Term) -> Self::Term;
    fn fp_le(&mut self, a: &Self::Term, b: &Self::Term) -> Self::Term;
    fn fp_gt(&mut self, a: &Self::Term, b: &Self::Term) -> Self::Term;
    fn fp_ge(&mut self, a: &Self::Term, b: &Self::Term) -> Self::Term;
    fn fp_is_nan(&mut self, a: &Self::Term) -> Self::Term;
    fn fp_is_zero(&mut self, a: &Self::Term) -> Self::Term;
    fn fp_is_neg(&mut self, a: &Self::Term) -> Self::Term;
    #[allow(dead_code)]
    fn fp_is_pos(&mut self, a: &Self::Term) -> Self::Term;
    #[allow(dead_code)]
    fn fp_is_inf(&mut self, a: &Self::Term) -> Self::Term;
    fn fp_from_sbv(&mut self, eb: u8, sb: u8, rm: FpRm, bv: &Self::Term) -> Self::Term;
    fn fp_from_ubv(&mut self, eb: u8, sb: u8, rm: FpRm, bv: &Self::Term) -> Self::Term;
    fn fp_to_sbv(&mut self, bits: u8, rm: FpRm, fp: &Self::Term) -> Self::Term;
    fn fp_to_ubv(&mut self, bits: u8, rm: FpRm, fp: &Self::Term) -> Self::Term;
    fn fp_to_fp(&mut self, eb: u8, sb: u8, rm: FpRm, fp: &Self::Term) -> Self::Term;

    fn assert_formula(&mut self, cond: &Self::Term) -> Result<(), SieveError>;
    fn push(&mut self) -> Result<(), SieveError>;
    fn pop(&mut self) -> Result<(), SieveError>;
    fn check_sat(&mut self) -> Result<RawSat, SieveError>;
    fn get_bv_u64(&mut self, term: &Self::Term, bits: u8) -> Result<u64, SieveError>;
    fn get_bv_u128(&mut self, term: &Self::Term, bits: u8) -> Result<u128, SieveError>;
    fn get_bool(&mut self, term: &Self::Term) -> Result<bool, SieveError>;
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum RawSat {
    Unsat,
    Sat,
    Unknown(String),
}

/// Per-lane view for 4x32-bit `V128` vectors.
///
/// Invariants:
/// - `term` is always a 32-bit BV term.
/// - When `mask_cond == Some(c)`, `term` is bit-identical to `ite(c, 0xFFFF_FFFF, 0)`.
/// - When `add_terms == Some(ts)`, `term` is equal mod `2^32` to the sum of `ts`.
#[derive(Clone, Debug)]
struct Lane32<T> {
    term: T,
    mask_cond: Option<T>,
    add_terms: Option<Vec<T>>,
}

impl<T> Lane32<T> {
    fn plain(term: T) -> Self {
        Self { term, mask_cond: None, add_terms: None }
    }
}

/// Bit-vector term paired with an optional statically folded constant value and
/// exact structural views (`lanes32`, `bool01`, `add_terms`) for term sharing.
///
/// Representation at the `SymVal` boundary:
/// - `I32` -> `BV32` (two's-complement bits)
/// - `I64` -> `BV64` (two's-complement bits)
/// - `F32` -> `BV32` (raw IEEE-754 binary32 bits)
/// - `F64` -> `BV64` (raw IEEE-754 binary64 bits)
/// - `V128` -> `BV128` (little-endian lane-packed bits)
#[derive(Clone, Debug)]
struct SymVal<T> {
    ty: ValType,
    term: T,
    konst: Option<u128>,
    /// Optional 4x32-bit lane view for `ValType::V128` (always `None` for scalar types).
    /// When `Some([l0, l1, l2, l3])`, `term` is bit-identical to `concat(l3, l2, l1, l0)`.
    lanes32: Option<[Lane32<T>; 4]>,
    /// When `Some(c)` (only for `ValType::I32`), `term` is bit-identical to `ite(c, 1, 0)`.
    bool01: Option<T>,
    /// Optional flattened associative-commutative `bv_add` summands for `I32`/`I64`.
    add_terms: Option<Vec<T>>,
}

const MAX_ADD_FLATTEN_TERMS: usize = 32;

fn sym_val<T>(ty: ValType, term: T) -> SymVal<T> {
    SymVal { ty, term, konst: None, lanes32: None, bool01: None, add_terms: None }
}

fn bool01_sym_val<T>(term: T, cond: T) -> SymVal<T> {
    SymVal {
        ty: ValType::I32,
        term,
        konst: None,
        lanes32: None,
        bool01: Some(cond),
        add_terms: None,
    }
}

fn zero_sym_val<B: SmtTarget>(b: &mut B, ty: ValType) -> SymVal<B::Term> {
    const_sym_val(b, ty, 0)
}

fn const_sym_val<B: SmtTarget>(b: &mut B, ty: ValType, raw: u128) -> SymVal<B::Term> {
    let masked = mask_for_ty(ty, raw);
    let lanes32 = if ty == ValType::V128 {
        Some([
            Lane32::plain(b.bv_const(32, (masked as u32) as u64)),
            Lane32::plain(b.bv_const(32, ((masked >> 32) as u32) as u64)),
            Lane32::plain(b.bv_const(32, ((masked >> 64) as u32) as u64)),
            Lane32::plain(b.bv_const(32, ((masked >> 96) as u32) as u64)),
        ])
    } else {
        None
    };
    SymVal {
        ty,
        term: b.bv_const_u128(bits_of(ty), masked),
        konst: Some(masked),
        lanes32,
        bool01: None,
        add_terms: None,
    }
}

fn canon_and<B: SmtTarget>(b: &mut B, a: &B::Term, c: &B::Term) -> B::Term {
    if a == c {
        a.clone()
    } else if b.cmp_term(a, c) == std::cmp::Ordering::Greater {
        b.and(c, a)
    } else {
        b.and(a, c)
    }
}

fn canon_or<B: SmtTarget>(b: &mut B, a: &B::Term, c: &B::Term) -> B::Term {
    if a == c {
        a.clone()
    } else if b.cmp_term(a, c) == std::cmp::Ordering::Greater {
        b.or(c, a)
    } else {
        b.or(a, c)
    }
}

fn canon_bv_add<B: SmtTarget>(
    b: &mut B,
    bits: u8,
    lhs_term: &B::Term,
    lhs_adds: Option<&[B::Term]>,
    rhs_term: &B::Term,
    rhs_adds: Option<&[B::Term]>,
) -> (B::Term, Option<Vec<B::Term>>) {
    let l_len = lhs_adds.map_or(1, <[B::Term]>::len);
    let r_len = rhs_adds.map_or(1, <[B::Term]>::len);
    if l_len + r_len > MAX_ADD_FLATTEN_TERMS {
        return (b.bv_add(bits, lhs_term, rhs_term), None);
    }
    let mut terms = Vec::with_capacity(l_len + r_len);
    match lhs_adds {
        Some(s) => terms.extend(s.iter().cloned()),
        None => terms.push(lhs_term.clone()),
    }
    match rhs_adds {
        Some(s) => terms.extend(s.iter().cloned()),
        None => terms.push(rhs_term.clone()),
    }
    terms.sort_by(|x, y| b.cmp_term(x, y));
    let mut acc = terms[0].clone();
    for t in terms.iter().skip(1) {
        acc = b.bv_add(bits, &acc, t);
    }
    (acc, Some(terms))
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
        ValType::I32 | ValType::F32 => 32,
        ValType::I64 | ValType::F64 => 64,
        ValType::V128 => 128,
    }
}

fn mask_for_ty(ty: ValType, v: u128) -> u128 {
    match ty {
        ValType::I32 | ValType::F32 => (v as u32) as u128,
        ValType::I64 | ValType::F64 => (v as u64) as u128,
        ValType::V128 => v,
    }
}

fn val_to_sym_val<B: SmtTarget>(b: &mut B, val: Val) -> SymVal<B::Term> {
    match val {
        Val::I32(v) => const_sym_val(b, ValType::I32, (v as u32) as u128),
        Val::I64(v) => const_sym_val(b, ValType::I64, (v as u64) as u128),
        Val::F32(bits) => const_sym_val(b, ValType::F32, bits as u128),
        Val::F64(bits) => const_sym_val(b, ValType::F64, bits as u128),
        Val::V128(bits) => const_sym_val(b, ValType::V128, bits),
    }
}

#[derive(Clone)]
struct MemSym<T> {
    init_array: T,
    array: T,
    init_bytes: T,
    pages: T,
    bytes: T,
    min_pages: u64,
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
    prefix: Rc<String>,
    fresh_counter: Rc<Cell<u32>>,
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

fn vec_to_arr4<T>(v: Vec<T>) -> [T; 4] {
    let mut it = v.into_iter();
    let a0 = it.next().expect("4 lanes");
    let a1 = it.next().expect("4 lanes");
    let a2 = it.next().expect("4 lanes");
    let a3 = it.next().expect("4 lanes");
    [a0, a1, a2, a3]
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
            if t.term == f.term {
                return Ok(SymVal {
                    ty: t.ty,
                    term: t.term.clone(),
                    konst: t.konst.or(f.konst),
                    lanes32: t.lanes32.clone().or_else(|| f.lanes32.clone()),
                    bool01: t.bool01.clone().or_else(|| f.bool01.clone()),
                    add_terms: t.add_terms.clone().or_else(|| f.add_terms.clone()),
                });
            }
            let konst = match (t.konst, f.konst) {
                (Some(a), Some(c)) if a == c => Some(a),
                _ => None,
            };
            let lanes32 = match (&t.lanes32, &f.lanes32) {
                (Some(tl), Some(fl)) => {
                    let mut merged: Vec<Lane32<B::Term>> = Vec::with_capacity(4);
                    for i in 0..4 {
                        if tl[i].term == fl[i].term {
                            merged.push(tl[i].clone());
                        } else {
                            merged.push(Lane32::plain(b.ite(&cond.term, &tl[i].term, &fl[i].term)));
                        }
                    }
                    Some(vec_to_arr4(merged))
                }
                _ => None,
            };
            let term = if let Some(ref lanes) = lanes32 {
                let lo64 = b.bv_concat(32, 32, &lanes[1].term, &lanes[0].term);
                let hi64 = b.bv_concat(32, 32, &lanes[3].term, &lanes[2].term);
                b.bv_concat(64, 64, &hi64, &lo64)
            } else {
                b.ite(&cond.term, &t.term, &f.term)
            };
            let bool01 = if t.ty == ValType::I32 && t.konst == Some(1) && f.konst == Some(0) {
                Some(cond.term.clone())
            } else {
                None
            };
            SymVal { ty: t.ty, term, konst, lanes32, bool01, add_terms: None }
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
                    min_pages: m.min_pages as u64,
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
                sym_val(g.ty, term)
            } else {
                val_to_sym_val(b, g.init)
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
            prefix: Rc::new(prefix.to_string()),
            fresh_counter: Rc::new(Cell::new(0)),
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
        let id = self.fresh_counter.get();
        self.fresh_counter.set(id + 1);
        format!("{}_sym_{tag}_{id}", self.prefix)
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
        if let Some(ref c) = v.bool01 {
            return SymBool::symbolic(c.clone());
        }
        let zero = b.bv_const_u128(bits_of(v.ty), 0);
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

/// Computes the 32-bit byte address `(base + offset + i) mod 2^32`, constant-folding
/// whenever `base.konst` is known and combining `offset + i` into a single addition so
/// `Load(B16, base, off)` byte `4*k + j` is term-identical to `Load(B4, base, off + 4*k)` byte `j`.
fn mem_byte_idx<B: SmtTarget>(
    b: &mut B,
    base: &SymVal<B::Term>,
    offset: u32,
    i: u32,
) -> B::Term {
    let total_off = offset.wrapping_add(i);
    if let Some(a_c) = base.konst {
        b.bv_const(32, (a_c as u32).wrapping_add(total_off) as u64)
    } else if total_off == 0 {
        base.term.clone()
    } else {
        let off32 = b.bv_const(32, total_off as u64);
        b.bv_add(32, &base.term, &off32)
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
    let ea_const_u64 = addr.konst.map(|a_c| (a_c as u32 as u64) + (offset as u64));
    let oob_sym = if let (Some(ea_c), Some(l_c)) = (ea_const_u64, len_const) {
        let sum = ea_c.saturating_add(l_c);
        let min_bytes = mem.min_pages.saturating_mul(WASM_PAGE_SIZE as u64);
        let max_bytes = mem.max_pages.saturating_mul(WASM_PAGE_SIZE as u64);
        if sum > max_bytes {
            SymBool::from_const(b, true)
        } else if sum <= min_bytes {
            SymBool::from_const(b, false)
        } else {
            let end64 = b.bv_const(64, sum);
            let in_bounds = b.bv_ule(64, &end64, &mem.bytes);
            SymBool::symbolic(b.not(&in_bounds))
        }
    } else {
        let ea64 = match ea_const_u64 {
            Some(ea) => b.bv_const(64, ea),
            None => {
                let addr64 = b.bv_zext(32, 32, &addr.term);
                if offset == 0 {
                    addr64
                } else {
                    let off64 = b.bv_const(64, offset as u64);
                    b.bv_add(64, &addr64, &off64)
                }
            }
        };
        let end64 = b.bv_add(64, &ea64, len_term);
        let in_bounds = b.bv_ule(64, &end64, &mem.bytes);
        SymBool::symbolic(b.not(&in_bounds))
    };
    state.trap_if(b, &oob_sym, TrapCode::OutOfBoundsMem);
    let ea32 = mem_byte_idx(b, addr, offset, 0);
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

const F32_EB: u8 = 8;
const F32_SB: u8 = 24;
const F64_EB: u8 = 11;
const F64_SB: u8 = 53;

const F32_SIGN_MASK: u64 = 0x8000_0000;
const F32_MAG_MASK: u64 = 0x7fff_ffff;
const F64_SIGN_MASK: u64 = 0x8000_0000_0000_0000;
const F64_MAG_MASK: u64 = 0x7fff_ffff_ffff_ffff;

/// Exact bijection `FP -> BV` preserving `-0.0` vs `+0.0` (via structural SMT `=`)
/// while enforcing Wasm canonical quiet NaN (`0x7fc0_0000` / `0x7ff8_0000_0000_0000`).
/// Delegates to the backend's hash-consed `SmtTarget::fp_to_bv_canon` so identical
/// FP terms across LHS/RHS share one BV representative.
fn fp_to_bv_canon<B: SmtTarget>(
    b: &mut B,
    _state: &mut ExecState<B::Term>,
    eb: u8,
    sb: u8,
    canon_nan_bv: u64,
    fp_term: &B::Term,
) -> Result<B::Term, SieveError> {
    b.fp_to_bv_canon(eb, sb, canon_nan_bv, fp_term)
}

#[derive(Clone, Copy)]
struct TruncSpec {
    eb: u8,
    sb: u8,
    in_bits: u8,
    out_bits: u8,
    signed: bool,
    min_bound_bits: u64,
    min_inclusive: bool,
    max_excl_bits: u64,
}

const TRUNC_I32_F32_S: TruncSpec = TruncSpec {
    eb: F32_EB,
    sb: F32_SB,
    in_bits: 32,
    out_bits: 32,
    signed: true,
    min_bound_bits: (-2147483648.0f32).to_bits() as u64,
    min_inclusive: true,
    max_excl_bits: (2147483648.0f32).to_bits() as u64,
};
const TRUNC_I32_F32_U: TruncSpec = TruncSpec {
    eb: F32_EB,
    sb: F32_SB,
    in_bits: 32,
    out_bits: 32,
    signed: false,
    min_bound_bits: (-1.0f32).to_bits() as u64,
    min_inclusive: false,
    max_excl_bits: (4294967296.0f32).to_bits() as u64,
};
const TRUNC_I32_F64_S: TruncSpec = TruncSpec {
    eb: F64_EB,
    sb: F64_SB,
    in_bits: 64,
    out_bits: 32,
    signed: true,
    min_bound_bits: (-2147483649.0f64).to_bits(),
    min_inclusive: false,
    max_excl_bits: (2147483648.0f64).to_bits(),
};
const TRUNC_I32_F64_U: TruncSpec = TruncSpec {
    eb: F64_EB,
    sb: F64_SB,
    in_bits: 64,
    out_bits: 32,
    signed: false,
    min_bound_bits: (-1.0f64).to_bits(),
    min_inclusive: false,
    max_excl_bits: (4294967296.0f64).to_bits(),
};
const TRUNC_I64_F32_S: TruncSpec = TruncSpec {
    eb: F32_EB,
    sb: F32_SB,
    in_bits: 32,
    out_bits: 64,
    signed: true,
    min_bound_bits: (-9223372036854775808.0f32).to_bits() as u64,
    min_inclusive: true,
    max_excl_bits: (9223372036854775808.0f32).to_bits() as u64,
};
const TRUNC_I64_F32_U: TruncSpec = TruncSpec {
    eb: F32_EB,
    sb: F32_SB,
    in_bits: 32,
    out_bits: 64,
    signed: false,
    min_bound_bits: (-1.0f32).to_bits() as u64,
    min_inclusive: false,
    max_excl_bits: (18446744073709551616.0f32).to_bits() as u64,
};
const TRUNC_I64_F64_S: TruncSpec = TruncSpec {
    eb: F64_EB,
    sb: F64_SB,
    in_bits: 64,
    out_bits: 64,
    signed: true,
    min_bound_bits: (-9223372036854775808.0f64).to_bits(),
    min_inclusive: true,
    max_excl_bits: (9223372036854775808.0f64).to_bits(),
};
const TRUNC_I64_F64_U: TruncSpec = TruncSpec {
    eb: F64_EB,
    sb: F64_SB,
    in_bits: 64,
    out_bits: 64,
    signed: false,
    min_bound_bits: (-1.0f64).to_bits(),
    min_inclusive: false,
    max_excl_bits: (18446744073709551616.0f64).to_bits(),
};

/// Guarded `fp.to_sbv`/`fp.to_ubv` encoding exact Wasm trapping `trunc` and trap-free `trunc_sat`.
fn eval_fp_trunc_bv<B: SmtTarget>(
    b: &mut B,
    state: &mut ExecState<B::Term>,
    x_bv: &B::Term,
    spec: TruncSpec,
    saturating: bool,
) -> B::Term {
    let fp_x = b.bv_to_fp(spec.eb, spec.sb, x_bv);
    let min_bv = b.bv_const(spec.in_bits, spec.min_bound_bits);
    let min_fp = b.bv_to_fp(spec.eb, spec.sb, &min_bv);
    let max_bv = b.bv_const(spec.in_bits, spec.max_excl_bits);
    let max_fp = b.bv_to_fp(spec.eb, spec.sb, &max_bv);

    let lo_ok = if spec.min_inclusive { b.fp_ge(&fp_x, &min_fp) } else { b.fp_gt(&fp_x, &min_fp) };
    let hi_ok = b.fp_lt(&fp_x, &max_fp);
    let in_range = b.and(&lo_ok, &hi_ok);

    let raw = if spec.signed {
        b.fp_to_sbv(spec.out_bits, FpRm::Rtz, &fp_x)
    } else {
        b.fp_to_ubv(spec.out_bits, FpRm::Rtz, &fp_x)
    };
    let zero = b.bv_const(spec.out_bits, 0);

    if !saturating {
        let bad = SymBool::symbolic(b.not(&in_range));
        state.trap_if(b, &bad, TrapCode::IntOverflow);
        b.ite(&in_range, &raw, &zero)
    } else {
        let is_nan = b.fp_is_nan(&fp_x);
        let is_neg = b.fp_is_neg(&fp_x);
        let (sat_min_u, sat_max_u) = match (spec.out_bits, spec.signed) {
            (32, true) => ((i32::MIN as u32) as u64, i32::MAX as u64),
            (32, false) => (0u64, u32::MAX as u64),
            (64, true) => (i64::MIN as u64, i64::MAX as u64),
            (_, false) => (0u64, u64::MAX),
            _ => unreachable!(),
        };
        let sat_min = b.bv_const(spec.out_bits, sat_min_u);
        let sat_max = b.bv_const(spec.out_bits, sat_max_u);
        let clamped = b.ite(&is_neg, &sat_min, &sat_max);
        let non_nan = b.ite(&in_range, &raw, &clamped);
        b.ite(&is_nan, &zero, &non_nan)
    }
}

/// Exact Wasm `f*.min` / `f*.max` (NEVER raw SMT `fp.min`/`fp.max`!):
/// - Either NaN -> canonical quiet NaN.
/// - Both zero -> `min` picks `-0.0` if either negative (`a_bv | b_bv`); `max` picks `+0.0` if either positive (`a_bv & b_bv`).
/// - Otherwise `a < b ? a_bv : b_bv` (for `min`) or `a > b ? a_bv : b_bv` (for `max`).
fn eval_fp_min_max_bv<B: SmtTarget>(
    b: &mut B,
    eb: u8,
    sb: u8,
    canon_nan_bv: u64,
    is_min: bool,
    a_bv: &B::Term,
    b_bv: &B::Term,
) -> B::Term {
    let bits = eb + sb;
    let a_fp = b.bv_to_fp(eb, sb, a_bv);
    let b_fp = b.bv_to_fp(eb, sb, b_bv);
    let a_nan = b.fp_is_nan(&a_fp);
    let b_nan = b.fp_is_nan(&b_fp);
    let either_nan = b.or(&a_nan, &b_nan);
    let a_zero = b.fp_is_zero(&a_fp);
    let b_zero = b.fp_is_zero(&b_fp);
    let both_zero = b.and(&a_zero, &b_zero);

    let ord_cond = if is_min { b.fp_lt(&a_fp, &b_fp) } else { b.fp_gt(&a_fp, &b_fp) };
    let ord_pick = b.ite(&ord_cond, a_bv, b_bv);
    let zero_pick = if is_min { b.bv_or(bits, a_bv, b_bv) } else { b.bv_and(bits, a_bv, b_bv) };
    let non_nan = b.ite(&both_zero, &zero_pick, &ord_pick);
    let nan_c = b.bv_const(bits, canon_nan_bv);
    b.ite(&either_nan, &nan_c, &non_nan)
}

/// Exact Wasm SIMD `pmin` / `pmax`:
/// - `pmin(a, b) = ite(fp.lt(b, a), b_bv, a_bv)`
/// - `pmax(a, b) = ite(fp.lt(a, b), b_bv, a_bv)`
///
/// Preserves operand bit patterns verbatim (no NaN canonicalization).
fn eval_fp_pmin_pmax_bv<B: SmtTarget>(
    b: &mut B,
    eb: u8,
    sb: u8,
    is_pmin: bool,
    a_bv: &B::Term,
    b_bv: &B::Term,
) -> B::Term {
    let a_fp = b.bv_to_fp(eb, sb, a_bv);
    let b_fp = b.bv_to_fp(eb, sb, b_bv);
    let take_b = if is_pmin { b.fp_lt(&b_fp, &a_fp) } else { b.fp_lt(&a_fp, &b_fp) };
    b.ite(&take_b, b_bv, a_bv)
}

fn eval_fp_unop_bv<B: SmtTarget>(
    b: &mut B,
    state: &mut ExecState<B::Term>,
    eb: u8,
    sb: u8,
    canon_nan: u64,
    x_bv: &B::Term,
    kind: FpUnaryKind,
) -> Result<B::Term, SieveError> {
    let bits = eb + sb;
    let sign_mask = if bits == 32 { F32_SIGN_MASK } else { F64_SIGN_MASK };
    let mag_mask = if bits == 32 { F32_MAG_MASK } else { F64_MAG_MASK };
    match kind {
        FpUnaryKind::Abs => {
            let m = b.bv_const(bits, mag_mask);
            Ok(b.bv_and(bits, x_bv, &m))
        }
        FpUnaryKind::Neg => {
            let m = b.bv_const(bits, sign_mask);
            Ok(b.bv_xor(bits, x_bv, &m))
        }
        FpUnaryKind::Rti(rm) => {
            let fp_x = b.bv_to_fp(eb, sb, x_bv);
            let r = b.fp_rti(eb, sb, rm, &fp_x);
            fp_to_bv_canon(b, state, eb, sb, canon_nan, &r)
        }
        FpUnaryKind::Sqrt => {
            let fp_x = b.bv_to_fp(eb, sb, x_bv);
            let r = b.fp_sqrt(eb, sb, FpRm::Rne, &fp_x);
            fp_to_bv_canon(b, state, eb, sb, canon_nan, &r)
        }
    }
}

#[derive(Clone, Copy)]
enum FpUnaryKind {
    Abs,
    Neg,
    Rti(FpRm),
    Sqrt,
}

fn unpack_lanes<B: SmtTarget>(b: &mut B, vec: &B::Term, lane_bits: u8, num_lanes: usize) -> Vec<B::Term> {
    let w = lane_bits as u32;
    (0..num_lanes)
        .map(|i| {
            let lo = (i as u32) * w;
            b.bv_extract(lo + w - 1, lo, vec)
        })
        .collect()
}

fn pack_lanes<B: SmtTarget>(b: &mut B, lanes: &[B::Term], lane_bits: u8) -> B::Term {
    debug_assert!(!lanes.is_empty());
    let mut acc = lanes[0].clone();
    let mut lo_bits = lane_bits;
    for lane in lanes.iter().skip(1) {
        acc = b.bv_concat(lane_bits, lo_bits, lane, &acc);
        lo_bits = lo_bits.saturating_add(lane_bits);
    }
    acc
}

fn extract_lane32_info<B: SmtTarget>(b: &mut B, vec: &SymVal<B::Term>, lane: usize) -> Lane32<B::Term> {
    debug_assert!(vec.ty == ValType::V128 && lane < 4);
    if let Some(ref lanes) = vec.lanes32 {
        return lanes[lane].clone();
    }
    let lo = (lane as u32) * 32;
    Lane32::plain(b.bv_extract(lo + 31, lo, &vec.term))
}

fn extract_lane32<B: SmtTarget>(b: &mut B, vec: &SymVal<B::Term>, lane: usize) -> B::Term {
    extract_lane32_info(b, vec, lane).term
}

fn extract_lanes32<B: SmtTarget>(b: &mut B, vec: &SymVal<B::Term>) -> [Lane32<B::Term>; 4] {
    debug_assert!(vec.ty == ValType::V128);
    if let Some(ref lanes) = vec.lanes32 {
        return lanes.clone();
    }
    [
        Lane32::plain(b.bv_extract(31, 0, &vec.term)),
        Lane32::plain(b.bv_extract(63, 32, &vec.term)),
        Lane32::plain(b.bv_extract(95, 64, &vec.term)),
        Lane32::plain(b.bv_extract(127, 96, &vec.term)),
    ]
}

fn pack_lanes32<B: SmtTarget>(b: &mut B, lanes: [Lane32<B::Term>; 4]) -> SymVal<B::Term> {
    let lo64 = b.bv_concat(32, 32, &lanes[1].term, &lanes[0].term);
    let hi64 = b.bv_concat(32, 32, &lanes[3].term, &lanes[2].term);
    let term = b.bv_concat(64, 64, &hi64, &lo64);
    SymVal {
        ty: ValType::V128,
        term,
        konst: None,
        lanes32: Some(lanes),
        bool01: None,
        add_terms: None,
    }
}

fn pack_plain_lanes32<B: SmtTarget>(b: &mut B, lanes: [B::Term; 4]) -> SymVal<B::Term> {
    let [l0, l1, l2, l3] = lanes;
    pack_lanes32(b, [Lane32::plain(l0), Lane32::plain(l1), Lane32::plain(l2), Lane32::plain(l3)])
}

fn map_lanes32_rich<B: SmtTarget, F>(
    b: &mut B,
    vec: &SymVal<B::Term>,
    mut f: F,
) -> Result<SymVal<B::Term>, SieveError>
where
    F: FnMut(&mut B, &Lane32<B::Term>) -> Result<Lane32<B::Term>, SieveError>,
{
    let in_lanes = extract_lanes32(b, vec);
    let mut out_lanes: Vec<Lane32<B::Term>> = Vec::with_capacity(4);
    for i in 0..4 {
        if let Some(prev) = (0..i).find(|&j| in_lanes[j].term == in_lanes[i].term) {
            out_lanes.push(out_lanes[prev].clone());
        } else {
            out_lanes.push(f(b, &in_lanes[i])?);
        }
    }
    Ok(pack_lanes32(b, vec_to_arr4(out_lanes)))
}

fn map_lanes32<B: SmtTarget, F>(
    b: &mut B,
    vec: &SymVal<B::Term>,
    mut f: F,
) -> Result<SymVal<B::Term>, SieveError>
where
    F: FnMut(&mut B, &B::Term) -> Result<B::Term, SieveError>,
{
    map_lanes32_rich(b, vec, |b, l| Ok(Lane32::plain(f(b, &l.term)?)))
}

fn zip_lanes32_rich<B: SmtTarget, F>(
    b: &mut B,
    lhs: &SymVal<B::Term>,
    rhs: &SymVal<B::Term>,
    mut f: F,
) -> Result<SymVal<B::Term>, SieveError>
where
    F: FnMut(&mut B, &Lane32<B::Term>, &Lane32<B::Term>) -> Result<Lane32<B::Term>, SieveError>,
{
    let a_lanes = extract_lanes32(b, lhs);
    let c_lanes = extract_lanes32(b, rhs);
    let mut out_lanes: Vec<Lane32<B::Term>> = Vec::with_capacity(4);
    for i in 0..4 {
        if let Some(prev) =
            (0..i).find(|&j| a_lanes[j].term == a_lanes[i].term && c_lanes[j].term == c_lanes[i].term)
        {
            out_lanes.push(out_lanes[prev].clone());
        } else {
            out_lanes.push(f(b, &a_lanes[i], &c_lanes[i])?);
        }
    }
    Ok(pack_lanes32(b, vec_to_arr4(out_lanes)))
}

fn zip_lanes32<B: SmtTarget, F>(
    b: &mut B,
    lhs: &SymVal<B::Term>,
    rhs: &SymVal<B::Term>,
    mut f: F,
) -> Result<SymVal<B::Term>, SieveError>
where
    F: FnMut(&mut B, &B::Term, &B::Term) -> Result<B::Term, SieveError>,
{
    zip_lanes32_rich(b, lhs, rhs, |b, a, c| Ok(Lane32::plain(f(b, &a.term, &c.term)?)))
}

fn zip_lanes32_cmp<B: SmtTarget, F>(
    b: &mut B,
    lhs: &SymVal<B::Term>,
    rhs: &SymVal<B::Term>,
    mut f: F,
) -> Result<SymVal<B::Term>, SieveError>
where
    F: FnMut(&mut B, &B::Term, &B::Term) -> B::Term,
{
    let all1 = b.bv_const(32, u32::MAX as u64);
    let zero = b.bv_const(32, 0);
    zip_lanes32_rich(b, lhs, rhs, |b, a, c| {
        let cond = f(b, &a.term, &c.term);
        let term = b.ite(&cond, &all1, &zero);
        Ok(Lane32 { term, mask_cond: Some(cond), add_terms: None })
    })
}

fn map_lanes_bv<B: SmtTarget, F>(
    b: &mut B,
    vec: &B::Term,
    lane_bits: u8,
    num_lanes: usize,
    mut f: F,
) -> Result<B::Term, SieveError>
where
    F: FnMut(&mut B, &B::Term) -> Result<B::Term, SieveError>,
{
    let in_lanes = unpack_lanes(b, vec, lane_bits, num_lanes);
    let mut out_lanes: Vec<B::Term> = Vec::with_capacity(num_lanes);
    for i in 0..num_lanes {
        if let Some(prev) = (0..i).find(|&j| in_lanes[j] == in_lanes[i]) {
            out_lanes.push(out_lanes[prev].clone());
        } else {
            out_lanes.push(f(b, &in_lanes[i])?);
        }
    }
    Ok(pack_lanes(b, &out_lanes, lane_bits))
}

fn zip_lanes_bv<B: SmtTarget, F>(
    b: &mut B,
    lhs: &B::Term,
    rhs: &B::Term,
    lane_bits: u8,
    num_lanes: usize,
    mut f: F,
) -> Result<B::Term, SieveError>
where
    F: FnMut(&mut B, &B::Term, &B::Term) -> Result<B::Term, SieveError>,
{
    let a_lanes = unpack_lanes(b, lhs, lane_bits, num_lanes);
    let c_lanes = unpack_lanes(b, rhs, lane_bits, num_lanes);
    let mut out_lanes: Vec<B::Term> = Vec::with_capacity(num_lanes);
    for i in 0..num_lanes {
        if let Some(prev) = (0..i).find(|&j| a_lanes[j] == a_lanes[i] && c_lanes[j] == c_lanes[i]) {
            out_lanes.push(out_lanes[prev].clone());
        } else {
            out_lanes.push(f(b, &a_lanes[i], &c_lanes[i])?);
        }
    }
    Ok(pack_lanes(b, &out_lanes, lane_bits))
}

fn eval_unop_const(op: UnOp, k: u128) -> Result<u128, TrapCode> {
    use UnOp::*;
    let b32 = k as u32;
    let b64 = k as u64;
    Ok(match op {
        I32Eqz => u128::from(b32 == 0),
        I64Eqz => u128::from(b64 == 0),
        I32Clz => b32.leading_zeros() as u128,
        I32Ctz => b32.trailing_zeros() as u128,
        I32Popcnt => b32.count_ones() as u128,
        I64Clz => b64.leading_zeros() as u128,
        I64Ctz => b64.trailing_zeros() as u128,
        I64Popcnt => b64.count_ones() as u128,
        I32WrapI64 => (b64 as u32) as u128,
        I64ExtendI32S => ((b32 as i32) as i64 as u64) as u128,
        I64ExtendI32U => b32 as u128,
        I32Extend8S => (((b32 as i8) as i32) as u32) as u128,
        I32Extend16S => (((b32 as i16) as i32) as u32) as u128,
        I64Extend8S => ((b64 as i8) as i64 as u64) as u128,
        I64Extend16S => ((b64 as i16) as i64 as u64) as u128,
        I64Extend32S => ((b64 as i32) as i64 as u64) as u128,
        // Scalar FP unary
        F32Abs => fp::f32_abs(b32) as u128,
        F32Neg => fp::f32_neg(b32) as u128,
        F32Ceil => fp::f32_ceil(b32) as u128,
        F32Floor => fp::f32_floor(b32) as u128,
        F32Trunc => fp::f32_trunc(b32) as u128,
        F32Nearest => fp::f32_nearest(b32) as u128,
        F32Sqrt => fp::f32_sqrt(b32) as u128,
        F64Abs => fp::f64_abs(b64) as u128,
        F64Neg => fp::f64_neg(b64) as u128,
        F64Ceil => fp::f64_ceil(b64) as u128,
        F64Floor => fp::f64_floor(b64) as u128,
        F64Trunc => fp::f64_trunc(b64) as u128,
        F64Nearest => fp::f64_nearest(b64) as u128,
        F64Sqrt => fp::f64_sqrt(b64) as u128,
        // Trapping truncations
        I32TruncF32S => (fp::i32_trunc_f32_s(b32)? as u32) as u128,
        I32TruncF32U => (fp::i32_trunc_f32_u(b32)? as u32) as u128,
        I32TruncF64S => (fp::i32_trunc_f64_s(b64)? as u32) as u128,
        I32TruncF64U => (fp::i32_trunc_f64_u(b64)? as u32) as u128,
        I64TruncF32S => (fp::i64_trunc_f32_s(b32)? as u64) as u128,
        I64TruncF32U => (fp::i64_trunc_f32_u(b32)? as u64) as u128,
        I64TruncF64S => (fp::i64_trunc_f64_s(b64)? as u64) as u128,
        I64TruncF64U => (fp::i64_trunc_f64_u(b64)? as u64) as u128,
        // Saturating truncations
        I32TruncSatF32S => (fp::i32_trunc_sat_f32_s(b32) as u32) as u128,
        I32TruncSatF32U => (fp::i32_trunc_sat_f32_u(b32) as u32) as u128,
        I32TruncSatF64S => (fp::i32_trunc_sat_f64_s(b64) as u32) as u128,
        I32TruncSatF64U => (fp::i32_trunc_sat_f64_u(b64) as u32) as u128,
        I64TruncSatF32S => (fp::i64_trunc_sat_f32_s(b32) as u64) as u128,
        I64TruncSatF32U => (fp::i64_trunc_sat_f32_u(b32) as u64) as u128,
        I64TruncSatF64S => (fp::i64_trunc_sat_f64_s(b64) as u64) as u128,
        I64TruncSatF64U => (fp::i64_trunc_sat_f64_u(b64) as u64) as u128,
        // Int-to-float conversions
        F32ConvertI32S => ((b32 as i32) as f32).to_bits() as u128,
        F32ConvertI32U => (b32 as f32).to_bits() as u128,
        F32ConvertI64S => ((b64 as i64) as f32).to_bits() as u128,
        F32ConvertI64U => (b64 as f32).to_bits() as u128,
        F64ConvertI32S => ((b32 as i32) as f64).to_bits() as u128,
        F64ConvertI32U => (b32 as f64).to_bits() as u128,
        F64ConvertI64S => ((b64 as i64) as f64).to_bits() as u128,
        F64ConvertI64U => (b64 as f64).to_bits() as u128,
        // Demote / Promote / Reinterpret
        F32DemoteF64 => fp::f32_demote_f64(b64) as u128,
        F64PromoteF32 => fp::f64_promote_f32(b32) as u128,
        I32ReinterpretF32 | F32ReinterpretI32 => b32 as u128,
        I64ReinterpretF64 | F64ReinterpretI64 => b64 as u128,
        // v128 unary
        V128Not => !k,
        V128AnyTrue => u128::from(k != 0),
        I8x16Splat => fp::splat_u8(b32 as u8),
        I16x8Splat => fp::splat_u16(b32 as u16),
        I32x4Splat | F32x4Splat => fp::splat_u32(b32),
        I64x2Splat | F64x2Splat => fp::splat_u64(b64),
        I8x16Bitmask => (fp::i8x16_bitmask(k) as u32) as u128,
        I16x8Bitmask => (fp::i16x8_bitmask(k) as u32) as u128,
        I32x4Bitmask => (fp::i32x4_bitmask(k) as u32) as u128,
        I64x2Bitmask => (fp::i64x2_bitmask(k) as u32) as u128,
        I32x4AllTrue => {
            let a = fp::unpack_u32x4(k);
            u128::from(a[0] != 0 && a[1] != 0 && a[2] != 0 && a[3] != 0)
        }
        I64x2AllTrue => {
            let a = fp::unpack_u64x2(k);
            u128::from(a[0] != 0 && a[1] != 0)
        }
        I32x4Abs => fp::map_u32x4(k, |l| (l as i32).wrapping_abs() as u32),
        I32x4Neg => fp::map_u32x4(k, |l| (l as i32).wrapping_neg() as u32),
        I64x2Abs => fp::map_u64x2(k, |l| (l as i64).wrapping_abs() as u64),
        I64x2Neg => fp::map_u64x2(k, |l| (l as i64).wrapping_neg() as u64),
        F32x4Abs => fp::map_u32x4(k, fp::f32_abs),
        F32x4Neg => fp::map_u32x4(k, fp::f32_neg),
        F32x4Sqrt => fp::map_u32x4(k, fp::f32_sqrt),
        F32x4Ceil => fp::map_u32x4(k, fp::f32_ceil),
        F32x4Floor => fp::map_u32x4(k, fp::f32_floor),
        F32x4Trunc => fp::map_u32x4(k, fp::f32_trunc),
        F32x4Nearest => fp::map_u32x4(k, fp::f32_nearest),
        F64x2Abs => fp::map_u64x2(k, fp::f64_abs),
        F64x2Neg => fp::map_u64x2(k, fp::f64_neg),
        F64x2Sqrt => fp::map_u64x2(k, fp::f64_sqrt),
        F64x2Ceil => fp::map_u64x2(k, fp::f64_ceil),
        F64x2Floor => fp::map_u64x2(k, fp::f64_floor),
        F64x2Trunc => fp::map_u64x2(k, fp::f64_trunc),
        F64x2Nearest => fp::map_u64x2(k, fp::f64_nearest),
        I32x4TruncSatF32x4S => fp::map_u32x4(k, |l| fp::i32_trunc_sat_f32_s(l) as u32),
        I32x4TruncSatF32x4U => fp::map_u32x4(k, |l| fp::i32_trunc_sat_f32_u(l) as u32),
        F32x4ConvertI32x4S => fp::map_u32x4(k, |l| ((l as i32) as f32).to_bits()),
        F32x4ConvertI32x4U => fp::map_u32x4(k, |l| (l as f32).to_bits()),
        I64x2ExtendLowI32x4S => {
            let a = fp::unpack_u32x4(k);
            fp::pack_u64x2([(a[0] as i32) as i64 as u64, (a[1] as i32) as i64 as u64])
        }
        I64x2ExtendLowI32x4U => {
            let a = fp::unpack_u32x4(k);
            fp::pack_u64x2([a[0] as u64, a[1] as u64])
        }
        I64x2ExtendHighI32x4S => {
            let a = fp::unpack_u32x4(k);
            fp::pack_u64x2([(a[2] as i32) as i64 as u64, (a[3] as i32) as i64 as u64])
        }
        I64x2ExtendHighI32x4U => {
            let a = fp::unpack_u32x4(k);
            fp::pack_u64x2([a[2] as u64, a[3] as u64])
        }
    })
}

fn eval_unop<B: SmtTarget>(
    b: &mut B,
    state: &mut ExecState<B::Term>,
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
        return match eval_unop_const(op, k) {
            Ok(v) => Ok(const_sym_val(b, out_ty, v)),
            Err(code) => {
                let t = SymBool::from_const(b, true);
                state.trap_if(b, &t, code);
                Ok(zero_sym_val(b, out_ty))
            }
        };
    }

    let term = match op {
        UnOp::I32Eqz => {
            let z = b.bv_const(32, 0);
            let cond = match &arg.bool01 {
                Some(c) => b.not(c),
                None => b.eq(&arg.term, &z),
            };
            let one = b.bv_const(32, 1);
            let term = b.ite(&cond, &one, &z);
            return Ok(bool01_sym_val(term, cond));
        }
        UnOp::I64Eqz => {
            let z64 = b.bv_const(64, 0);
            let cond = b.eq(&arg.term, &z64);
            let one = b.bv_const(32, 1);
            let z32 = b.bv_const(32, 0);
            let term = b.ite(&cond, &one, &z32);
            return Ok(bool01_sym_val(term, cond));
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
        // Scalar FP unary
        UnOp::F32Abs => eval_fp_unop_bv(b, state, F32_EB, F32_SB, fp::F32_CANON_NAN as u64, &arg.term, FpUnaryKind::Abs)?,
        UnOp::F32Neg => eval_fp_unop_bv(b, state, F32_EB, F32_SB, fp::F32_CANON_NAN as u64, &arg.term, FpUnaryKind::Neg)?,
        UnOp::F32Ceil => eval_fp_unop_bv(b, state, F32_EB, F32_SB, fp::F32_CANON_NAN as u64, &arg.term, FpUnaryKind::Rti(FpRm::Rtp))?,
        UnOp::F32Floor => eval_fp_unop_bv(b, state, F32_EB, F32_SB, fp::F32_CANON_NAN as u64, &arg.term, FpUnaryKind::Rti(FpRm::Rtn))?,
        UnOp::F32Trunc => eval_fp_unop_bv(b, state, F32_EB, F32_SB, fp::F32_CANON_NAN as u64, &arg.term, FpUnaryKind::Rti(FpRm::Rtz))?,
        UnOp::F32Nearest => eval_fp_unop_bv(b, state, F32_EB, F32_SB, fp::F32_CANON_NAN as u64, &arg.term, FpUnaryKind::Rti(FpRm::Rne))?,
        UnOp::F32Sqrt => eval_fp_unop_bv(b, state, F32_EB, F32_SB, fp::F32_CANON_NAN as u64, &arg.term, FpUnaryKind::Sqrt)?,
        UnOp::F64Abs => eval_fp_unop_bv(b, state, F64_EB, F64_SB, fp::F64_CANON_NAN, &arg.term, FpUnaryKind::Abs)?,
        UnOp::F64Neg => eval_fp_unop_bv(b, state, F64_EB, F64_SB, fp::F64_CANON_NAN, &arg.term, FpUnaryKind::Neg)?,
        UnOp::F64Ceil => eval_fp_unop_bv(b, state, F64_EB, F64_SB, fp::F64_CANON_NAN, &arg.term, FpUnaryKind::Rti(FpRm::Rtp))?,
        UnOp::F64Floor => eval_fp_unop_bv(b, state, F64_EB, F64_SB, fp::F64_CANON_NAN, &arg.term, FpUnaryKind::Rti(FpRm::Rtn))?,
        UnOp::F64Trunc => eval_fp_unop_bv(b, state, F64_EB, F64_SB, fp::F64_CANON_NAN, &arg.term, FpUnaryKind::Rti(FpRm::Rtz))?,
        UnOp::F64Nearest => eval_fp_unop_bv(b, state, F64_EB, F64_SB, fp::F64_CANON_NAN, &arg.term, FpUnaryKind::Rti(FpRm::Rne))?,
        UnOp::F64Sqrt => eval_fp_unop_bv(b, state, F64_EB, F64_SB, fp::F64_CANON_NAN, &arg.term, FpUnaryKind::Sqrt)?,
        // Trapping float-to-int truncations
        UnOp::I32TruncF32S => eval_fp_trunc_bv(b, state, &arg.term, TRUNC_I32_F32_S, false),
        UnOp::I32TruncF32U => eval_fp_trunc_bv(b, state, &arg.term, TRUNC_I32_F32_U, false),
        UnOp::I32TruncF64S => eval_fp_trunc_bv(b, state, &arg.term, TRUNC_I32_F64_S, false),
        UnOp::I32TruncF64U => eval_fp_trunc_bv(b, state, &arg.term, TRUNC_I32_F64_U, false),
        UnOp::I64TruncF32S => eval_fp_trunc_bv(b, state, &arg.term, TRUNC_I64_F32_S, false),
        UnOp::I64TruncF32U => eval_fp_trunc_bv(b, state, &arg.term, TRUNC_I64_F32_U, false),
        UnOp::I64TruncF64S => eval_fp_trunc_bv(b, state, &arg.term, TRUNC_I64_F64_S, false),
        UnOp::I64TruncF64U => eval_fp_trunc_bv(b, state, &arg.term, TRUNC_I64_F64_U, false),
        // Saturating float-to-int truncations
        UnOp::I32TruncSatF32S => eval_fp_trunc_bv(b, state, &arg.term, TRUNC_I32_F32_S, true),
        UnOp::I32TruncSatF32U => eval_fp_trunc_bv(b, state, &arg.term, TRUNC_I32_F32_U, true),
        UnOp::I32TruncSatF64S => eval_fp_trunc_bv(b, state, &arg.term, TRUNC_I32_F64_S, true),
        UnOp::I32TruncSatF64U => eval_fp_trunc_bv(b, state, &arg.term, TRUNC_I32_F64_U, true),
        UnOp::I64TruncSatF32S => eval_fp_trunc_bv(b, state, &arg.term, TRUNC_I64_F32_S, true),
        UnOp::I64TruncSatF32U => eval_fp_trunc_bv(b, state, &arg.term, TRUNC_I64_F32_U, true),
        UnOp::I64TruncSatF64S => eval_fp_trunc_bv(b, state, &arg.term, TRUNC_I64_F64_S, true),
        UnOp::I64TruncSatF64U => eval_fp_trunc_bv(b, state, &arg.term, TRUNC_I64_F64_U, true),
        // Int-to-float conversions
        UnOp::F32ConvertI32S | UnOp::F32ConvertI64S => {
            let f = b.fp_from_sbv(F32_EB, F32_SB, FpRm::Rne, &arg.term);
            fp_to_bv_canon(b, state, F32_EB, F32_SB, fp::F32_CANON_NAN as u64, &f)?
        }
        UnOp::F32ConvertI32U | UnOp::F32ConvertI64U => {
            let f = b.fp_from_ubv(F32_EB, F32_SB, FpRm::Rne, &arg.term);
            fp_to_bv_canon(b, state, F32_EB, F32_SB, fp::F32_CANON_NAN as u64, &f)?
        }
        UnOp::F64ConvertI32S | UnOp::F64ConvertI64S => {
            let f = b.fp_from_sbv(F64_EB, F64_SB, FpRm::Rne, &arg.term);
            fp_to_bv_canon(b, state, F64_EB, F64_SB, fp::F64_CANON_NAN, &f)?
        }
        UnOp::F64ConvertI32U | UnOp::F64ConvertI64U => {
            let f = b.fp_from_ubv(F64_EB, F64_SB, FpRm::Rne, &arg.term);
            fp_to_bv_canon(b, state, F64_EB, F64_SB, fp::F64_CANON_NAN, &f)?
        }
        // Demote / Promote / Reinterpret
        UnOp::F32DemoteF64 => {
            let f64_t = b.bv_to_fp(F64_EB, F64_SB, &arg.term);
            let f32_t = b.fp_to_fp(F32_EB, F32_SB, FpRm::Rne, &f64_t);
            fp_to_bv_canon(b, state, F32_EB, F32_SB, fp::F32_CANON_NAN as u64, &f32_t)?
        }
        UnOp::F64PromoteF32 => {
            let f32_t = b.bv_to_fp(F32_EB, F32_SB, &arg.term);
            let f64_t = b.fp_to_fp(F64_EB, F64_SB, FpRm::Rne, &f32_t);
            fp_to_bv_canon(b, state, F64_EB, F64_SB, fp::F64_CANON_NAN, &f64_t)?
        }
        UnOp::I32ReinterpretF32
        | UnOp::I64ReinterpretF64
        | UnOp::F32ReinterpretI32
        | UnOp::F64ReinterpretI64 => arg.term.clone(),
        // v128 unary / splat / bitmask / lane ops
        UnOp::V128Not => {
            if arg.lanes32.is_some() {
                let all1 = b.bv_const(32, u32::MAX as u64);
                let zero = b.bv_const(32, 0);
                return map_lanes32_rich(b, arg, |b, l| {
                    if let Some(ref c) = l.mask_cond {
                        let nc = b.not(c);
                        let term = b.ite(&nc, &all1, &zero);
                        Ok(Lane32 { term, mask_cond: Some(nc), add_terms: None })
                    } else {
                        Ok(Lane32::plain(b.bv_not(32, &l.term)))
                    }
                });
            }
            b.bv_not(128, &arg.term)
        }
        UnOp::V128AnyTrue => {
            let z128 = b.bv_const_u128(128, 0);
            let eq_z = b.eq(&arg.term, &z128);
            let cond = b.not(&eq_z);
            let zero32 = b.bv_const(32, 0);
            let one32 = b.bv_const(32, 1);
            let term = b.ite(&cond, &one32, &zero32);
            return Ok(bool01_sym_val(term, cond));
        }
        UnOp::I8x16Splat => {
            let b8 = b.bv_extract(7, 0, &arg.term);
            let b16 = b.bv_concat(8, 8, &b8, &b8);
            let b32 = b.bv_concat(16, 16, &b16, &b16);
            return Ok(pack_plain_lanes32(b, [b32.clone(), b32.clone(), b32.clone(), b32]));
        }
        UnOp::I16x8Splat => {
            let b16 = b.bv_extract(15, 0, &arg.term);
            let b32 = b.bv_concat(16, 16, &b16, &b16);
            return Ok(pack_plain_lanes32(b, [b32.clone(), b32.clone(), b32.clone(), b32]));
        }
        UnOp::I32x4Splat | UnOp::F32x4Splat => {
            let l = Lane32 {
                term: arg.term.clone(),
                mask_cond: None,
                add_terms: if arg.ty == ValType::I32 { arg.add_terms.clone() } else { None },
            };
            return Ok(pack_lanes32(b, [l.clone(), l.clone(), l.clone(), l]));
        }
        UnOp::I64x2Splat | UnOp::F64x2Splat => b.bv_concat(64, 64, &arg.term, &arg.term),
        UnOp::I8x16Bitmask => {
            let bits: Vec<B::Term> = (0..16u32).map(|i| b.bv_extract(i * 8 + 7, i * 8 + 7, &arg.term)).collect();
            let packed = pack_lanes(b, &bits, 1);
            b.bv_zext(16, 16, &packed)
        }
        UnOp::I16x8Bitmask => {
            let bits: Vec<B::Term> = (0..8u32).map(|i| b.bv_extract(i * 16 + 15, i * 16 + 15, &arg.term)).collect();
            let packed = pack_lanes(b, &bits, 1);
            b.bv_zext(8, 24, &packed)
        }
        UnOp::I32x4Bitmask => {
            let bits: Vec<B::Term> = if let Some(ref lanes) = arg.lanes32 {
                let one1 = b.bv_const(1, 1);
                let zero1 = b.bv_const(1, 0);
                lanes
                    .iter()
                    .map(|l| match &l.mask_cond {
                        Some(c) => b.ite(c, &one1, &zero1),
                        None => b.bv_extract(31, 31, &l.term),
                    })
                    .collect()
            } else {
                (0..4u32).map(|i| b.bv_extract(i * 32 + 31, i * 32 + 31, &arg.term)).collect()
            };
            let packed = pack_lanes(b, &bits, 1);
            b.bv_zext(4, 28, &packed)
        }
        UnOp::I64x2Bitmask => {
            let b0 = b.bv_extract(63, 63, &arg.term);
            let b1 = b.bv_extract(127, 127, &arg.term);
            let packed = b.bv_concat(1, 1, &b1, &b0);
            b.bv_zext(2, 30, &packed)
        }
        UnOp::I32x4AllTrue => {
            let lanes = extract_lanes32(b, arg);
            let zero32 = b.bv_const(32, 0);
            let mut all_nz = b.bool_const(true);
            for l in &lanes {
                let nz = match &l.mask_cond {
                    Some(c) => c.clone(),
                    None => {
                        let eq = b.eq(&l.term, &zero32);
                        b.not(&eq)
                    }
                };
                all_nz = b.and(&all_nz, &nz);
            }
            let one32 = b.bv_const(32, 1);
            let term = b.ite(&all_nz, &one32, &zero32);
            return Ok(bool01_sym_val(term, all_nz));
        }
        UnOp::I64x2AllTrue => {
            let lanes = unpack_lanes(b, &arg.term, 64, 2);
            let zero64 = b.bv_const(64, 0);
            let eq0 = b.eq(&lanes[0], &zero64);
            let eq1 = b.eq(&lanes[1], &zero64);
            let nz0 = b.not(&eq0);
            let nz1 = b.not(&eq1);
            let all_nz = b.and(&nz0, &nz1);
            let one32 = b.bv_const(32, 1);
            let zero32 = b.bv_const(32, 0);
            let term = b.ite(&all_nz, &one32, &zero32);
            return Ok(bool01_sym_val(term, all_nz));
        }
        UnOp::I32x4Abs => {
            return map_lanes32(b, arg, |b, l| {
                let z = b.bv_const(32, 0);
                let neg = b.bv_neg(32, l);
                let is_neg = b.bv_slt(32, l, &z);
                Ok(b.ite(&is_neg, &neg, l))
            });
        }
        UnOp::I32x4Neg => return map_lanes32(b, arg, |b, l| Ok(b.bv_neg(32, l))),
        UnOp::I64x2Abs => map_lanes_bv(b, &arg.term, 64, 2, |b, l| {
            let z = b.bv_const(64, 0);
            let neg = b.bv_neg(64, l);
            let is_neg = b.bv_slt(64, l, &z);
            Ok(b.ite(&is_neg, &neg, l))
        })?,
        UnOp::I64x2Neg => map_lanes_bv(b, &arg.term, 64, 2, |b, l| Ok(b.bv_neg(64, l)))?,
        UnOp::F32x4Abs => {
            return map_lanes32(b, arg, |b, l| {
                eval_fp_unop_bv(b, state, F32_EB, F32_SB, fp::F32_CANON_NAN as u64, l, FpUnaryKind::Abs)
            });
        }
        UnOp::F32x4Neg => {
            return map_lanes32(b, arg, |b, l| {
                eval_fp_unop_bv(b, state, F32_EB, F32_SB, fp::F32_CANON_NAN as u64, l, FpUnaryKind::Neg)
            });
        }
        UnOp::F32x4Sqrt => {
            return map_lanes32(b, arg, |b, l| {
                eval_fp_unop_bv(b, state, F32_EB, F32_SB, fp::F32_CANON_NAN as u64, l, FpUnaryKind::Sqrt)
            });
        }
        UnOp::F32x4Ceil => {
            return map_lanes32(b, arg, |b, l| {
                eval_fp_unop_bv(b, state, F32_EB, F32_SB, fp::F32_CANON_NAN as u64, l, FpUnaryKind::Rti(FpRm::Rtp))
            });
        }
        UnOp::F32x4Floor => {
            return map_lanes32(b, arg, |b, l| {
                eval_fp_unop_bv(b, state, F32_EB, F32_SB, fp::F32_CANON_NAN as u64, l, FpUnaryKind::Rti(FpRm::Rtn))
            });
        }
        UnOp::F32x4Trunc => {
            return map_lanes32(b, arg, |b, l| {
                eval_fp_unop_bv(b, state, F32_EB, F32_SB, fp::F32_CANON_NAN as u64, l, FpUnaryKind::Rti(FpRm::Rtz))
            });
        }
        UnOp::F32x4Nearest => {
            return map_lanes32(b, arg, |b, l| {
                eval_fp_unop_bv(b, state, F32_EB, F32_SB, fp::F32_CANON_NAN as u64, l, FpUnaryKind::Rti(FpRm::Rne))
            });
        }
        UnOp::F64x2Abs => map_lanes_bv(b, &arg.term, 64, 2, |b, l| {
            eval_fp_unop_bv(b, state, F64_EB, F64_SB, fp::F64_CANON_NAN, l, FpUnaryKind::Abs)
        })?,
        UnOp::F64x2Neg => map_lanes_bv(b, &arg.term, 64, 2, |b, l| {
            eval_fp_unop_bv(b, state, F64_EB, F64_SB, fp::F64_CANON_NAN, l, FpUnaryKind::Neg)
        })?,
        UnOp::F64x2Sqrt => map_lanes_bv(b, &arg.term, 64, 2, |b, l| {
            eval_fp_unop_bv(b, state, F64_EB, F64_SB, fp::F64_CANON_NAN, l, FpUnaryKind::Sqrt)
        })?,
        UnOp::F64x2Ceil => map_lanes_bv(b, &arg.term, 64, 2, |b, l| {
            eval_fp_unop_bv(b, state, F64_EB, F64_SB, fp::F64_CANON_NAN, l, FpUnaryKind::Rti(FpRm::Rtp))
        })?,
        UnOp::F64x2Floor => map_lanes_bv(b, &arg.term, 64, 2, |b, l| {
            eval_fp_unop_bv(b, state, F64_EB, F64_SB, fp::F64_CANON_NAN, l, FpUnaryKind::Rti(FpRm::Rtn))
        })?,
        UnOp::F64x2Trunc => map_lanes_bv(b, &arg.term, 64, 2, |b, l| {
            eval_fp_unop_bv(b, state, F64_EB, F64_SB, fp::F64_CANON_NAN, l, FpUnaryKind::Rti(FpRm::Rtz))
        })?,
        UnOp::F64x2Nearest => map_lanes_bv(b, &arg.term, 64, 2, |b, l| {
            eval_fp_unop_bv(b, state, F64_EB, F64_SB, fp::F64_CANON_NAN, l, FpUnaryKind::Rti(FpRm::Rne))
        })?,
        UnOp::I32x4TruncSatF32x4S => {
            return map_lanes32(b, arg, |b, l| {
                Ok(eval_fp_trunc_bv(b, state, l, TRUNC_I32_F32_S, true))
            });
        }
        UnOp::I32x4TruncSatF32x4U => {
            return map_lanes32(b, arg, |b, l| {
                Ok(eval_fp_trunc_bv(b, state, l, TRUNC_I32_F32_U, true))
            });
        }
        UnOp::F32x4ConvertI32x4S => {
            return map_lanes32(b, arg, |b, l| {
                let f = b.fp_from_sbv(F32_EB, F32_SB, FpRm::Rne, l);
                fp_to_bv_canon(b, state, F32_EB, F32_SB, fp::F32_CANON_NAN as u64, &f)
            });
        }
        UnOp::F32x4ConvertI32x4U => {
            return map_lanes32(b, arg, |b, l| {
                let f = b.fp_from_ubv(F32_EB, F32_SB, FpRm::Rne, l);
                fp_to_bv_canon(b, state, F32_EB, F32_SB, fp::F32_CANON_NAN as u64, &f)
            });
        }
        UnOp::I64x2ExtendLowI32x4S => {
            let l0 = extract_lane32(b, arg, 0);
            let l1 = extract_lane32(b, arg, 1);
            let e0 = b.bv_sext(32, 32, &l0);
            let e1 = b.bv_sext(32, 32, &l1);
            b.bv_concat(64, 64, &e1, &e0)
        }
        UnOp::I64x2ExtendLowI32x4U => {
            let l0 = extract_lane32(b, arg, 0);
            let l1 = extract_lane32(b, arg, 1);
            let e0 = b.bv_zext(32, 32, &l0);
            let e1 = b.bv_zext(32, 32, &l1);
            b.bv_concat(64, 64, &e1, &e0)
        }
        UnOp::I64x2ExtendHighI32x4S => {
            let l2 = extract_lane32(b, arg, 2);
            let l3 = extract_lane32(b, arg, 3);
            let e2 = b.bv_sext(32, 32, &l2);
            let e3 = b.bv_sext(32, 32, &l3);
            b.bv_concat(64, 64, &e3, &e2)
        }
        UnOp::I64x2ExtendHighI32x4U => {
            let l2 = extract_lane32(b, arg, 2);
            let l3 = extract_lane32(b, arg, 3);
            let e2 = b.bv_zext(32, 32, &l2);
            let e3 = b.bv_zext(32, 32, &l3);
            b.bv_concat(64, 64, &e3, &e2)
        }
    };
    Ok(sym_val(out_ty, term))
}

fn eval_binop_const(op: BinOp, l: u128, r: u128) -> u128 {
    use BinOp::*;
    let b32 = |c: bool| if c { u32::MAX } else { 0u32 };
    let b64 = |c: bool| if c { u64::MAX } else { 0u64 };
    let (l32, r32) = (l as u32, r as u32);
    let (li32, ri32) = (l32 as i32, r32 as i32);
    let (l64, r64) = (l as u64, r as u64);
    let (li64, ri64) = (l64 as i64, r64 as i64);
    match op {
        I32Eq => u128::from(li32 == ri32),
        I32Ne => u128::from(li32 != ri32),
        I32LtS => u128::from(li32 < ri32),
        I32LtU => u128::from(l32 < r32),
        I32GtS => u128::from(li32 > ri32),
        I32GtU => u128::from(l32 > r32),
        I32LeS => u128::from(li32 <= ri32),
        I32LeU => u128::from(l32 <= r32),
        I32GeS => u128::from(li32 >= ri32),
        I32GeU => u128::from(l32 >= r32),
        I32Add => (li32.wrapping_add(ri32) as u32) as u128,
        I32Sub => (li32.wrapping_sub(ri32) as u32) as u128,
        I32Mul => (li32.wrapping_mul(ri32) as u32) as u128,
        I32And => (l32 & r32) as u128,
        I32Or => (l32 | r32) as u128,
        I32Xor => (l32 ^ r32) as u128,
        I32Shl => (li32.wrapping_shl(r32) as u32) as u128,
        I32ShrS => (li32.wrapping_shr(r32) as u32) as u128,
        I32ShrU => l32.wrapping_shr(r32) as u128,
        I32Rotl => l32.rotate_left(r32 & 31) as u128,
        I32Rotr => l32.rotate_right(r32 & 31) as u128,
        I64Eq => u128::from(li64 == ri64),
        I64Ne => u128::from(li64 != ri64),
        I64LtS => u128::from(li64 < ri64),
        I64LtU => u128::from(l64 < r64),
        I64GtS => u128::from(li64 > ri64),
        I64GtU => u128::from(l64 > r64),
        I64LeS => u128::from(li64 <= ri64),
        I64LeU => u128::from(l64 <= r64),
        I64GeS => u128::from(li64 >= ri64),
        I64GeU => u128::from(l64 >= r64),
        I64Add => (li64.wrapping_add(ri64) as u64) as u128,
        I64Sub => (li64.wrapping_sub(ri64) as u64) as u128,
        I64Mul => (li64.wrapping_mul(ri64) as u64) as u128,
        I64And => (l64 & r64) as u128,
        I64Or => (l64 | r64) as u128,
        I64Xor => (l64 ^ r64) as u128,
        I64Shl => (li64.wrapping_shl(r64 as u32) as u64) as u128,
        I64ShrS => (li64.wrapping_shr(r64 as u32) as u64) as u128,
        I64ShrU => l64.wrapping_shr(r64 as u32) as u128,
        I64Rotl => l64.rotate_left((r64 as u32) & 63) as u128,
        I64Rotr => l64.rotate_right((r64 as u32) & 63) as u128,
        // Scalar FP
        F32Add => fp::f32_add(l32, r32) as u128,
        F32Sub => fp::f32_sub(l32, r32) as u128,
        F32Mul => fp::f32_mul(l32, r32) as u128,
        F32Div => fp::f32_div(l32, r32) as u128,
        F32Min => fp::f32_min(l32, r32) as u128,
        F32Max => fp::f32_max(l32, r32) as u128,
        F32Copysign => fp::f32_copysign(l32, r32) as u128,
        F32Eq => u128::from(fp::f32_eq(l32, r32)),
        F32Ne => u128::from(fp::f32_ne(l32, r32)),
        F32Lt => u128::from(fp::f32_lt(l32, r32)),
        F32Gt => u128::from(fp::f32_gt(l32, r32)),
        F32Le => u128::from(fp::f32_le(l32, r32)),
        F32Ge => u128::from(fp::f32_ge(l32, r32)),
        F64Add => fp::f64_add(l64, r64) as u128,
        F64Sub => fp::f64_sub(l64, r64) as u128,
        F64Mul => fp::f64_mul(l64, r64) as u128,
        F64Div => fp::f64_div(l64, r64) as u128,
        F64Min => fp::f64_min(l64, r64) as u128,
        F64Max => fp::f64_max(l64, r64) as u128,
        F64Copysign => fp::f64_copysign(l64, r64) as u128,
        F64Eq => u128::from(fp::f64_eq(l64, r64)),
        F64Ne => u128::from(fp::f64_ne(l64, r64)),
        F64Lt => u128::from(fp::f64_lt(l64, r64)),
        F64Gt => u128::from(fp::f64_gt(l64, r64)),
        F64Le => u128::from(fp::f64_le(l64, r64)),
        F64Ge => u128::from(fp::f64_ge(l64, r64)),
        // v128 bitwise & swizzle
        V128And => l & r,
        V128AndNot => l & !r,
        V128Or => l | r,
        V128Xor => l ^ r,
        I8x16Swizzle => fp::i8x16_swizzle(l, r),
        // i32x4
        I32x4Add => fp::zip_u32x4(l, r, u32::wrapping_add),
        I32x4Sub => fp::zip_u32x4(l, r, u32::wrapping_sub),
        I32x4Mul => fp::zip_u32x4(l, r, u32::wrapping_mul),
        I32x4MinS => fp::zip_u32x4(l, r, |x, y| (x as i32).min(y as i32) as u32),
        I32x4MinU => fp::zip_u32x4(l, r, u32::min),
        I32x4MaxS => fp::zip_u32x4(l, r, |x, y| (x as i32).max(y as i32) as u32),
        I32x4MaxU => fp::zip_u32x4(l, r, u32::max),
        I32x4Eq => fp::zip_u32x4(l, r, |x, y| b32(x == y)),
        I32x4Ne => fp::zip_u32x4(l, r, |x, y| b32(x != y)),
        I32x4LtS => fp::zip_u32x4(l, r, |x, y| b32((x as i32) < (y as i32))),
        I32x4LtU => fp::zip_u32x4(l, r, |x, y| b32(x < y)),
        I32x4GtS => fp::zip_u32x4(l, r, |x, y| b32((x as i32) > (y as i32))),
        I32x4GtU => fp::zip_u32x4(l, r, |x, y| b32(x > y)),
        I32x4LeS => fp::zip_u32x4(l, r, |x, y| b32((x as i32) <= (y as i32))),
        I32x4LeU => fp::zip_u32x4(l, r, |x, y| b32(x <= y)),
        I32x4GeS => fp::zip_u32x4(l, r, |x, y| b32((x as i32) >= (y as i32))),
        I32x4GeU => fp::zip_u32x4(l, r, |x, y| b32(x >= y)),
        I32x4Shl => fp::map_u32x4(l, |x| x.wrapping_shl(r32 & 31)),
        I32x4ShrS => fp::map_u32x4(l, |x| (x as i32).wrapping_shr(r32 & 31) as u32),
        I32x4ShrU => fp::map_u32x4(l, |x| x.wrapping_shr(r32 & 31)),
        // i64x2
        I64x2Add => fp::zip_u64x2(l, r, u64::wrapping_add),
        I64x2Sub => fp::zip_u64x2(l, r, u64::wrapping_sub),
        I64x2Mul => fp::zip_u64x2(l, r, u64::wrapping_mul),
        I64x2Eq => fp::zip_u64x2(l, r, |x, y| b64(x == y)),
        I64x2Ne => fp::zip_u64x2(l, r, |x, y| b64(x != y)),
        I64x2LtS => fp::zip_u64x2(l, r, |x, y| b64((x as i64) < (y as i64))),
        I64x2GtS => fp::zip_u64x2(l, r, |x, y| b64((x as i64) > (y as i64))),
        I64x2LeS => fp::zip_u64x2(l, r, |x, y| b64((x as i64) <= (y as i64))),
        I64x2GeS => fp::zip_u64x2(l, r, |x, y| b64((x as i64) >= (y as i64))),
        I64x2Shl => fp::map_u64x2(l, |x| x.wrapping_shl(r32 & 63)),
        I64x2ShrS => fp::map_u64x2(l, |x| (x as i64).wrapping_shr(r32 & 63) as u64),
        I64x2ShrU => fp::map_u64x2(l, |x| x.wrapping_shr(r32 & 63)),
        // f32x4
        F32x4Add => fp::zip_u32x4(l, r, fp::f32_add),
        F32x4Sub => fp::zip_u32x4(l, r, fp::f32_sub),
        F32x4Mul => fp::zip_u32x4(l, r, fp::f32_mul),
        F32x4Div => fp::zip_u32x4(l, r, fp::f32_div),
        F32x4Min => fp::zip_u32x4(l, r, fp::f32_min),
        F32x4Max => fp::zip_u32x4(l, r, fp::f32_max),
        F32x4PMin => fp::zip_u32x4(l, r, fp::f32_pmin),
        F32x4PMax => fp::zip_u32x4(l, r, fp::f32_pmax),
        F32x4Eq => fp::zip_u32x4(l, r, |x, y| b32(fp::f32_eq(x, y))),
        F32x4Ne => fp::zip_u32x4(l, r, |x, y| b32(fp::f32_ne(x, y))),
        F32x4Lt => fp::zip_u32x4(l, r, |x, y| b32(fp::f32_lt(x, y))),
        F32x4Gt => fp::zip_u32x4(l, r, |x, y| b32(fp::f32_gt(x, y))),
        F32x4Le => fp::zip_u32x4(l, r, |x, y| b32(fp::f32_le(x, y))),
        F32x4Ge => fp::zip_u32x4(l, r, |x, y| b32(fp::f32_ge(x, y))),
        // f64x2
        F64x2Add => fp::zip_u64x2(l, r, fp::f64_add),
        F64x2Sub => fp::zip_u64x2(l, r, fp::f64_sub),
        F64x2Mul => fp::zip_u64x2(l, r, fp::f64_mul),
        F64x2Div => fp::zip_u64x2(l, r, fp::f64_div),
        F64x2Min => fp::zip_u64x2(l, r, fp::f64_min),
        F64x2Max => fp::zip_u64x2(l, r, fp::f64_max),
        F64x2PMin => fp::zip_u64x2(l, r, fp::f64_pmin),
        F64x2PMax => fp::zip_u64x2(l, r, fp::f64_pmax),
        F64x2Eq => fp::zip_u64x2(l, r, |x, y| b64(fp::f64_eq(x, y))),
        F64x2Ne => fp::zip_u64x2(l, r, |x, y| b64(fp::f64_ne(x, y))),
        F64x2Lt => fp::zip_u64x2(l, r, |x, y| b64(fp::f64_lt(x, y))),
        F64x2Gt => fp::zip_u64x2(l, r, |x, y| b64(fp::f64_gt(x, y))),
        F64x2Le => fp::zip_u64x2(l, r, |x, y| b64(fp::f64_le(x, y))),
        F64x2Ge => fp::zip_u64x2(l, r, |x, y| b64(fp::f64_ge(x, y))),
        I32DivS | I32DivU | I32RemS | I32RemU | I64DivS | I64DivU | I64RemS | I64RemU => {
            unreachable!()
        }
    }
}

fn eval_binop<B: SmtTarget>(
    b: &mut B,
    state: &mut ExecState<B::Term>,
    op: BinOp,
    lhs: &SymVal<B::Term>,
    rhs: &SymVal<B::Term>,
) -> Result<SymVal<B::Term>, SieveError> {
    let lhs_ty = op.lhs_ty();
    let rhs_ty = op.rhs_ty();
    let out_ty = op.output_ty();
    if lhs.ty != lhs_ty || rhs.ty != rhs_ty {
        return Err(SieveError::EncodingError(format!(
            "BinOp {:?} expected ({:?}, {:?}), got ({:?}, {:?})",
            op, lhs_ty, rhs_ty, lhs.ty, rhs.ty
        )));
    }
    let bits = bits_of(lhs_ty);

    // Handle div/rem trap conditions identically to gnomon_kernel::eval.
    match op {
        BinOp::I32DivS | BinOp::I64DivS => {
            let zero = b.bv_const(bits, 0);
            let minus_one = b.bv_const(bits, if bits == 32 { 0xFFFF_FFFF } else { u64::MAX });
            let min_signed = b.bv_const(bits, if bits == 32 { 0x8000_0000 } else { 1u64 << 63 });
            let min_const: u128 = if bits == 32 { 0x8000_0000 } else { 1u128 << 63 };

            let is_zero = match rhs.konst {
                Some(r) => SymBool::from_const(b, r == 0),
                None => SymBool::symbolic(b.eq(&rhs.term, &zero)),
            };
            state.trap_if(b, &is_zero, TrapCode::DivByZero);

            let is_min = match lhs.konst {
                Some(l) => SymBool::from_const(b, l == min_const),
                None => SymBool::symbolic(b.eq(&lhs.term, &min_signed)),
            };
            let is_neg1 = match rhs.konst {
                Some(r) => SymBool::from_const(b, r == mask_for_ty(lhs_ty, u64::MAX as u128)),
                None => SymBool::symbolic(b.eq(&rhs.term, &minus_one)),
            };
            let overflow = is_min.and(b, &is_neg1);
            state.trap_if(b, &overflow, TrapCode::IntOverflow);

            if let (Some(l), Some(r)) = (lhs.konst, rhs.konst) {
                let res: u128 = if bits == 32 {
                    let (a, c) = (l as u32 as i32, r as u32 as i32);
                    if c == 0 || (a == i32::MIN && c == -1) { 0 } else { (a.wrapping_div(c) as u32) as u128 }
                } else {
                    let (a, c) = (l as u64 as i64, r as u64 as i64);
                    if c == 0 || (a == i64::MIN && c == -1) { 0 } else { (a.wrapping_div(c) as u64) as u128 }
                };
                return Ok(const_sym_val(b, out_ty, res));
            }
            let div = b.bv_sdiv(bits, &lhs.term, &rhs.term);
            let bad = is_zero.or(b, &overflow);
            let term = match bad.konst {
                Some(true) => zero,
                Some(false) => div,
                None => b.ite(&bad.term, &zero, &div),
            };
            return Ok(sym_val(out_ty, term));
        }
        BinOp::I32DivU | BinOp::I64DivU => {
            let zero = b.bv_const(bits, 0);
            let is_zero = match rhs.konst {
                Some(r) => SymBool::from_const(b, r == 0),
                None => SymBool::symbolic(b.eq(&rhs.term, &zero)),
            };
            state.trap_if(b, &is_zero, TrapCode::DivByZero);

            if let (Some(l), Some(r)) = (lhs.konst, rhs.konst) {
                let res = l.checked_div(r).map_or(0, |q| mask_for_ty(lhs_ty, q));
                return Ok(const_sym_val(b, out_ty, res));
            }
            let div = b.bv_udiv(bits, &lhs.term, &rhs.term);
            let term = match is_zero.konst {
                Some(true) => zero,
                Some(false) => div,
                None => b.ite(&is_zero.term, &zero, &div),
            };
            return Ok(sym_val(out_ty, term));
        }
        BinOp::I32RemS | BinOp::I64RemS => {
            let zero = b.bv_const(bits, 0);
            let minus_one = b.bv_const(bits, if bits == 32 { 0xFFFF_FFFF } else { u64::MAX });
            let min_signed = b.bv_const(bits, if bits == 32 { 0x8000_0000 } else { 1u64 << 63 });
            let min_const: u128 = if bits == 32 { 0x8000_0000 } else { 1u128 << 63 };

            let is_zero = match rhs.konst {
                Some(r) => SymBool::from_const(b, r == 0),
                None => SymBool::symbolic(b.eq(&rhs.term, &zero)),
            };
            state.trap_if(b, &is_zero, TrapCode::DivByZero);

            if let (Some(l), Some(r)) = (lhs.konst, rhs.konst) {
                let res: u128 = if bits == 32 {
                    let (a, c) = (l as u32 as i32, r as u32 as i32);
                    if c == 0 || (a == i32::MIN && c == -1) { 0 } else { (a.wrapping_rem(c) as u32) as u128 }
                } else {
                    let (a, c) = (l as u64 as i64, r as u64 as i64);
                    if c == 0 || (a == i64::MIN && c == -1) { 0 } else { (a.wrapping_rem(c) as u64) as u128 }
                };
                return Ok(const_sym_val(b, out_ty, res));
            }
            let is_min = match lhs.konst {
                Some(l) => SymBool::from_const(b, l == min_const),
                None => SymBool::symbolic(b.eq(&lhs.term, &min_signed)),
            };
            let is_neg1 = match rhs.konst {
                Some(r) => SymBool::from_const(b, r == mask_for_ty(lhs_ty, u64::MAX as u128)),
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
            return Ok(sym_val(out_ty, term));
        }
        BinOp::I32RemU | BinOp::I64RemU => {
            let zero = b.bv_const(bits, 0);
            let is_zero = match rhs.konst {
                Some(r) => SymBool::from_const(b, r == 0),
                None => SymBool::symbolic(b.eq(&rhs.term, &zero)),
            };
            state.trap_if(b, &is_zero, TrapCode::DivByZero);

            if let (Some(l), Some(r)) = (lhs.konst, rhs.konst) {
                let res = if r == 0 { 0 } else { mask_for_ty(lhs_ty, l % r) };
                return Ok(const_sym_val(b, out_ty, res));
            }
            let rem = b.bv_urem(bits, &lhs.term, &rhs.term);
            let term = match is_zero.konst {
                Some(true) => zero,
                Some(false) => rem,
                None => b.ite(&is_zero.term, &zero, &rem),
            };
            return Ok(sym_val(out_ty, term));
        }
        _ => {}
    }

    // Constant fold all non-trapping binary operations.
    if let (Some(l), Some(r)) = (lhs.konst, rhs.konst) {
        let v = eval_binop_const(op, l, r);
        return Ok(const_sym_val(b, out_ty, v));
    }

    let one32 = b.bv_const(32, 1);
    let zero32 = b.bv_const(32, 0);
    let bool_to_i32_val = |b: &mut B, cond: B::Term| {
        let term = b.ite(&cond, &one32, &zero32);
        bool01_sym_val(term, cond)
    };
    let bool_to_mask = |b: &mut B, w: u8, cond: B::Term| {
        let all1 = b.bv_const(w, if w == 32 { u32::MAX as u64 } else { u64::MAX });
        let z = b.bv_const(w, 0);
        b.ite(&cond, &all1, &z)
    };

    let term = match op {
        BinOp::I32Eq | BinOp::I64Eq => {
            let c = b.eq(&lhs.term, &rhs.term);
            return Ok(bool_to_i32_val(b, c));
        }
        BinOp::I32Ne | BinOp::I64Ne => {
            let eq = b.eq(&lhs.term, &rhs.term);
            let ne = b.not(&eq);
            return Ok(bool_to_i32_val(b, ne));
        }
        BinOp::I32LtS | BinOp::I64LtS => {
            let c = b.bv_slt(bits, &lhs.term, &rhs.term);
            return Ok(bool_to_i32_val(b, c));
        }
        BinOp::I32LtU | BinOp::I64LtU => {
            let c = b.bv_ult(bits, &lhs.term, &rhs.term);
            return Ok(bool_to_i32_val(b, c));
        }
        BinOp::I32GtS | BinOp::I64GtS => {
            let c = b.bv_sgt(bits, &lhs.term, &rhs.term);
            return Ok(bool_to_i32_val(b, c));
        }
        BinOp::I32GtU | BinOp::I64GtU => {
            let c = b.bv_ugt(bits, &lhs.term, &rhs.term);
            return Ok(bool_to_i32_val(b, c));
        }
        BinOp::I32LeS | BinOp::I64LeS => {
            let c = b.bv_sle(bits, &lhs.term, &rhs.term);
            return Ok(bool_to_i32_val(b, c));
        }
        BinOp::I32LeU | BinOp::I64LeU => {
            let c = b.bv_ule(bits, &lhs.term, &rhs.term);
            return Ok(bool_to_i32_val(b, c));
        }
        BinOp::I32GeS | BinOp::I64GeS => {
            let c = b.bv_sge(bits, &lhs.term, &rhs.term);
            return Ok(bool_to_i32_val(b, c));
        }
        BinOp::I32GeU | BinOp::I64GeU => {
            let c = b.bv_uge(bits, &lhs.term, &rhs.term);
            return Ok(bool_to_i32_val(b, c));
        }
        BinOp::I32Add | BinOp::I64Add => {
            if lhs.konst == Some(0) {
                return Ok(rhs.clone());
            }
            if rhs.konst == Some(0) {
                return Ok(lhs.clone());
            }
            let (term, add_terms) = canon_bv_add(
                b,
                bits,
                &lhs.term,
                lhs.add_terms.as_deref(),
                &rhs.term,
                rhs.add_terms.as_deref(),
            );
            return Ok(SymVal {
                ty: out_ty,
                term,
                konst: None,
                lanes32: None,
                bool01: None,
                add_terms,
            });
        }
        BinOp::I32Sub | BinOp::I64Sub => b.bv_sub(bits, &lhs.term, &rhs.term),
        BinOp::I32Mul | BinOp::I64Mul => b.bv_mul(bits, &lhs.term, &rhs.term),
        BinOp::I32And => {
            if let (Some(cl), Some(cr)) = (&lhs.bool01, &rhs.bool01) {
                let cond = canon_and(b, cl, cr);
                return Ok(bool_to_i32_val(b, cond));
            }
            b.bv_and(32, &lhs.term, &rhs.term)
        }
        BinOp::I64And => b.bv_and(64, &lhs.term, &rhs.term),
        BinOp::I32Or => {
            if let (Some(cl), Some(cr)) = (&lhs.bool01, &rhs.bool01) {
                let cond = canon_or(b, cl, cr);
                return Ok(bool_to_i32_val(b, cond));
            }
            b.bv_or(32, &lhs.term, &rhs.term)
        }
        BinOp::I64Or => b.bv_or(64, &lhs.term, &rhs.term),
        BinOp::I32Xor => {
            if let Some(cl) = &lhs.bool01
                && rhs.konst == Some(1)
            {
                let cond = b.not(cl);
                return Ok(bool_to_i32_val(b, cond));
            }
            if let Some(cr) = &rhs.bool01
                && lhs.konst == Some(1)
            {
                let cond = b.not(cr);
                return Ok(bool_to_i32_val(b, cond));
            }
            b.bv_xor(32, &lhs.term, &rhs.term)
        }
        BinOp::I64Xor => b.bv_xor(64, &lhs.term, &rhs.term),
        BinOp::I32Shl | BinOp::I64Shl => {
            let shift_mask = b.bv_const(bits, (bits - 1) as u64);
            let s = b.bv_and(bits, &rhs.term, &shift_mask);
            b.bv_shl(bits, &lhs.term, &s)
        }
        BinOp::I32ShrS | BinOp::I64ShrS => {
            let shift_mask = b.bv_const(bits, (bits - 1) as u64);
            let s = b.bv_and(bits, &rhs.term, &shift_mask);
            b.bv_ashr(bits, &lhs.term, &s)
        }
        BinOp::I32ShrU | BinOp::I64ShrU => {
            let shift_mask = b.bv_const(bits, (bits - 1) as u64);
            let s = b.bv_and(bits, &rhs.term, &shift_mask);
            b.bv_lshr(bits, &lhs.term, &s)
        }
        BinOp::I32Rotl | BinOp::I64Rotl => {
            let shift_mask = b.bv_const(bits, (bits - 1) as u64);
            let s = b.bv_and(bits, &rhs.term, &shift_mask);
            b.bv_rotl(bits, &lhs.term, &s)
        }
        BinOp::I32Rotr | BinOp::I64Rotr => {
            let shift_mask = b.bv_const(bits, (bits - 1) as u64);
            let s = b.bv_and(bits, &rhs.term, &shift_mask);
            b.bv_rotr(bits, &lhs.term, &s)
        }
        // Scalar FP binary
        BinOp::F32Add => {
            let af = b.bv_to_fp(F32_EB, F32_SB, &lhs.term);
            let bf = b.bv_to_fp(F32_EB, F32_SB, &rhs.term);
            let rf = b.fp_add(F32_EB, F32_SB, FpRm::Rne, &af, &bf);
            fp_to_bv_canon(b, state, F32_EB, F32_SB, fp::F32_CANON_NAN as u64, &rf)?
        }
        BinOp::F32Sub => {
            let af = b.bv_to_fp(F32_EB, F32_SB, &lhs.term);
            let bf = b.bv_to_fp(F32_EB, F32_SB, &rhs.term);
            let rf = b.fp_sub(F32_EB, F32_SB, FpRm::Rne, &af, &bf);
            fp_to_bv_canon(b, state, F32_EB, F32_SB, fp::F32_CANON_NAN as u64, &rf)?
        }
        BinOp::F32Mul => {
            let af = b.bv_to_fp(F32_EB, F32_SB, &lhs.term);
            let bf = b.bv_to_fp(F32_EB, F32_SB, &rhs.term);
            let rf = b.fp_mul(F32_EB, F32_SB, FpRm::Rne, &af, &bf);
            fp_to_bv_canon(b, state, F32_EB, F32_SB, fp::F32_CANON_NAN as u64, &rf)?
        }
        BinOp::F32Div => {
            let af = b.bv_to_fp(F32_EB, F32_SB, &lhs.term);
            let bf = b.bv_to_fp(F32_EB, F32_SB, &rhs.term);
            let rf = b.fp_div(F32_EB, F32_SB, FpRm::Rne, &af, &bf);
            fp_to_bv_canon(b, state, F32_EB, F32_SB, fp::F32_CANON_NAN as u64, &rf)?
        }
        BinOp::F32Min => eval_fp_min_max_bv(b, F32_EB, F32_SB, fp::F32_CANON_NAN as u64, true, &lhs.term, &rhs.term),
        BinOp::F32Max => eval_fp_min_max_bv(b, F32_EB, F32_SB, fp::F32_CANON_NAN as u64, false, &lhs.term, &rhs.term),
        BinOp::F32Copysign => {
            let mag_m = b.bv_const(32, F32_MAG_MASK);
            let sign_m = b.bv_const(32, F32_SIGN_MASK);
            let mag = b.bv_and(32, &lhs.term, &mag_m);
            let sign = b.bv_and(32, &rhs.term, &sign_m);
            b.bv_or(32, &mag, &sign)
        }
        BinOp::F32Eq => {
            let af = b.bv_to_fp(F32_EB, F32_SB, &lhs.term);
            let bf = b.bv_to_fp(F32_EB, F32_SB, &rhs.term);
            let c = b.fp_eq(&af, &bf);
            return Ok(bool_to_i32_val(b, c));
        }
        BinOp::F32Ne => {
            let af = b.bv_to_fp(F32_EB, F32_SB, &lhs.term);
            let bf = b.bv_to_fp(F32_EB, F32_SB, &rhs.term);
            let eq = b.fp_eq(&af, &bf);
            let ne = b.not(&eq);
            return Ok(bool_to_i32_val(b, ne));
        }
        BinOp::F32Lt => {
            let af = b.bv_to_fp(F32_EB, F32_SB, &lhs.term);
            let bf = b.bv_to_fp(F32_EB, F32_SB, &rhs.term);
            let c = b.fp_lt(&af, &bf);
            return Ok(bool_to_i32_val(b, c));
        }
        BinOp::F32Gt => {
            let af = b.bv_to_fp(F32_EB, F32_SB, &lhs.term);
            let bf = b.bv_to_fp(F32_EB, F32_SB, &rhs.term);
            let c = b.fp_gt(&af, &bf);
            return Ok(bool_to_i32_val(b, c));
        }
        BinOp::F32Le => {
            let af = b.bv_to_fp(F32_EB, F32_SB, &lhs.term);
            let bf = b.bv_to_fp(F32_EB, F32_SB, &rhs.term);
            let c = b.fp_le(&af, &bf);
            return Ok(bool_to_i32_val(b, c));
        }
        BinOp::F32Ge => {
            let af = b.bv_to_fp(F32_EB, F32_SB, &lhs.term);
            let bf = b.bv_to_fp(F32_EB, F32_SB, &rhs.term);
            let c = b.fp_ge(&af, &bf);
            return Ok(bool_to_i32_val(b, c));
        }
        BinOp::F64Add => {
            let af = b.bv_to_fp(F64_EB, F64_SB, &lhs.term);
            let bf = b.bv_to_fp(F64_EB, F64_SB, &rhs.term);
            let rf = b.fp_add(F64_EB, F64_SB, FpRm::Rne, &af, &bf);
            fp_to_bv_canon(b, state, F64_EB, F64_SB, fp::F64_CANON_NAN, &rf)?
        }
        BinOp::F64Sub => {
            let af = b.bv_to_fp(F64_EB, F64_SB, &lhs.term);
            let bf = b.bv_to_fp(F64_EB, F64_SB, &rhs.term);
            let rf = b.fp_sub(F64_EB, F64_SB, FpRm::Rne, &af, &bf);
            fp_to_bv_canon(b, state, F64_EB, F64_SB, fp::F64_CANON_NAN, &rf)?
        }
        BinOp::F64Mul => {
            let af = b.bv_to_fp(F64_EB, F64_SB, &lhs.term);
            let bf = b.bv_to_fp(F64_EB, F64_SB, &rhs.term);
            let rf = b.fp_mul(F64_EB, F64_SB, FpRm::Rne, &af, &bf);
            fp_to_bv_canon(b, state, F64_EB, F64_SB, fp::F64_CANON_NAN, &rf)?
        }
        BinOp::F64Div => {
            let af = b.bv_to_fp(F64_EB, F64_SB, &lhs.term);
            let bf = b.bv_to_fp(F64_EB, F64_SB, &rhs.term);
            let rf = b.fp_div(F64_EB, F64_SB, FpRm::Rne, &af, &bf);
            fp_to_bv_canon(b, state, F64_EB, F64_SB, fp::F64_CANON_NAN, &rf)?
        }
        BinOp::F64Min => eval_fp_min_max_bv(b, F64_EB, F64_SB, fp::F64_CANON_NAN, true, &lhs.term, &rhs.term),
        BinOp::F64Max => eval_fp_min_max_bv(b, F64_EB, F64_SB, fp::F64_CANON_NAN, false, &lhs.term, &rhs.term),
        BinOp::F64Copysign => {
            let mag_m = b.bv_const(64, F64_MAG_MASK);
            let sign_m = b.bv_const(64, F64_SIGN_MASK);
            let mag = b.bv_and(64, &lhs.term, &mag_m);
            let sign = b.bv_and(64, &rhs.term, &sign_m);
            b.bv_or(64, &mag, &sign)
        }
        BinOp::F64Eq => {
            let af = b.bv_to_fp(F64_EB, F64_SB, &lhs.term);
            let bf = b.bv_to_fp(F64_EB, F64_SB, &rhs.term);
            let c = b.fp_eq(&af, &bf);
            return Ok(bool_to_i32_val(b, c));
        }
        BinOp::F64Ne => {
            let af = b.bv_to_fp(F64_EB, F64_SB, &lhs.term);
            let bf = b.bv_to_fp(F64_EB, F64_SB, &rhs.term);
            let eq = b.fp_eq(&af, &bf);
            let ne = b.not(&eq);
            return Ok(bool_to_i32_val(b, ne));
        }
        BinOp::F64Lt => {
            let af = b.bv_to_fp(F64_EB, F64_SB, &lhs.term);
            let bf = b.bv_to_fp(F64_EB, F64_SB, &rhs.term);
            let c = b.fp_lt(&af, &bf);
            return Ok(bool_to_i32_val(b, c));
        }
        BinOp::F64Gt => {
            let af = b.bv_to_fp(F64_EB, F64_SB, &lhs.term);
            let bf = b.bv_to_fp(F64_EB, F64_SB, &rhs.term);
            let c = b.fp_gt(&af, &bf);
            return Ok(bool_to_i32_val(b, c));
        }
        BinOp::F64Le => {
            let af = b.bv_to_fp(F64_EB, F64_SB, &lhs.term);
            let bf = b.bv_to_fp(F64_EB, F64_SB, &rhs.term);
            let c = b.fp_le(&af, &bf);
            return Ok(bool_to_i32_val(b, c));
        }
        BinOp::F64Ge => {
            let af = b.bv_to_fp(F64_EB, F64_SB, &lhs.term);
            let bf = b.bv_to_fp(F64_EB, F64_SB, &rhs.term);
            let c = b.fp_ge(&af, &bf);
            return Ok(bool_to_i32_val(b, c));
        }
        // v128 bitwise & swizzle
        BinOp::V128And => {
            if lhs.lanes32.is_some() || rhs.lanes32.is_some() {
                let all1 = b.bv_const(32, u32::MAX as u64);
                let z32 = b.bv_const(32, 0);
                return zip_lanes32_rich(b, lhs, rhs, |b, a, c| match (&a.mask_cond, &c.mask_cond) {
                    (Some(ca), Some(cc)) => {
                        let cond = canon_and(b, ca, cc);
                        let term = b.ite(&cond, &all1, &z32);
                        Ok(Lane32 { term, mask_cond: Some(cond), add_terms: None })
                    }
                    (Some(ca), None) => Ok(Lane32::plain(b.ite(ca, &c.term, &z32))),
                    (None, Some(cc)) => Ok(Lane32::plain(b.ite(cc, &a.term, &z32))),
                    (None, None) => Ok(Lane32::plain(b.bv_and(32, &a.term, &c.term))),
                });
            }
            b.bv_and(128, &lhs.term, &rhs.term)
        }
        BinOp::V128AndNot => {
            if lhs.lanes32.is_some() || rhs.lanes32.is_some() {
                let all1 = b.bv_const(32, u32::MAX as u64);
                let z32 = b.bv_const(32, 0);
                return zip_lanes32_rich(b, lhs, rhs, |b, a, c| match (&a.mask_cond, &c.mask_cond) {
                    (Some(ca), Some(cc)) => {
                        let ncc = b.not(cc);
                        let cond = canon_and(b, ca, &ncc);
                        let term = b.ite(&cond, &all1, &z32);
                        Ok(Lane32 { term, mask_cond: Some(cond), add_terms: None })
                    }
                    (None, Some(cc)) => Ok(Lane32::plain(b.ite(cc, &z32, &a.term))),
                    _ => {
                        let not_c = b.bv_not(32, &c.term);
                        Ok(Lane32::plain(b.bv_and(32, &a.term, &not_c)))
                    }
                });
            }
            let not_r = b.bv_not(128, &rhs.term);
            b.bv_and(128, &lhs.term, &not_r)
        }
        BinOp::V128Or => {
            if lhs.lanes32.is_some() || rhs.lanes32.is_some() {
                let all1 = b.bv_const(32, u32::MAX as u64);
                let z32 = b.bv_const(32, 0);
                return zip_lanes32_rich(b, lhs, rhs, |b, a, c| match (&a.mask_cond, &c.mask_cond) {
                    (Some(ca), Some(cc)) => {
                        let cond = canon_or(b, ca, cc);
                        let term = b.ite(&cond, &all1, &z32);
                        Ok(Lane32 { term, mask_cond: Some(cond), add_terms: None })
                    }
                    _ => Ok(Lane32::plain(b.bv_or(32, &a.term, &c.term))),
                });
            }
            b.bv_or(128, &lhs.term, &rhs.term)
        }
        BinOp::V128Xor => {
            if lhs.lanes32.is_some() || rhs.lanes32.is_some() {
                return zip_lanes32(b, lhs, rhs, |b, a, c| Ok(b.bv_xor(32, a, c)));
            }
            b.bv_xor(128, &lhs.term, &rhs.term)
        }
        BinOp::I8x16Swizzle => {
            let a_bytes = unpack_lanes(b, &lhs.term, 8, 16);
            let s_bytes = unpack_lanes(b, &rhs.term, 8, 16);
            let zero8 = b.bv_const(8, 0);
            let mut out = Vec::with_capacity(16);
            for s_i in &s_bytes {
                let mut acc = zero8.clone();
                for (k, a_k) in a_bytes.iter().enumerate() {
                    let k_c = b.bv_const(8, k as u64);
                    let hit = b.eq(s_i, &k_c);
                    acc = b.ite(&hit, a_k, &acc);
                }
                out.push(acc);
            }
            pack_lanes(b, &out, 8)
        }
        // i32x4 lane binary
        BinOp::I32x4Add => {
            return zip_lanes32_rich(b, lhs, rhs, |b, a, c| {
                let (term, add_terms) = canon_bv_add(
                    b,
                    32,
                    &a.term,
                    a.add_terms.as_deref(),
                    &c.term,
                    c.add_terms.as_deref(),
                );
                Ok(Lane32 { term, mask_cond: None, add_terms })
            });
        }
        BinOp::I32x4Sub => return zip_lanes32(b, lhs, rhs, |b, a, c| Ok(b.bv_sub(32, a, c))),
        BinOp::I32x4Mul => return zip_lanes32(b, lhs, rhs, |b, a, c| Ok(b.bv_mul(32, a, c))),
        BinOp::I32x4MinS => {
            return zip_lanes32(b, lhs, rhs, |b, a, c| {
                let lt = b.bv_slt(32, a, c);
                Ok(b.ite(&lt, a, c))
            });
        }
        BinOp::I32x4MinU => {
            return zip_lanes32(b, lhs, rhs, |b, a, c| {
                let lt = b.bv_ult(32, a, c);
                Ok(b.ite(&lt, a, c))
            });
        }
        BinOp::I32x4MaxS => {
            return zip_lanes32(b, lhs, rhs, |b, a, c| {
                let gt = b.bv_sgt(32, a, c);
                Ok(b.ite(&gt, a, c))
            });
        }
        BinOp::I32x4MaxU => {
            return zip_lanes32(b, lhs, rhs, |b, a, c| {
                let gt = b.bv_ugt(32, a, c);
                Ok(b.ite(&gt, a, c))
            });
        }
        BinOp::I32x4Eq => return zip_lanes32_cmp(b, lhs, rhs, |b, a, c| b.eq(a, c)),
        BinOp::I32x4Ne => {
            return zip_lanes32_cmp(b, lhs, rhs, |b, a, c| {
                let eq = b.eq(a, c);
                b.not(&eq)
            });
        }
        BinOp::I32x4LtS => return zip_lanes32_cmp(b, lhs, rhs, |b, a, c| b.bv_slt(32, a, c)),
        BinOp::I32x4LtU => return zip_lanes32_cmp(b, lhs, rhs, |b, a, c| b.bv_ult(32, a, c)),
        BinOp::I32x4GtS => return zip_lanes32_cmp(b, lhs, rhs, |b, a, c| b.bv_sgt(32, a, c)),
        BinOp::I32x4GtU => return zip_lanes32_cmp(b, lhs, rhs, |b, a, c| b.bv_ugt(32, a, c)),
        BinOp::I32x4LeS => return zip_lanes32_cmp(b, lhs, rhs, |b, a, c| b.bv_sle(32, a, c)),
        BinOp::I32x4LeU => return zip_lanes32_cmp(b, lhs, rhs, |b, a, c| b.bv_ule(32, a, c)),
        BinOp::I32x4GeS => return zip_lanes32_cmp(b, lhs, rhs, |b, a, c| b.bv_sge(32, a, c)),
        BinOp::I32x4GeU => return zip_lanes32_cmp(b, lhs, rhs, |b, a, c| b.bv_uge(32, a, c)),
        BinOp::I32x4Shl => {
            let s = if let Some(k) = rhs.konst {
                b.bv_const(32, (k as u32 & 31) as u64)
            } else {
                let m31 = b.bv_const(32, 31);
                b.bv_and(32, &rhs.term, &m31)
            };
            return map_lanes32(b, lhs, |b, a| Ok(b.bv_shl(32, a, &s)));
        }
        BinOp::I32x4ShrS => {
            let s = if let Some(k) = rhs.konst {
                b.bv_const(32, (k as u32 & 31) as u64)
            } else {
                let m31 = b.bv_const(32, 31);
                b.bv_and(32, &rhs.term, &m31)
            };
            return map_lanes32(b, lhs, |b, a| Ok(b.bv_ashr(32, a, &s)));
        }
        BinOp::I32x4ShrU => {
            let s = if let Some(k) = rhs.konst {
                b.bv_const(32, (k as u32 & 31) as u64)
            } else {
                let m31 = b.bv_const(32, 31);
                b.bv_and(32, &rhs.term, &m31)
            };
            return map_lanes32(b, lhs, |b, a| Ok(b.bv_lshr(32, a, &s)));
        }
        // i64x2 lane binary
        BinOp::I64x2Add => zip_lanes_bv(b, &lhs.term, &rhs.term, 64, 2, |b, a, c| Ok(b.bv_add(64, a, c)))?,
        BinOp::I64x2Sub => zip_lanes_bv(b, &lhs.term, &rhs.term, 64, 2, |b, a, c| Ok(b.bv_sub(64, a, c)))?,
        BinOp::I64x2Mul => zip_lanes_bv(b, &lhs.term, &rhs.term, 64, 2, |b, a, c| Ok(b.bv_mul(64, a, c)))?,
        BinOp::I64x2Eq => zip_lanes_bv(b, &lhs.term, &rhs.term, 64, 2, |b, a, c| {
            let cond = b.eq(a, c);
            Ok(bool_to_mask(b, 64, cond))
        })?,
        BinOp::I64x2Ne => zip_lanes_bv(b, &lhs.term, &rhs.term, 64, 2, |b, a, c| {
            let eq = b.eq(a, c);
            let ne = b.not(&eq);
            Ok(bool_to_mask(b, 64, ne))
        })?,
        BinOp::I64x2LtS => zip_lanes_bv(b, &lhs.term, &rhs.term, 64, 2, |b, a, c| {
            let cond = b.bv_slt(64, a, c);
            Ok(bool_to_mask(b, 64, cond))
        })?,
        BinOp::I64x2GtS => zip_lanes_bv(b, &lhs.term, &rhs.term, 64, 2, |b, a, c| {
            let cond = b.bv_sgt(64, a, c);
            Ok(bool_to_mask(b, 64, cond))
        })?,
        BinOp::I64x2LeS => zip_lanes_bv(b, &lhs.term, &rhs.term, 64, 2, |b, a, c| {
            let cond = b.bv_sle(64, a, c);
            Ok(bool_to_mask(b, 64, cond))
        })?,
        BinOp::I64x2GeS => zip_lanes_bv(b, &lhs.term, &rhs.term, 64, 2, |b, a, c| {
            let cond = b.bv_sge(64, a, c);
            Ok(bool_to_mask(b, 64, cond))
        })?,
        BinOp::I64x2Shl => {
            let m63 = b.bv_const(32, 63);
            let s32 = b.bv_and(32, &rhs.term, &m63);
            let s64 = b.bv_zext(32, 32, &s32);
            map_lanes_bv(b, &lhs.term, 64, 2, |b, a| Ok(b.bv_shl(64, a, &s64)))?
        }
        BinOp::I64x2ShrS => {
            let m63 = b.bv_const(32, 63);
            let s32 = b.bv_and(32, &rhs.term, &m63);
            let s64 = b.bv_zext(32, 32, &s32);
            map_lanes_bv(b, &lhs.term, 64, 2, |b, a| Ok(b.bv_ashr(64, a, &s64)))?
        }
        BinOp::I64x2ShrU => {
            let m63 = b.bv_const(32, 63);
            let s32 = b.bv_and(32, &rhs.term, &m63);
            let s64 = b.bv_zext(32, 32, &s32);
            map_lanes_bv(b, &lhs.term, 64, 2, |b, a| Ok(b.bv_lshr(64, a, &s64)))?
        }
        // f32x4 lane binary
        BinOp::F32x4Add => {
            return zip_lanes32(b, lhs, rhs, |b, a, c| {
                let af = b.bv_to_fp(F32_EB, F32_SB, a);
                let cf = b.bv_to_fp(F32_EB, F32_SB, c);
                let rf = b.fp_add(F32_EB, F32_SB, FpRm::Rne, &af, &cf);
                fp_to_bv_canon(b, state, F32_EB, F32_SB, fp::F32_CANON_NAN as u64, &rf)
            });
        }
        BinOp::F32x4Sub => {
            return zip_lanes32(b, lhs, rhs, |b, a, c| {
                let af = b.bv_to_fp(F32_EB, F32_SB, a);
                let cf = b.bv_to_fp(F32_EB, F32_SB, c);
                let rf = b.fp_sub(F32_EB, F32_SB, FpRm::Rne, &af, &cf);
                fp_to_bv_canon(b, state, F32_EB, F32_SB, fp::F32_CANON_NAN as u64, &rf)
            });
        }
        BinOp::F32x4Mul => {
            return zip_lanes32(b, lhs, rhs, |b, a, c| {
                let af = b.bv_to_fp(F32_EB, F32_SB, a);
                let cf = b.bv_to_fp(F32_EB, F32_SB, c);
                let rf = b.fp_mul(F32_EB, F32_SB, FpRm::Rne, &af, &cf);
                fp_to_bv_canon(b, state, F32_EB, F32_SB, fp::F32_CANON_NAN as u64, &rf)
            });
        }
        BinOp::F32x4Div => {
            return zip_lanes32(b, lhs, rhs, |b, a, c| {
                let af = b.bv_to_fp(F32_EB, F32_SB, a);
                let cf = b.bv_to_fp(F32_EB, F32_SB, c);
                let rf = b.fp_div(F32_EB, F32_SB, FpRm::Rne, &af, &cf);
                fp_to_bv_canon(b, state, F32_EB, F32_SB, fp::F32_CANON_NAN as u64, &rf)
            });
        }
        BinOp::F32x4Min => {
            return zip_lanes32(b, lhs, rhs, |b, a, c| {
                Ok(eval_fp_min_max_bv(b, F32_EB, F32_SB, fp::F32_CANON_NAN as u64, true, a, c))
            });
        }
        BinOp::F32x4Max => {
            return zip_lanes32(b, lhs, rhs, |b, a, c| {
                Ok(eval_fp_min_max_bv(b, F32_EB, F32_SB, fp::F32_CANON_NAN as u64, false, a, c))
            });
        }
        BinOp::F32x4PMin => {
            return zip_lanes32(b, lhs, rhs, |b, a, c| {
                Ok(eval_fp_pmin_pmax_bv(b, F32_EB, F32_SB, true, a, c))
            });
        }
        BinOp::F32x4PMax => {
            return zip_lanes32(b, lhs, rhs, |b, a, c| {
                Ok(eval_fp_pmin_pmax_bv(b, F32_EB, F32_SB, false, a, c))
            });
        }
        BinOp::F32x4Eq => {
            return zip_lanes32_cmp(b, lhs, rhs, |b, a, c| {
                let af = b.bv_to_fp(F32_EB, F32_SB, a);
                let cf = b.bv_to_fp(F32_EB, F32_SB, c);
                b.fp_eq(&af, &cf)
            });
        }
        BinOp::F32x4Ne => {
            return zip_lanes32_cmp(b, lhs, rhs, |b, a, c| {
                let af = b.bv_to_fp(F32_EB, F32_SB, a);
                let cf = b.bv_to_fp(F32_EB, F32_SB, c);
                let eq = b.fp_eq(&af, &cf);
                b.not(&eq)
            });
        }
        BinOp::F32x4Lt => {
            return zip_lanes32_cmp(b, lhs, rhs, |b, a, c| {
                let af = b.bv_to_fp(F32_EB, F32_SB, a);
                let cf = b.bv_to_fp(F32_EB, F32_SB, c);
                b.fp_lt(&af, &cf)
            });
        }
        BinOp::F32x4Gt => {
            return zip_lanes32_cmp(b, lhs, rhs, |b, a, c| {
                let af = b.bv_to_fp(F32_EB, F32_SB, a);
                let cf = b.bv_to_fp(F32_EB, F32_SB, c);
                b.fp_gt(&af, &cf)
            });
        }
        BinOp::F32x4Le => {
            return zip_lanes32_cmp(b, lhs, rhs, |b, a, c| {
                let af = b.bv_to_fp(F32_EB, F32_SB, a);
                let cf = b.bv_to_fp(F32_EB, F32_SB, c);
                b.fp_le(&af, &cf)
            });
        }
        BinOp::F32x4Ge => {
            return zip_lanes32_cmp(b, lhs, rhs, |b, a, c| {
                let af = b.bv_to_fp(F32_EB, F32_SB, a);
                let cf = b.bv_to_fp(F32_EB, F32_SB, c);
                b.fp_ge(&af, &cf)
            });
        }
        // f64x2 lane binary
        BinOp::F64x2Add => zip_lanes_bv(b, &lhs.term, &rhs.term, 64, 2, |b, a, c| {
            let af = b.bv_to_fp(F64_EB, F64_SB, a);
            let cf = b.bv_to_fp(F64_EB, F64_SB, c);
            let rf = b.fp_add(F64_EB, F64_SB, FpRm::Rne, &af, &cf);
            fp_to_bv_canon(b, state, F64_EB, F64_SB, fp::F64_CANON_NAN, &rf)
        })?,
        BinOp::F64x2Sub => zip_lanes_bv(b, &lhs.term, &rhs.term, 64, 2, |b, a, c| {
            let af = b.bv_to_fp(F64_EB, F64_SB, a);
            let cf = b.bv_to_fp(F64_EB, F64_SB, c);
            let rf = b.fp_sub(F64_EB, F64_SB, FpRm::Rne, &af, &cf);
            fp_to_bv_canon(b, state, F64_EB, F64_SB, fp::F64_CANON_NAN, &rf)
        })?,
        BinOp::F64x2Mul => zip_lanes_bv(b, &lhs.term, &rhs.term, 64, 2, |b, a, c| {
            let af = b.bv_to_fp(F64_EB, F64_SB, a);
            let cf = b.bv_to_fp(F64_EB, F64_SB, c);
            let rf = b.fp_mul(F64_EB, F64_SB, FpRm::Rne, &af, &cf);
            fp_to_bv_canon(b, state, F64_EB, F64_SB, fp::F64_CANON_NAN, &rf)
        })?,
        BinOp::F64x2Div => zip_lanes_bv(b, &lhs.term, &rhs.term, 64, 2, |b, a, c| {
            let af = b.bv_to_fp(F64_EB, F64_SB, a);
            let cf = b.bv_to_fp(F64_EB, F64_SB, c);
            let rf = b.fp_div(F64_EB, F64_SB, FpRm::Rne, &af, &cf);
            fp_to_bv_canon(b, state, F64_EB, F64_SB, fp::F64_CANON_NAN, &rf)
        })?,
        BinOp::F64x2Min => zip_lanes_bv(b, &lhs.term, &rhs.term, 64, 2, |b, a, c| {
            Ok(eval_fp_min_max_bv(b, F64_EB, F64_SB, fp::F64_CANON_NAN, true, a, c))
        })?,
        BinOp::F64x2Max => zip_lanes_bv(b, &lhs.term, &rhs.term, 64, 2, |b, a, c| {
            Ok(eval_fp_min_max_bv(b, F64_EB, F64_SB, fp::F64_CANON_NAN, false, a, c))
        })?,
        BinOp::F64x2PMin => zip_lanes_bv(b, &lhs.term, &rhs.term, 64, 2, |b, a, c| {
            Ok(eval_fp_pmin_pmax_bv(b, F64_EB, F64_SB, true, a, c))
        })?,
        BinOp::F64x2PMax => zip_lanes_bv(b, &lhs.term, &rhs.term, 64, 2, |b, a, c| {
            Ok(eval_fp_pmin_pmax_bv(b, F64_EB, F64_SB, false, a, c))
        })?,
        BinOp::F64x2Eq => zip_lanes_bv(b, &lhs.term, &rhs.term, 64, 2, |b, a, c| {
            let af = b.bv_to_fp(F64_EB, F64_SB, a);
            let cf = b.bv_to_fp(F64_EB, F64_SB, c);
            let cond = b.fp_eq(&af, &cf);
            Ok(bool_to_mask(b, 64, cond))
        })?,
        BinOp::F64x2Ne => zip_lanes_bv(b, &lhs.term, &rhs.term, 64, 2, |b, a, c| {
            let af = b.bv_to_fp(F64_EB, F64_SB, a);
            let cf = b.bv_to_fp(F64_EB, F64_SB, c);
            let eq = b.fp_eq(&af, &cf);
            let ne = b.not(&eq);
            Ok(bool_to_mask(b, 64, ne))
        })?,
        BinOp::F64x2Lt => zip_lanes_bv(b, &lhs.term, &rhs.term, 64, 2, |b, a, c| {
            let af = b.bv_to_fp(F64_EB, F64_SB, a);
            let cf = b.bv_to_fp(F64_EB, F64_SB, c);
            let cond = b.fp_lt(&af, &cf);
            Ok(bool_to_mask(b, 64, cond))
        })?,
        BinOp::F64x2Gt => zip_lanes_bv(b, &lhs.term, &rhs.term, 64, 2, |b, a, c| {
            let af = b.bv_to_fp(F64_EB, F64_SB, a);
            let cf = b.bv_to_fp(F64_EB, F64_SB, c);
            let cond = b.fp_gt(&af, &cf);
            Ok(bool_to_mask(b, 64, cond))
        })?,
        BinOp::F64x2Le => zip_lanes_bv(b, &lhs.term, &rhs.term, 64, 2, |b, a, c| {
            let af = b.bv_to_fp(F64_EB, F64_SB, a);
            let cf = b.bv_to_fp(F64_EB, F64_SB, c);
            let cond = b.fp_le(&af, &cf);
            Ok(bool_to_mask(b, 64, cond))
        })?,
        BinOp::F64x2Ge => zip_lanes_bv(b, &lhs.term, &rhs.term, 64, 2, |b, a, c| {
            let af = b.bv_to_fp(F64_EB, F64_SB, a);
            let cf = b.bv_to_fp(F64_EB, F64_SB, c);
            let cond = b.fp_ge(&af, &cf);
            Ok(bool_to_mask(b, 64, cond))
        })?,
        BinOp::I32DivS
        | BinOp::I64DivS
        | BinOp::I32DivU
        | BinOp::I64DivU
        | BinOp::I32RemS
        | BinOp::I64RemS
        | BinOp::I32RemU
        | BinOp::I64RemU => unreachable!(),
    };
    Ok(sym_val(out_ty, term))
}

fn valid_load_store_pair(ty: ValType, width: MemWidth) -> bool {
    matches!(
        (ty, width),
        (ValType::I32, MemWidth::B1 | MemWidth::B2 | MemWidth::B4)
            | (ValType::I64, MemWidth::B1 | MemWidth::B2 | MemWidth::B4 | MemWidth::B8)
            | (ValType::F32, MemWidth::B4)
            | (ValType::F64, MemWidth::B8)
            | (ValType::V128, MemWidth::B16)
    )
}

fn lane_bit_width(kind: LaneKind) -> u8 {
    match kind {
        LaneKind::I8x16S | LaneKind::I8x16U => 8,
        LaneKind::I16x8S | LaneKind::I16x8U => 16,
        LaneKind::I32x4 | LaneKind::F32x4 => 32,
        LaneKind::I64x2 | LaneKind::F64x2 => 64,
    }
}

fn eval_op<B: SmtTarget>(
    b: &mut B,
    state: &mut ExecState<B::Term>,
    op: &Op,
) -> Result<SymVal<B::Term>, SieveError> {
    match op {
        Op::ConstI32(v) => Ok(const_sym_val(b, ValType::I32, (*v as u32) as u128)),
        Op::ConstI64(v) => Ok(const_sym_val(b, ValType::I64, (*v as u64) as u128)),
        Op::ConstF32(bits) => Ok(const_sym_val(b, ValType::F32, *bits as u128)),
        Op::ConstF64(bits) => Ok(const_sym_val(b, ValType::F64, *bits as u128)),
        Op::ConstV128(bits) => Ok(const_sym_val(b, ValType::V128, *bits)),
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
                Ok(zero_sym_val(b, ValType::I32))
            }
        },
        Op::Un(u, a) => {
            let av = state.get_val(*a)?;
            eval_unop(b, state, *u, &av)
        }
        Op::Bin(bin, l, r) => {
            let lv = state.get_val(*l)?;
            let rv = state.get_val(*r)?;
            eval_binop(b, state, *bin, &lv, &rv)
        }
        Op::Load { mem, addr, offset, width, signed, result_ty } => {
            if !valid_load_store_pair(*result_ty, *width) {
                let t = SymBool::from_const(b, true);
                state.trap_if(b, &t, TrapCode::Unreachable);
                return Ok(zero_sym_val(b, *result_ty));
            }
            let addr_v = state.get_u32(*addr)?;
            let w_bytes = width.bytes();
            let w_term = b.bv_const(64, w_bytes);
            let Some((ea32, _can_read)) =
                check_mem_ea(b, state, *mem, &addr_v, *offset, &w_term, Some(w_bytes))
            else {
                return Ok(zero_sym_val(b, *result_ty));
            };
            let mem_sym = state.mems.get_mut(mem).expect("checked");
            mem_sym.record_read(ea32, *width);
            let mut bytes = Vec::with_capacity(w_bytes as usize);
            for i in 0..w_bytes {
                let idx = mem_byte_idx(b, &addr_v, *offset, i as u32);
                bytes.push(eval_mem_byte(b, mem_sym, &idx));
            }
            if *result_ty == ValType::V128 && *width == MemWidth::B16 {
                let mut lanes: Vec<B::Term> = Vec::with_capacity(4);
                for lane in 0..4usize {
                    let base = lane * 4;
                    let mut w = bytes[base].clone();
                    let mut w_bits = 8u8;
                    for byte in &bytes[base + 1..base + 4] {
                        w = b.bv_concat(8, w_bits, byte, &w);
                        w_bits += 8;
                    }
                    lanes.push(w);
                }
                return Ok(pack_plain_lanes32(b, vec_to_arr4(lanes)));
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
            Ok(sym_val(*result_ty, extended))
        }
        Op::MemorySize(mem) => {
            let Some(m) = state.mems.get(mem) else {
                let t = SymBool::from_const(b, true);
                state.trap_if(b, &t, TrapCode::OutOfBoundsMem);
                return Ok(zero_sym_val(b, ValType::I32));
            };
            Ok(sym_val(ValType::I32, b.bv_extract(31, 0, &m.pages)))
        }
        Op::MemoryGrow { mem, delta } => {
            let delta_v = state.get_u32(*delta)?;
            let Some(m) = state.mems.get_mut(mem) else {
                let t = SymBool::from_const(b, true);
                state.trap_if(b, &t, TrapCode::OutOfBoundsMem);
                return Ok(zero_sym_val(b, ValType::I32));
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
            Ok(sym_val(ValType::I32, ret))
        }
        Op::SimdExtractLane { kind, lane, vec } => {
            let out_ty = kind.scalar_ty();
            if *lane >= kind.num_lanes() {
                let t = SymBool::from_const(b, true);
                state.trap_if(b, &t, TrapCode::Unreachable);
                return Ok(zero_sym_val(b, out_ty));
            }
            let vv = state.get_val(*vec)?;
            if vv.ty != ValType::V128 {
                return Err(SieveError::EncodingError(format!(
                    "SimdExtractLane expected V128, got {:?}",
                    vv.ty
                )));
            }
            let w = lane_bit_width(*kind);
            let lo = (*lane as u32) * (w as u32);
            if let Some(k) = vv.konst {
                let raw: u128 = match kind {
                    LaneKind::I8x16S => ((((k >> lo) as u8 as i8) as i32) as u32) as u128,
                    LaneKind::I8x16U => ((k >> lo) as u8) as u128,
                    LaneKind::I16x8S => ((((k >> lo) as u16 as i16) as i32) as u32) as u128,
                    LaneKind::I16x8U => ((k >> lo) as u16) as u128,
                    LaneKind::I32x4 | LaneKind::F32x4 => ((k >> lo) as u32) as u128,
                    LaneKind::I64x2 | LaneKind::F64x2 => ((k >> lo) as u64) as u128,
                };
                return Ok(const_sym_val(b, out_ty, raw));
            }
            if matches!(kind, LaneKind::I32x4 | LaneKind::F32x4) {
                let info = extract_lane32_info(b, &vv, *lane as usize);
                return Ok(SymVal {
                    ty: out_ty,
                    term: info.term,
                    konst: None,
                    lanes32: None,
                    bool01: None,
                    add_terms: if out_ty == ValType::I32 { info.add_terms } else { None },
                });
            }
            if matches!(kind, LaneKind::I64x2 | LaneKind::F64x2)
                && let Some(ref lanes) = vv.lanes32
            {
                let base = (*lane as usize) * 2;
                return Ok(sym_val(
                    out_ty,
                    b.bv_concat(32, 32, &lanes[base + 1].term, &lanes[base].term),
                ));
            }
            let slice = b.bv_extract(lo + (w as u32) - 1, lo, &vv.term);
            let term = match kind {
                LaneKind::I8x16S => b.bv_sext(8, 24, &slice),
                LaneKind::I8x16U => b.bv_zext(8, 24, &slice),
                LaneKind::I16x8S => b.bv_sext(16, 16, &slice),
                LaneKind::I16x8U => b.bv_zext(16, 16, &slice),
                LaneKind::I32x4 | LaneKind::I64x2 | LaneKind::F32x4 | LaneKind::F64x2 => slice,
            };
            Ok(sym_val(out_ty, term))
        }
        Op::SimdReplaceLane { kind, lane, vec, val } => {
            if *lane >= kind.num_lanes() {
                let t = SymBool::from_const(b, true);
                state.trap_if(b, &t, TrapCode::Unreachable);
                return Ok(zero_sym_val(b, ValType::V128));
            }
            let vv = state.get_val(*vec)?;
            let ev = state.get_val(*val)?;
            if vv.ty != ValType::V128 || ev.ty != kind.scalar_ty() {
                return Err(SieveError::EncodingError(format!(
                    "SimdReplaceLane {:?} expected (V128, {:?}), got ({:?}, {:?})",
                    kind,
                    kind.scalar_ty(),
                    vv.ty,
                    ev.ty
                )));
            }
            let w = lane_bit_width(*kind);
            let lo = (*lane as u32) * (w as u32);
            let hi = lo + (w as u32) - 1;
            if let (Some(vk), Some(ek)) = (vv.konst, ev.konst) {
                let lane_mask = if w == 64 { u64::MAX as u128 } else { (1u128 << w) - 1 };
                let replaced = (vk & !(lane_mask << lo)) | ((ek & lane_mask) << lo);
                return Ok(const_sym_val(b, ValType::V128, replaced));
            }
            if matches!(kind, LaneKind::I32x4 | LaneKind::F32x4) {
                let mut lanes = extract_lanes32(b, &vv);
                lanes[*lane as usize] = Lane32 {
                    term: ev.term.clone(),
                    mask_cond: None,
                    add_terms: if ev.ty == ValType::I32 { ev.add_terms.clone() } else { None },
                };
                return Ok(pack_lanes32(b, lanes));
            }
            let elem = match kind {
                LaneKind::I8x16S | LaneKind::I8x16U => b.bv_extract(7, 0, &ev.term),
                LaneKind::I16x8S | LaneKind::I16x8U => b.bv_extract(15, 0, &ev.term),
                LaneKind::I32x4 | LaneKind::I64x2 | LaneKind::F32x4 | LaneKind::F64x2 => {
                    ev.term.clone()
                }
            };
            let term = if lo == 0 {
                let hi_part = b.bv_extract(127, hi + 1, &vv.term);
                b.bv_concat(128 - w, w, &hi_part, &elem)
            } else if hi == 127 {
                let lo_part = b.bv_extract(lo - 1, 0, &vv.term);
                b.bv_concat(w, lo as u8, &elem, &lo_part)
            } else {
                let hi_part = b.bv_extract(127, hi + 1, &vv.term);
                let lo_part = b.bv_extract(lo - 1, 0, &vv.term);
                let mid = b.bv_concat(w, lo as u8, &elem, &lo_part);
                b.bv_concat((127 - hi) as u8, (hi + 1) as u8, &hi_part, &mid)
            };
            Ok(sym_val(ValType::V128, term))
        }
        Op::SimdBitselect { a, b: b_id, mask } => {
            let av = state.get_val(*a)?;
            let bv = state.get_val(*b_id)?;
            let mv = state.get_val(*mask)?;
            if av.ty != ValType::V128 || bv.ty != ValType::V128 || mv.ty != ValType::V128 {
                return Err(SieveError::EncodingError(format!(
                    "SimdBitselect expected (V128, V128, V128), got ({:?}, {:?}, {:?})",
                    av.ty, bv.ty, mv.ty
                )));
            }
            if let (Some(ak), Some(bk), Some(mk)) = (av.konst, bv.konst, mv.konst) {
                return Ok(const_sym_val(b, ValType::V128, (ak & mk) | (bk & !mk)));
            }
            if av.lanes32.is_some() || bv.lanes32.is_some() || mv.lanes32.is_some() {
                let a_lanes = extract_lanes32(b, &av);
                let b_lanes = extract_lanes32(b, &bv);
                let m_lanes = extract_lanes32(b, &mv);
                let mut out_lanes: Vec<Lane32<B::Term>> = Vec::with_capacity(4);
                for i in 0..4 {
                    if let Some(prev) = (0..i).find(|&j| {
                        a_lanes[j].term == a_lanes[i].term
                            && b_lanes[j].term == b_lanes[i].term
                            && m_lanes[j].term == m_lanes[i].term
                    }) {
                        out_lanes.push(out_lanes[prev].clone());
                    } else if let Some(ref cm) = m_lanes[i].mask_cond {
                        out_lanes.push(Lane32::plain(b.ite(cm, &a_lanes[i].term, &b_lanes[i].term)));
                    } else {
                        let a_and_m = b.bv_and(32, &a_lanes[i].term, &m_lanes[i].term);
                        let not_m = b.bv_not(32, &m_lanes[i].term);
                        let b_and_nm = b.bv_and(32, &b_lanes[i].term, &not_m);
                        out_lanes.push(Lane32::plain(b.bv_or(32, &a_and_m, &b_and_nm)));
                    }
                }
                return Ok(pack_lanes32(b, vec_to_arr4(out_lanes)));
            }
            let a_and_m = b.bv_and(128, &av.term, &mv.term);
            let not_m = b.bv_not(128, &mv.term);
            let b_and_nm = b.bv_and(128, &bv.term, &not_m);
            let term = b.bv_or(128, &a_and_m, &b_and_nm);
            Ok(sym_val(ValType::V128, term))
        }
        Op::SimdShuffle { lhs, rhs, lanes } => {
            if lanes.iter().any(|&idx| idx >= 32) {
                let t = SymBool::from_const(b, true);
                state.trap_if(b, &t, TrapCode::Unreachable);
                return Ok(zero_sym_val(b, ValType::V128));
            }
            let lv = state.get_val(*lhs)?;
            let rv = state.get_val(*rhs)?;
            if lv.ty != ValType::V128 || rv.ty != ValType::V128 {
                return Err(SieveError::EncodingError(format!(
                    "SimdShuffle expected (V128, V128), got ({:?}, {:?})",
                    lv.ty, rv.ty
                )));
            }
            if let (Some(lk), Some(rk)) = (lv.konst, rv.konst) {
                return match fp::i8x16_shuffle(lk, rk, *lanes) {
                    Ok(v) => Ok(const_sym_val(b, ValType::V128, v)),
                    Err(code) => {
                        let t = SymBool::from_const(b, true);
                        state.trap_if(b, &t, code);
                        Ok(zero_sym_val(b, ValType::V128))
                    }
                };
            }
            let aligned_lane32 = |k: usize| -> Option<(bool, usize)> {
                let base = lanes[4 * k];
                if base.is_multiple_of(4)
                    && lanes[4 * k + 1] == base + 1
                    && lanes[4 * k + 2] == base + 2
                    && lanes[4 * k + 3] == base + 3
                {
                    if base < 16 {
                        Some((false, (base / 4) as usize))
                    } else {
                        Some((true, ((base - 16) / 4) as usize))
                    }
                } else {
                    None
                }
            };
            if let (Some(l0), Some(l1), Some(l2), Some(l3)) = (
                aligned_lane32(0),
                aligned_lane32(1),
                aligned_lane32(2),
                aligned_lane32(3),
            ) {
                let pick = |b: &mut B, (is_rhs, idx): (bool, usize)| {
                    if is_rhs {
                        extract_lane32_info(b, &rv, idx)
                    } else {
                        extract_lane32_info(b, &lv, idx)
                    }
                };
                let out0 = pick(b, l0);
                let out1 = pick(b, l1);
                let out2 = pick(b, l2);
                let out3 = pick(b, l3);
                return Ok(pack_lanes32(b, [out0, out1, out2, out3]));
            }
            let mut out_bytes = Vec::with_capacity(16);
            for &idx in lanes {
                let (src, byte_idx) = if idx < 16 {
                    (&lv.term, idx as u32)
                } else {
                    (&rv.term, (idx - 16) as u32)
                };
                let lo = byte_idx * 8;
                out_bytes.push(b.bv_extract(lo + 7, lo, src));
            }
            let term = pack_lanes(b, &out_bytes, 8);
            Ok(sym_val(ValType::V128, term))
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
            if !valid_load_store_pair(val_v.ty, *width) {
                let t = SymBool::from_const(b, true);
                state.trap_if(b, &t, TrapCode::Unreachable);
                return Ok(());
            }
            let w_bytes = width.bytes();
            let w_term = b.bv_const(64, w_bytes);
            let Some((_ea32, can_write)) =
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
                let byte = if *width == MemWidth::B16
                    && let Some(ref lanes) = val_v.lanes32
                {
                    let lane_idx = (i / 4) as usize;
                    let lane_byte_lo = ((i % 4) as u32) * 8;
                    b.bv_extract(lane_byte_lo + 7, lane_byte_lo, &lanes[lane_idx].term)
                } else {
                    let lo = (i as u32) * 8;
                    b.bv_extract(lo + 7, lo, &val_v.term)
                };
                let idx = mem_byte_idx(b, &addr_v, *offset, i as u32);
                store_mem_byte_cond(b, mem_sym, &idx, &byte, &can_write, track_writes);
            }
            Ok(())
        }
        EffectOp::MemoryFill { mem, dst, val, len } => {
            let dst_v = state.get_u32(*dst)?;
            let val_v = state.get_u32(*val)?;
            let len_v = state.get_u32(*len)?;
            let len64 = b.bv_zext(32, 32, &len_v.term);
            let Some((_ea32, can_write)) = check_mem_ea(
                b,
                state,
                *mem,
                &dst_v,
                0,
                &len64,
                len_v.konst.map(|k| k as u64),
            ) else {
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
                    let idx = mem_byte_idx(b, &dst_v, 0, i as u32);
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
                    let idx = mem_byte_idx(b, &dst_v, 0, i as u32);
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
            let len_c = len_v.konst.map(|k| k as u64);
            let Some((_dst_ea32, _)) =
                check_mem_ea(b, state, *dst_mem, &dst_v, 0, &len64, len_c)
            else {
                return Ok(());
            };
            let Some((_src_ea32, can_write)) =
                check_mem_ea(b, state, *src_mem, &src_v, 0, &len64, len_c)
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
                    let s_idx = mem_byte_idx(b, &src_v, 0, i as u32);
                    bytes.push(eval_mem_byte(b, &src_snapshot, &s_idx));
                }
                let track_writes = state.track_writes;
                let dst_sym = state.mems.get_mut(dst_mem).expect("checked");
                for (i, byte) in bytes.iter().enumerate() {
                    let d_idx = mem_byte_idx(b, &dst_v, 0, i as u32);
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
                    let s_idx = mem_byte_idx(b, &src_v, 0, i as u32);
                    src_bytes.push(eval_mem_byte(b, &src_snapshot, &s_idx));
                }
                let track_writes = state.track_writes;
                let dst_sym = state.mems.get_mut(dst_mem).expect("checked");
                for (i, byte) in src_bytes.iter().enumerate() {
                    let i32_t = b.bv_const(32, i as u64);
                    let in_len = SymBool::symbolic(b.bv_ult(32, &i32_t, &len_v.term));
                    let do_i = can_write.and(b, &in_len);
                    let d_idx = mem_byte_idx(b, &dst_v, 0, i as u32);
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
            .map(|&ty| zero_sym_val(b, ty))
            .collect());
    }
    if depth >= MAX_CALL_DEPTH {
        let t = SymBool::from_const(b, true);
        state.trap_if(b, &t, TrapCode::OutOfFuel);
        return Ok(results
            .iter()
            .map(|&ty| zero_sym_val(b, ty))
            .collect());
    }
    let saved_env = std::mem::take(&mut state.env);
    if !bind_params(b, state, params, args)? {
        state.env = saved_env;
        return Ok(results
            .iter()
            .map(|&ty| zero_sym_val(b, ty))
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
            .map(|&ty| zero_sym_val(b, ty))
            .collect());
    }
    state.path_active = combined.active;
    if combined.values.is_empty() && !results.is_empty() {
        Ok(results
            .iter()
            .map(|&ty| zero_sym_val(b, ty))
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
            .map(|&(_, ty)| zero_sym_val(b, ty))
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
            .map(|&(_, ty)| zero_sym_val(b, ty))
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
            .map(|&(_, ty)| zero_sym_val(b, ty))
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
            SliceBound::Const(c) => Some(const_sym_val(b, ValType::I32, c as u128)),
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
                .map(|ty| zero_sym_val(b, ty))
                .collect()
        } else if combined.values.is_empty() && !expected_tys.is_empty() {
            expected_tys
                .into_iter()
                .map(|ty| zero_sym_val(b, ty))
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
                sym_val(ty, b.fresh_bv(&name, bits_of(ty)))
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
                        state.env.insert(id, zero_sym_val(b, ty));
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
    /// Soft width-driven fallback defaults (e.g. `MemWidth::B8` -> `I64`, `B4` -> `I32`).
    /// Overridden by any exact type constraint recorded in `free_tys` without conflict.
    fallback_tys: BTreeMap<ValId, ValType>,
}

impl<'a> FreeVarCollector<'a> {
    fn record_fallback(&mut self, id: ValId, bound: &[ValId], ty: ValType) {
        if bound.contains(&id) {
            return;
        }
        self.free_tys.entry(id).or_insert(None);
        // Priority: V128 > I64 > I32 so a B8 store isn't downgraded by a B1/B2/B4 store on the same ValId.
        let rank = |t: ValType| match t {
            ValType::V128 => 3,
            ValType::I64 | ValType::F64 => 2,
            ValType::I32 | ValType::F32 => 1,
        };
        let should_update = self
            .fallback_tys
            .get(&id)
            .is_none_or(|&prev| rank(ty) > rank(prev));
        if should_update {
            self.fallback_tys.insert(id, ty);
        }
    }
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
                                Op::ConstI32(_)
                                | Op::ConstI64(_)
                                | Op::ConstF32(_)
                                | Op::ConstF64(_)
                                | Op::ConstV128(_)
                                | Op::GlobalGet(_)
                                | Op::MemorySize(_) => {}
                                Op::Copy(v) => self.record(v, bound, Some(ty))?,
                                Op::Select { cond, true_val, false_val } => {
                                    self.record(cond, bound, Some(ValType::I32))?;
                                    self.record(true_val, bound, Some(ty))?;
                                    self.record(false_val, bound, Some(ty))?;
                                }
                                Op::Un(u, v) => self.record(v, bound, Some(u.input_ty()))?,
                                Op::Bin(bin, l, r) => {
                                    self.record(l, bound, Some(bin.lhs_ty()))?;
                                    self.record(r, bound, Some(bin.rhs_ty()))?;
                                }
                                Op::Load { addr, .. } => self.record(addr, bound, Some(ValType::I32))?,
                                Op::MemoryGrow { delta, .. } => self.record(delta, bound, Some(ValType::I32))?,
                                Op::SimdExtractLane { vec, .. } => {
                                    self.record(vec, bound, Some(ValType::V128))?;
                                }
                                Op::SimdReplaceLane { kind, vec, val, .. } => {
                                    self.record(vec, bound, Some(ValType::V128))?;
                                    self.record(val, bound, Some(kind.scalar_ty()))?;
                                }
                                Op::SimdBitselect { a, b: b_id, mask } => {
                                    self.record(a, bound, Some(ValType::V128))?;
                                    self.record(b_id, bound, Some(ValType::V128))?;
                                    self.record(mask, bound, Some(ValType::V128))?;
                                }
                                Op::SimdShuffle { lhs, rhs, .. } => {
                                    self.record(lhs, bound, Some(ValType::V128))?;
                                    self.record(rhs, bound, Some(ValType::V128))?;
                                }
                            }
                            bound.push(dst);
                            local_tys.insert(dst, ty);
                        }
                        Stmt::Effect(eff) => match eff {
                            EffectOp::Store { addr, width, val, .. } => {
                                self.record(addr, bound, Some(ValType::I32))?;
                                match width {
                                    MemWidth::B16 => self.record(val, bound, Some(ValType::V128))?,
                                    MemWidth::B8 => {
                                        self.record(val, bound, None)?;
                                        self.record_fallback(val, bound, ValType::I64);
                                    }
                                    MemWidth::B4 | MemWidth::B2 | MemWidth::B1 => {
                                        self.record(val, bound, None)?;
                                        self.record_fallback(val, bound, ValType::I32);
                                    }
                                }
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
    let mut collector = FreeVarCollector {
        module,
        registry,
        free_tys: BTreeMap::new(),
        fallback_tys: BTreeMap::new(),
    };
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
            if collector.free_tys.contains_key(&lv) {
                if let Some(t) = rt {
                    collector.record(lv, &[], Some(t))?;
                } else if let Some(ft) = collector.fallback_tys.get(&rv).copied() {
                    collector.record_fallback(lv, &[], ft);
                }
            }
            if collector.free_tys.contains_key(&rv) {
                if let Some(t) = lt {
                    collector.record(rv, &[], Some(t))?;
                } else if let Some(ft) = collector.fallback_tys.get(&lv).copied() {
                    collector.record_fallback(rv, &[], ft);
                }
            }
        }
    }

    let fallback_tys = collector.fallback_tys;
    Ok(collector
        .free_tys
        .into_iter()
        .map(|(id, ty)| {
            let resolved = ty
                .or_else(|| fallback_tys.get(&id).copied())
                .unwrap_or(ValType::I32);
            (id, resolved)
        })
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
            None => b.get_bv_u128(&sv.term, bits_of(sv.ty))?,
        };
        let val = match sv.ty {
            ValType::I32 => Val::I32(raw as u32 as i32),
            ValType::I64 => Val::I64(raw as u64 as i64),
            ValType::F32 => Val::F32(raw as u32),
            ValType::F64 => Val::F64(raw as u64),
            ValType::V128 => Val::V128(raw),
        };
        scalar_values.push((*id, val));
    }

    let mut global_values = Vec::with_capacity(global_syms.len());
    for (gid, sv) in global_syms {
        let raw = match sv.konst {
            Some(k) => k,
            None => b.get_bv_u128(&sv.term, bits_of(sv.ty))?,
        };
        let val = match sv.ty {
            ValType::I32 => Val::I32(raw as u32 as i32),
            ValType::I64 => Val::I64(raw as u64 as i64),
            ValType::F32 => Val::F32(raw as u32),
            ValType::F64 => Val::F64(raw as u64),
            ValType::V128 => Val::V128(raw),
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
        let sv = sym_val(ty, term);
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
                        | Op::ConstF32(_)
                        | Op::ConstF64(_)
                        | Op::ConstV128(_)
                        | Op::Copy(_)
                        | Op::Select { .. }
                        | Op::SimdBitselect { .. } => {}
                        Op::SimdExtractLane { kind, lane, .. }
                        | Op::SimdReplaceLane { kind, lane, .. } => {
                            if lane >= kind.num_lanes() {
                                return false;
                            }
                        }
                        Op::SimdShuffle { lanes, .. } => {
                            if lanes.iter().any(|&l| l >= 32) {
                                return false;
                            }
                        }
                        Op::Un(u, _) => {
                            if matches!(
                                u,
                                UnOp::I32TruncF32S
                                    | UnOp::I32TruncF32U
                                    | UnOp::I32TruncF64S
                                    | UnOp::I32TruncF64U
                                    | UnOp::I64TruncF32S
                                    | UnOp::I64TruncF32U
                                    | UnOp::I64TruncF64S
                                    | UnOp::I64TruncF64U
                            ) {
                                return false;
                            }
                        }
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
        let sv = const_sym_val(b, ValType::I32, init_u32 as u128);
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
        let sv = sym_val(ty, term);
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
        let sv = sym_val(ty, term);
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
            .map(|&ty| zero_sym_val(b, ty))
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
