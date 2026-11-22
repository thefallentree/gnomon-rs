//! Native Bitwuzla `QF_ABV` backend using the `bitwuzla` (0.11.0) C/Rust API.

use bitwuzla::{Bitwuzla, Kind, Opt, Options, SatResult, Sort, Term, TermManager};
use gnomon_kernel::{Module, Region, StratumRegistry, VcObligation};

use crate::smt_ir::{RawSat, SmtTarget, run_check_equivalence, run_check_vc};
use crate::{SieveError, SmtBackend, SmtResult};

/// Native in-process Bitwuzla `QF_ABV` solver backend.
#[derive(Clone, Debug, Default)]
pub struct BitwuzlaNativeBackend {
    query_count: u64,
    time_limit_ms: Option<u64>,
}

impl BitwuzlaNativeBackend {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_time_limit_ms(time_limit_ms: u64) -> Self {
        Self { query_count: 0, time_limit_ms: Some(time_limit_ms) }
    }

    fn new_session(&mut self) -> Result<(NativeSession, String), SieveError> {
        let qid = self.query_count;
        self.query_count += 1;
        let tm = TermManager::new();
        let mut opts = Options::new();
        opts.set(Opt::ProduceModels, true)
            .map_err(|e| SieveError::SolverError(e.to_string()))?;
        if let Some(ms) = self.time_limit_ms {
            opts.set(Opt::TimeLimitPer, ms)
                .map_err(|e| SieveError::SolverError(e.to_string()))?;
        }
        let solver = Bitwuzla::new(&tm, &opts)
            .map_err(|e| SieveError::SolverError(e.to_string()))?;
        let bv8 = tm.mk_bv_sort(8);
        let bv32 = tm.mk_bv_sort(32);
        let bv64 = tm.mk_bv_sort(64);
        let bool_sort = tm.mk_bool_sort();
        let mem_sort = tm.mk_array_sort(&bv32, &bv8);
        let written_sort = tm.mk_array_sort(&bv32, &bool_sort);
        Ok((
            NativeSession { tm, solver, bv8, bv32, bv64, mem_sort, written_sort },
            format!("nq{qid}"),
        ))
    }
}

impl SmtBackend for BitwuzlaNativeBackend {
    fn check_vc(
        &mut self,
        module: &Module,
        registry: &StratumRegistry,
        vc: &VcObligation,
    ) -> Result<SmtResult, SieveError> {
        let (mut session, prefix) = self.new_session()?;
        run_check_vc(&mut session, module, registry, vc, &prefix)
    }

    fn check_equivalence(
        &mut self,
        module: &Module,
        registry: &StratumRegistry,
        lhs: &Region,
        rhs: &Region,
        precondition: Option<&Region>,
    ) -> Result<SmtResult, SieveError> {
        let (mut session, prefix) = self.new_session()?;
        run_check_equivalence(&mut session, module, registry, lhs, rhs, precondition, &prefix)
    }
}

struct NativeSession {
    tm: TermManager,
    solver: Bitwuzla,
    bv8: Sort,
    bv32: Sort,
    bv64: Sort,
    mem_sort: Sort,
    written_sort: Sort,
}

impl NativeSession {
    fn bv_sort(&self, bits: u8) -> Sort {
        match bits {
            8 => self.bv8.clone(),
            32 => self.bv32.clone(),
            64 => self.bv64.clone(),
            other => self.tm.mk_bv_sort(other as u64),
        }
    }
}

impl SmtTarget for NativeSession {
    type Term = Term;

    fn bool_const(&mut self, v: bool) -> Term {
        if v { self.tm.mk_true() } else { self.tm.mk_false() }
    }

    fn bv_const(&mut self, bits: u8, v: u64) -> Term {
        let sort = self.bv_sort(bits);
        let masked = match bits {
            64 => v,
            n => v & ((1u64 << n) - 1),
        };
        self.tm.mk_bv_value_u64(&sort, masked)
    }

    fn const_array_bool(&mut self, v: bool) -> Term {
        let val = self.bool_const(v);
        self.tm.mk_const_array(&self.written_sort, &val)
    }

    fn fresh_bv(&mut self, name: &str, bits: u8) -> Term {
        let sort = self.bv_sort(bits);
        self.tm.mk_const(&sort, name)
    }

    fn fresh_mem(&mut self, name: &str) -> Term {
        self.tm.mk_const(&self.mem_sort, name)
    }

    fn not(&mut self, a: &Term) -> Term {
        self.tm.mk_term(Kind::Not, &[a], &[])
    }

    fn and(&mut self, a: &Term, b: &Term) -> Term {
        self.tm.mk_term(Kind::And, &[a, b], &[])
    }

    fn or(&mut self, a: &Term, b: &Term) -> Term {
        self.tm.mk_term(Kind::Or, &[a, b], &[])
    }

    fn eq(&mut self, a: &Term, b: &Term) -> Term {
        self.tm.mk_term(Kind::Equal, &[a, b], &[])
    }

    fn ite(&mut self, cond: &Term, t: &Term, f: &Term) -> Term {
        self.tm.mk_term(Kind::Ite, &[cond, t, f], &[])
    }

    fn array_select(&mut self, arr: &Term, idx: &Term) -> Term {
        self.tm.mk_term(Kind::ArraySelect, &[arr, idx], &[])
    }

    fn array_store(&mut self, arr: &Term, idx: &Term, val: &Term) -> Term {
        self.tm.mk_term(Kind::ArrayStore, &[arr, idx, val], &[])
    }

    fn bv_add(&mut self, _bits: u8, a: &Term, b: &Term) -> Term {
        self.tm.mk_term(Kind::BvAdd, &[a, b], &[])
    }

    fn bv_sub(&mut self, _bits: u8, a: &Term, b: &Term) -> Term {
        self.tm.mk_term(Kind::BvSub, &[a, b], &[])
    }

    fn bv_mul(&mut self, _bits: u8, a: &Term, b: &Term) -> Term {
        self.tm.mk_term(Kind::BvMul, &[a, b], &[])
    }

    fn bv_sdiv(&mut self, _bits: u8, a: &Term, b: &Term) -> Term {
        self.tm.mk_term(Kind::BvSdiv, &[a, b], &[])
    }

    fn bv_udiv(&mut self, _bits: u8, a: &Term, b: &Term) -> Term {
        self.tm.mk_term(Kind::BvUdiv, &[a, b], &[])
    }

    fn bv_srem(&mut self, _bits: u8, a: &Term, b: &Term) -> Term {
        self.tm.mk_term(Kind::BvSrem, &[a, b], &[])
    }

    fn bv_urem(&mut self, _bits: u8, a: &Term, b: &Term) -> Term {
        self.tm.mk_term(Kind::BvUrem, &[a, b], &[])
    }

    fn bv_and(&mut self, _bits: u8, a: &Term, b: &Term) -> Term {
        self.tm.mk_term(Kind::BvAnd, &[a, b], &[])
    }

    fn bv_or(&mut self, _bits: u8, a: &Term, b: &Term) -> Term {
        self.tm.mk_term(Kind::BvOr, &[a, b], &[])
    }

    fn bv_xor(&mut self, _bits: u8, a: &Term, b: &Term) -> Term {
        self.tm.mk_term(Kind::BvXor, &[a, b], &[])
    }

    fn bv_shl(&mut self, _bits: u8, a: &Term, b: &Term) -> Term {
        self.tm.mk_term(Kind::BvShl, &[a, b], &[])
    }

    fn bv_lshr(&mut self, _bits: u8, a: &Term, b: &Term) -> Term {
        self.tm.mk_term(Kind::BvShr, &[a, b], &[])
    }

    fn bv_ashr(&mut self, _bits: u8, a: &Term, b: &Term) -> Term {
        self.tm.mk_term(Kind::BvAshr, &[a, b], &[])
    }

    fn bv_rotl(&mut self, _bits: u8, a: &Term, b: &Term) -> Term {
        self.tm.mk_term(Kind::BvRol, &[a, b], &[])
    }

    fn bv_rotr(&mut self, _bits: u8, a: &Term, b: &Term) -> Term {
        self.tm.mk_term(Kind::BvRor, &[a, b], &[])
    }

    fn bv_ult(&mut self, _bits: u8, a: &Term, b: &Term) -> Term {
        self.tm.mk_term(Kind::BvUlt, &[a, b], &[])
    }

    fn bv_ule(&mut self, _bits: u8, a: &Term, b: &Term) -> Term {
        self.tm.mk_term(Kind::BvUle, &[a, b], &[])
    }

    fn bv_ugt(&mut self, _bits: u8, a: &Term, b: &Term) -> Term {
        self.tm.mk_term(Kind::BvUgt, &[a, b], &[])
    }

    fn bv_uge(&mut self, _bits: u8, a: &Term, b: &Term) -> Term {
        self.tm.mk_term(Kind::BvUge, &[a, b], &[])
    }

    fn bv_slt(&mut self, _bits: u8, a: &Term, b: &Term) -> Term {
        self.tm.mk_term(Kind::BvSlt, &[a, b], &[])
    }

    fn bv_sle(&mut self, _bits: u8, a: &Term, b: &Term) -> Term {
        self.tm.mk_term(Kind::BvSle, &[a, b], &[])
    }

    fn bv_sgt(&mut self, _bits: u8, a: &Term, b: &Term) -> Term {
        self.tm.mk_term(Kind::BvSgt, &[a, b], &[])
    }

    fn bv_sge(&mut self, _bits: u8, a: &Term, b: &Term) -> Term {
        self.tm.mk_term(Kind::BvSge, &[a, b], &[])
    }

    fn bv_extract(&mut self, hi: u32, lo: u32, x: &Term) -> Term {
        self.tm.mk_term(Kind::BvExtract, &[x], &[hi as u64, lo as u64])
    }

    fn bv_zext(&mut self, _src_bits: u8, extra_bits: u8, x: &Term) -> Term {
        self.tm.mk_term(Kind::BvZeroExtend, &[x], &[extra_bits as u64])
    }

    fn bv_sext(&mut self, _src_bits: u8, extra_bits: u8, x: &Term) -> Term {
        self.tm.mk_term(Kind::BvSignExtend, &[x], &[extra_bits as u64])
    }

    fn bv_concat(&mut self, _hi_bits: u8, _lo_bits: u8, hi: &Term, lo: &Term) -> Term {
        self.tm.mk_term(Kind::BvConcat, &[hi, lo], &[])
    }

    fn assert_formula(&mut self, cond: &Term) -> Result<(), SieveError> {
        self.solver.assert_formula(cond);
        Ok(())
    }

    fn push(&mut self) -> Result<(), SieveError> {
        self.solver.push(1);
        Ok(())
    }

    fn pop(&mut self) -> Result<(), SieveError> {
        self.solver.pop(1);
        Ok(())
    }

    fn check_sat(&mut self) -> Result<RawSat, SieveError> {
        match self.solver.check_sat() {
            Ok(SatResult::Unsat) => Ok(RawSat::Unsat),
            Ok(SatResult::Sat) => Ok(RawSat::Sat),
            Ok(SatResult::Unknown) => Ok(RawSat::Unknown("bitwuzla returned unknown".into())),
            Err(e) => Err(SieveError::SolverError(e.to_string())),
        }
    }

    fn get_bv_u64(&mut self, term: &Term, _bits: u8) -> Result<u64, SieveError> {
        let val = self.solver.get_value(term);
        let hex = val.value_str(16);
        u64::from_str_radix(&hex, 16)
            .map_err(|e| SieveError::SolverError(format!("failed to parse BV hex '{hex}': {e}")))
    }

    fn get_bool(&mut self, term: &Term) -> Result<bool, SieveError> {
        let val = self.solver.get_value(term);
        Ok(val.value_bool())
    }
}
