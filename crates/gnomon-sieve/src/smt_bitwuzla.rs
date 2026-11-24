//! Native Bitwuzla `QF_ABVFP` backend using the `bitwuzla` (0.11.0) C/Rust API.

use std::collections::HashMap;

use bitwuzla::{Bitwuzla, Kind, Opt, Options, RoundingMode, SatResult, Sort, Term, TermManager};
use gnomon_kernel::{Module, Region, StratumRegistry, VcObligation};

use crate::smt_ir::{
    FpRm, RawSat, SmtTarget, run_check_contract, run_check_equivalence_with_options, run_check_vc,
};
use crate::{ContractSpec, EquivOptions, SieveError, SmtBackend, SmtResult};

/// Native in-process Bitwuzla `QF_ABVFP` solver backend.
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
        let bv128 = tm.mk_bv_sort(128);
        let bool_sort = tm.mk_bool_sort();
        let mem_sort = tm.mk_array_sort(&bv32, &bv8);
        let written_sort = tm.mk_array_sort(&bv32, &bool_sort);
        let rm_rne = tm.mk_rm_value(RoundingMode::Rne);
        let rm_rtp = tm.mk_rm_value(RoundingMode::Rtp);
        let rm_rtn = tm.mk_rm_value(RoundingMode::Rtn);
        let rm_rtz = tm.mk_rm_value(RoundingMode::Rtz);
        Ok((
            NativeSession {
                tm,
                solver,
                prefix: format!("nq{qid}"),
                fp_bv_counter: 0,
                fp_bv_cache: HashMap::new(),
                fp_bv_cache_stack: Vec::new(),
                bv8,
                bv32,
                bv64,
                bv128,
                mem_sort,
                written_sort,
                rm_rne,
                rm_rtp,
                rm_rtn,
                rm_rtz,
            },
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

    fn check_equivalence_with_options(
        &mut self,
        module: &Module,
        registry: &StratumRegistry,
        lhs: &Region,
        rhs: &Region,
        precondition: Option<&Region>,
        opts: &EquivOptions,
    ) -> Result<SmtResult, SieveError> {
        let (mut session, prefix) = self.new_session()?;
        run_check_equivalence_with_options(
            &mut session,
            module,
            registry,
            lhs,
            rhs,
            precondition,
            opts,
            &prefix,
        )
    }

    fn check_contract(
        &mut self,
        module: &Module,
        registry: &StratumRegistry,
        contract: &ContractSpec<'_>,
    ) -> Result<SmtResult, SieveError> {
        let (mut session, prefix) = self.new_session()?;
        run_check_contract(&mut session, module, registry, contract, &prefix)
    }
}

struct NativeSession {
    tm: TermManager,
    solver: Bitwuzla,
    prefix: String,
    fp_bv_counter: u64,
    fp_bv_cache: HashMap<(Term, u64), Term>,
    fp_bv_cache_stack: Vec<HashMap<(Term, u64), Term>>,
    bv8: Sort,
    bv32: Sort,
    bv64: Sort,
    bv128: Sort,
    mem_sort: Sort,
    written_sort: Sort,
    rm_rne: Term,
    rm_rtp: Term,
    rm_rtn: Term,
    rm_rtz: Term,
}

impl NativeSession {
    fn bv_sort(&self, bits: u8) -> Sort {
        match bits {
            8 => self.bv8.clone(),
            32 => self.bv32.clone(),
            64 => self.bv64.clone(),
            128 => self.bv128.clone(),
            other => self.tm.mk_bv_sort(other as u64),
        }
    }

    fn rm_term(&self, rm: FpRm) -> &Term {
        match rm {
            FpRm::Rne => &self.rm_rne,
            FpRm::Rtp => &self.rm_rtp,
            FpRm::Rtn => &self.rm_rtn,
            FpRm::Rtz => &self.rm_rtz,
        }
    }
}

impl SmtTarget for NativeSession {
    type Term = Term;

    fn cmp_term(&self, a: &Term, b: &Term) -> std::cmp::Ordering {
        a.id().cmp(&b.id())
    }

    fn bool_const(&mut self, v: bool) -> Term {
        if v { self.tm.mk_true() } else { self.tm.mk_false() }
    }

    fn bv_const(&mut self, bits: u8, v: u64) -> Term {
        if bits > 64 {
            return self.bv_const_u128(bits, v as u128);
        }
        let sort = self.bv_sort(bits);
        let masked = match bits {
            64 => v,
            n => v & ((1u64 << n) - 1),
        };
        self.tm.mk_bv_value_u64(&sort, masked)
    }

    fn bv_const_u128(&mut self, bits: u8, v: u128) -> Term {
        if bits <= 64 {
            return self.bv_const(bits, v as u64);
        }
        let hi_bits = bits - 64;
        let hi = self.bv_const(hi_bits, (v >> 64) as u64);
        let lo = self.bv_const(64, v as u64);
        self.bv_concat(hi_bits, 64, &hi, &lo)
    }

    fn const_array_bool(&mut self, v: bool) -> Term {
        let val = self.bool_const(v);
        self.tm.mk_const_array(&self.written_sort, &val)
    }

    fn const_array_bv8(&mut self, v: u8) -> Term {
        let val = self.bv_const(8, v as u64);
        self.tm.mk_const_array(&self.mem_sort, &val)
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

    fn bv_not(&mut self, _bits: u8, a: &Term) -> Term {
        self.tm.mk_term(Kind::BvNot, &[a], &[])
    }

    fn bv_neg(&mut self, _bits: u8, a: &Term) -> Term {
        self.tm.mk_term(Kind::BvNeg, &[a], &[])
    }

    fn bv_to_fp(&mut self, eb: u8, sb: u8, bv: &Term) -> Term {
        self.tm.mk_term(Kind::FpToFpFromBv, &[bv], &[eb as u64, sb as u64])
    }

    fn fp_to_bv_canon(
        &mut self,
        eb: u8,
        sb: u8,
        canon_nan_bv: u64,
        fp: &Term,
    ) -> Result<Term, SieveError> {
        let key = (fp.clone(), canon_nan_bv);
        if let Some(existing) = self.fp_bv_cache.get(&key) {
            return Ok(existing.clone());
        }
        let id = self.fp_bv_counter;
        self.fp_bv_counter += 1;
        let bits = eb + sb;
        let name = format!("{}_fpbv_{id}", self.prefix);
        let bv = self.fresh_bv(&name, bits);
        let is_nan = self.fp_is_nan(fp);
        let nan_c = self.bv_const(bits, canon_nan_bv);
        let eq_nan = self.eq(&bv, &nan_c);
        let fp_of_bv = self.bv_to_fp(eb, sb, &bv);
        let eq_fp = self.eq(&fp_of_bv, fp);
        let constraint = self.ite(&is_nan, &eq_nan, &eq_fp);
        self.assert_formula(&constraint)?;
        self.fp_bv_cache.insert(key, bv.clone());
        Ok(bv)
    }

    fn fp_add(&mut self, _eb: u8, _sb: u8, rm: FpRm, a: &Term, b: &Term) -> Term {
        let rm_t = self.rm_term(rm);
        self.tm.mk_term(Kind::FpAdd, &[rm_t, a, b], &[])
    }

    fn fp_sub(&mut self, _eb: u8, _sb: u8, rm: FpRm, a: &Term, b: &Term) -> Term {
        let rm_t = self.rm_term(rm);
        self.tm.mk_term(Kind::FpSub, &[rm_t, a, b], &[])
    }

    fn fp_mul(&mut self, _eb: u8, _sb: u8, rm: FpRm, a: &Term, b: &Term) -> Term {
        let rm_t = self.rm_term(rm);
        self.tm.mk_term(Kind::FpMul, &[rm_t, a, b], &[])
    }

    fn fp_div(&mut self, _eb: u8, _sb: u8, rm: FpRm, a: &Term, b: &Term) -> Term {
        let rm_t = self.rm_term(rm);
        self.tm.mk_term(Kind::FpDiv, &[rm_t, a, b], &[])
    }

    fn fp_sqrt(&mut self, _eb: u8, _sb: u8, rm: FpRm, a: &Term) -> Term {
        let rm_t = self.rm_term(rm);
        self.tm.mk_term(Kind::FpSqrt, &[rm_t, a], &[])
    }

    fn fp_rti(&mut self, _eb: u8, _sb: u8, rm: FpRm, a: &Term) -> Term {
        let rm_t = self.rm_term(rm);
        self.tm.mk_term(Kind::FpRti, &[rm_t, a], &[])
    }

    fn fp_eq(&mut self, a: &Term, b: &Term) -> Term {
        self.tm.mk_term(Kind::FpEqual, &[a, b], &[])
    }

    fn fp_lt(&mut self, a: &Term, b: &Term) -> Term {
        self.tm.mk_term(Kind::FpLt, &[a, b], &[])
    }

    fn fp_le(&mut self, a: &Term, b: &Term) -> Term {
        self.tm.mk_term(Kind::FpLeq, &[a, b], &[])
    }

    fn fp_gt(&mut self, a: &Term, b: &Term) -> Term {
        self.tm.mk_term(Kind::FpGt, &[a, b], &[])
    }

    fn fp_ge(&mut self, a: &Term, b: &Term) -> Term {
        self.tm.mk_term(Kind::FpGeq, &[a, b], &[])
    }

    fn fp_is_nan(&mut self, a: &Term) -> Term {
        self.tm.mk_term(Kind::FpIsNan, &[a], &[])
    }

    fn fp_is_zero(&mut self, a: &Term) -> Term {
        self.tm.mk_term(Kind::FpIsZero, &[a], &[])
    }

    fn fp_is_neg(&mut self, a: &Term) -> Term {
        self.tm.mk_term(Kind::FpIsNeg, &[a], &[])
    }

    fn fp_is_pos(&mut self, a: &Term) -> Term {
        self.tm.mk_term(Kind::FpIsPos, &[a], &[])
    }

    fn fp_is_inf(&mut self, a: &Term) -> Term {
        self.tm.mk_term(Kind::FpIsInf, &[a], &[])
    }

    fn fp_from_sbv(&mut self, eb: u8, sb: u8, rm: FpRm, bv: &Term) -> Term {
        let rm_t = self.rm_term(rm);
        self.tm.mk_term(Kind::FpToFpFromSbv, &[rm_t, bv], &[eb as u64, sb as u64])
    }

    fn fp_from_ubv(&mut self, eb: u8, sb: u8, rm: FpRm, bv: &Term) -> Term {
        let rm_t = self.rm_term(rm);
        self.tm.mk_term(Kind::FpToFpFromUbv, &[rm_t, bv], &[eb as u64, sb as u64])
    }

    fn fp_to_sbv(&mut self, bits: u8, rm: FpRm, fp: &Term) -> Term {
        let rm_t = self.rm_term(rm);
        self.tm.mk_term(Kind::FpToSbv, &[rm_t, fp], &[bits as u64])
    }

    fn fp_to_ubv(&mut self, bits: u8, rm: FpRm, fp: &Term) -> Term {
        let rm_t = self.rm_term(rm);
        self.tm.mk_term(Kind::FpToUbv, &[rm_t, fp], &[bits as u64])
    }

    fn fp_to_fp(&mut self, eb: u8, sb: u8, rm: FpRm, fp: &Term) -> Term {
        let rm_t = self.rm_term(rm);
        self.tm.mk_term(Kind::FpToFpFromFp, &[rm_t, fp], &[eb as u64, sb as u64])
    }

    fn assert_formula(&mut self, cond: &Term) -> Result<(), SieveError> {
        self.solver.assert_formula(cond);
        Ok(())
    }

    fn push(&mut self) -> Result<(), SieveError> {
        self.fp_bv_cache_stack.push(self.fp_bv_cache.clone());
        self.solver.push(1);
        Ok(())
    }

    fn pop(&mut self) -> Result<(), SieveError> {
        if let Some(prev) = self.fp_bv_cache_stack.pop() {
            self.fp_bv_cache = prev;
        }
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

    fn get_bv_u128(&mut self, term: &Term, _bits: u8) -> Result<u128, SieveError> {
        let val = self.solver.get_value(term);
        let hex = val.value_str(16);
        u128::from_str_radix(&hex, 16)
            .map_err(|e| SieveError::SolverError(format!("failed to parse BV128 hex '{hex}': {e}")))
    }

    fn get_bool(&mut self, term: &Term) -> Result<bool, SieveError> {
        let val = self.solver.get_value(term);
        Ok(val.value_bool())
    }
}
