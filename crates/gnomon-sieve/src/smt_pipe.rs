//! Persistent incremental SMT-LIB2 pipe backend spawning a single
//! `bitwuzla --lang=smt2` child process reused across queries via `(push 1)` / `(pop 1)`.

use std::collections::HashMap;
use std::io::{BufRead, BufReader, BufWriter, Write};
use std::path::PathBuf;
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};

use gnomon_kernel::{Module, Region, StratumRegistry, VcObligation};

use crate::smt_ir::{
    FpRm, RawSat, SmtTarget, run_check_contract, run_check_equivalence_with_options, run_check_vc,
};
use crate::{ContractSpec, EquivOptions, SieveError, SmtBackend, SmtResult};

/// Persistent incremental `bitwuzla` SMT-LIB2 child-process backend.
pub struct BitwuzlaPipeBackend {
    child: Child,
    stdin: BufWriter<ChildStdin>,
    stdout: BufReader<ChildStdout>,
    query_count: u64,
    dead: bool,
}

impl std::fmt::Debug for BitwuzlaPipeBackend {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BitwuzlaPipeBackend")
            .field("query_count", &self.query_count)
            .field("dead", &self.dead)
            .finish()
    }
}

fn locate_bitwuzla_binary() -> PathBuf {
    if let Some(home) = std::env::var_os("HOME") {
        let local = PathBuf::from(home).join(".local/bitwuzla/bin/bitwuzla");
        if local.is_file() {
            return local;
        }
    }
    PathBuf::from("bitwuzla")
}

impl BitwuzlaPipeBackend {
    /// Spawns one persistent `bitwuzla` incremental SMT-LIB2 child process.
    pub fn new() -> Result<Self, SieveError> {
        Self::with_binary(locate_bitwuzla_binary())
    }

    /// Spawns one persistent incremental `bitwuzla` child from an explicit path.
    pub fn with_binary(bin: impl Into<PathBuf>) -> Result<Self, SieveError> {
        let bin_path = bin.into();
        let mut child = Command::new(&bin_path)
            .arg("--lang=smt2")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()
            .map_err(|e| {
                SieveError::SolverError(format!(
                    "failed to spawn bitwuzla binary '{}': {e}",
                    bin_path.display()
                ))
            })?;

        let stdin = child
            .stdin
            .take()
            .ok_or_else(|| SieveError::SolverError("missing bitwuzla child stdin".into()))?;
        let stdout = child
            .stdout
            .take()
            .ok_or_else(|| SieveError::SolverError("missing bitwuzla child stdout".into()))?;

        let mut backend = Self {
            child,
            stdin: BufWriter::new(stdin),
            stdout: BufReader::new(stdout),
            query_count: 0,
            dead: false,
        };
        backend.send_raw("(set-option :produce-models true)\n(set-logic QF_ABVFP)\n")?;
        Ok(backend)
    }

    /// Returns the number of queries executed on this persistent process.
    pub fn query_count(&self) -> u64 {
        self.query_count
    }

    fn send_raw(&mut self, data: &str) -> Result<(), SieveError> {
        if self.dead {
            return Err(SieveError::SolverError("bitwuzla pipe process terminated".into()));
        }
        if let Err(e) = self.stdin.write_all(data.as_bytes()).and_then(|_| self.stdin.flush()) {
            self.dead = true;
            return Err(SieveError::SolverError(format!("bitwuzla pipe write failed: {e}")));
        }
        Ok(())
    }

    fn read_line_checked(&mut self) -> Result<String, SieveError> {
        let mut line = String::new();
        let n = self.stdout.read_line(&mut line).map_err(|e| {
            self.dead = true;
            SieveError::SolverError(format!("bitwuzla pipe read failed: {e}"))
        })?;
        if n == 0 {
            self.dead = true;
            return Err(SieveError::SolverError("bitwuzla pipe closed unexpectedly (EOF)".into()));
        }
        Ok(line)
    }

    fn read_sexpr_response(&mut self) -> Result<String, SieveError> {
        let mut buf = String::new();
        let mut depth: i32 = 0;
        let mut started = false;
        let mut in_string = false;
        let mut escaped = false;

        loop {
            let line = self.read_line_checked()?;
            for ch in line.chars() {
                if in_string {
                    if escaped {
                        escaped = false;
                    } else if ch == '\\' {
                        escaped = true;
                    } else if ch == '"' {
                        in_string = false;
                    }
                    continue;
                }
                match ch {
                    '"' => in_string = true,
                    '(' => {
                        started = true;
                        depth += 1;
                    }
                    ')' => {
                        depth -= 1;
                    }
                    _ => {}
                }
            }
            buf.push_str(&line);
            if started && depth <= 0 {
                return Ok(buf);
            }
            if !started && !line.trim().is_empty() {
                return Ok(buf);
            }
        }
    }

    fn run_in_frame<F>(&mut self, f: F) -> Result<SmtResult, SieveError>
    where
        F: FnOnce(&mut PipeSession<'_>) -> Result<SmtResult, SieveError>,
    {
        if self.dead {
            return Err(SieveError::SolverError("bitwuzla pipe process is not alive".into()));
        }
        let qid = self.query_count;
        self.query_count += 1;
        let mut session = PipeSession::new(self, qid);
        let res = f(&mut session);
        let cleanup_res = session.pop_all();
        match (res, cleanup_res) {
            (Ok(r), Ok(())) => Ok(r),
            (Err(e), _) => Err(e),
            (Ok(_), Err(e)) => Err(e),
        }
    }
}

impl Drop for BitwuzlaPipeBackend {
    fn drop(&mut self) {
        if !self.dead {
            let _ = self.stdin.write_all(b"(exit)\n");
            let _ = self.stdin.flush();
        }
        match self.child.try_wait() {
            Ok(Some(_)) => {}
            _ => {
                let _ = self.child.kill();
                let _ = self.child.wait();
            }
        }
    }
}

impl SmtBackend for BitwuzlaPipeBackend {
    fn check_vc(
        &mut self,
        module: &Module,
        registry: &StratumRegistry,
        vc: &VcObligation,
    ) -> Result<SmtResult, SieveError> {
        self.run_in_frame(|session| {
            let prefix = format!("pq{}", session.qid);
            run_check_vc(session, module, registry, vc, &prefix)
        })
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
        self.run_in_frame(|session| {
            let prefix = format!("pq{}", session.qid);
            run_check_equivalence_with_options(
                session,
                module,
                registry,
                lhs,
                rhs,
                precondition,
                opts,
                &prefix,
            )
        })
    }

    fn check_contract(
        &mut self,
        module: &Module,
        registry: &StratumRegistry,
        contract: &ContractSpec<'_>,
    ) -> Result<SmtResult, SieveError> {
        self.run_in_frame(|session| {
            let prefix = format!("pq{}", session.qid);
            run_check_contract(session, module, registry, contract, &prefix)
        })
    }
}

struct PipeSession<'a> {
    backend: &'a mut BitwuzlaPipeBackend,
    qid: u64,
    next_id: u64,
    pending: String,
    expr_cache: HashMap<String, String>,
    cache_stack: Vec<HashMap<String, String>>,
    fp_bv_cache: HashMap<(String, u64), String>,
    fp_bv_cache_stack: Vec<HashMap<(String, u64), String>>,
    sorts: HashMap<String, String>,
    push_depth: usize,
}

impl<'a> PipeSession<'a> {
    fn new(backend: &'a mut BitwuzlaPipeBackend, qid: u64) -> Self {
        Self {
            backend,
            qid,
            next_id: 0,
            pending: String::new(),
            expr_cache: HashMap::new(),
            cache_stack: Vec::new(),
            fp_bv_cache: HashMap::new(),
            fp_bv_cache_stack: Vec::new(),
            sorts: HashMap::new(),
            push_depth: 0,
        }
    }

    fn ensure_outer_push(&mut self) {
        if self.push_depth == 0 {
            self.push_depth = 1;
            let mut with_push = String::from("(push 1)\n");
            with_push.push_str(&self.pending);
            self.pending = with_push;
        }
    }

    fn flush_pending(&mut self) -> Result<(), SieveError> {
        self.ensure_outer_push();
        if !self.pending.is_empty() {
            let cmds = std::mem::take(&mut self.pending);
            self.backend.send_raw(&cmds)?;
        }
        Ok(())
    }

    fn pop_all(&mut self) -> Result<(), SieveError> {
        if self.push_depth == 0 {
            self.pending.clear();
            return Ok(());
        }
        let pops = self.push_depth;
        self.push_depth = 0;
        self.pending.clear();
        self.cache_stack.clear();
        self.fp_bv_cache_stack.clear();
        let mut cmd = String::new();
        for _ in 0..pops {
            cmd.push_str("(pop 1)\n");
        }
        self.backend.send_raw(&cmd)
    }

    fn def(&mut self, sort: &str, rhs: String) -> String {
        if let Some(existing) = self.expr_cache.get(&rhs) {
            return existing.clone();
        }
        let id = self.next_id;
        self.next_id += 1;
        let sym = format!("pq{}_t{id}", self.qid);
        self.pending.push_str(&format!("(define-fun {sym} () {sort} {rhs})\n"));
        self.expr_cache.insert(rhs, sym.clone());
        self.sorts.insert(sym.clone(), sort.to_string());
        sym
    }

    fn bv_sort_str(bits: u8) -> String {
        format!("(_ BitVec {bits})")
    }

    fn fp_sort_str(eb: u8, sb: u8) -> String {
        format!("(_ FloatingPoint {eb} {sb})")
    }

    fn parse_get_value_atom(resp: &str) -> Result<String, SieveError> {
        let trimmed = resp.trim();
        if trimmed.starts_with("(error") {
            return Err(SieveError::SolverError(format!("bitwuzla SMT2 error: {trimmed}")));
        }
        // Expected form: ((sym val))
        let inner = trimmed
            .strip_prefix('(')
            .and_then(|s| s.strip_suffix(')'))
            .map(str::trim)
            .and_then(|s| s.strip_prefix('('))
            .and_then(|s| s.strip_suffix(')'))
            .map(str::trim)
            .ok_or_else(|| {
                SieveError::SolverError(format!("unexpected get-value response: {trimmed}"))
            })?;
        // Split first token (symbol) from the rest (value).
        let split_idx = inner
            .find(char::is_whitespace)
            .ok_or_else(|| SieveError::SolverError(format!("malformed get-value pair: {inner}")))?;
        Ok(inner[split_idx..].trim().to_string())
    }
}

fn parse_smt_bv_literal_u128(val_str: &str) -> Result<u128, SieveError> {
    let s = val_str.trim();
    if let Some(bits) = s.strip_prefix("#b") {
        u128::from_str_radix(bits, 2)
            .map_err(|e| SieveError::SolverError(format!("invalid #b literal '{s}': {e}")))
    } else if let Some(hex) = s.strip_prefix("#x") {
        u128::from_str_radix(hex, 16)
            .map_err(|e| SieveError::SolverError(format!("invalid #x literal '{s}': {e}")))
    } else if let Some(rest) = s.strip_prefix("(_ bv").and_then(|r| r.strip_suffix(')')) {
        let dec = rest
            .split_whitespace()
            .next()
            .ok_or_else(|| SieveError::SolverError(format!("invalid (_ bv ...) '{s}'")))?;
        dec.parse::<u128>()
            .map_err(|e| SieveError::SolverError(format!("invalid bv decimal '{s}': {e}")))
    } else {
        Err(SieveError::SolverError(format!("unsupported BV value format: '{s}'")))
    }
}

fn parse_smt_bv_literal(val_str: &str) -> Result<u64, SieveError> {
    let v = parse_smt_bv_literal_u128(val_str)?;
    u64::try_from(v)
        .map_err(|e| SieveError::SolverError(format!("BV literal '{val_str}' exceeds u64: {e}")))
}

impl SmtTarget for PipeSession<'_> {
    type Term = String;

    fn cmp_term(&self, a: &String, b: &String) -> std::cmp::Ordering {
        a.cmp(b)
    }

    fn bool_const(&mut self, v: bool) -> String {
        if v { "true".to_string() } else { "false".to_string() }
    }

    fn bv_const(&mut self, bits: u8, v: u64) -> String {
        if bits > 64 {
            return self.bv_const_u128(bits, v as u128);
        }
        match bits {
            1 => format!("#b{}", v & 1),
            8 => format!("#x{:02x}", (v as u8)),
            16 => format!("#x{:04x}", (v as u16)),
            32 => format!("#x{:08x}", (v as u32)),
            64 => format!("#x{:016x}", v),
            n => format!("(_ bv{} {n})", v & ((1u64 << n) - 1)),
        }
    }

    fn bv_const_u128(&mut self, bits: u8, v: u128) -> String {
        if bits <= 64 {
            return self.bv_const(bits, v as u64);
        }
        match bits {
            128 => format!("#x{:032x}", v),
            n => format!("(_ bv{} {n})", v & ((1u128 << n) - 1)),
        }
    }

    fn const_array_bool(&mut self, v: bool) -> String {
        let b = if v { "true" } else { "false" };
        self.def(
            "(Array (_ BitVec 32) Bool)",
            format!("((as const (Array (_ BitVec 32) Bool)) {b})"),
        )
    }

    fn const_array_bv8(&mut self, v: u8) -> String {
        let b = self.bv_const(8, v as u64);
        self.def(
            "(Array (_ BitVec 32) (_ BitVec 8))",
            format!("((as const (Array (_ BitVec 32) (_ BitVec 8))) {b})"),
        )
    }

    fn fresh_bv(&mut self, name: &str, bits: u8) -> String {
        let sort = Self::bv_sort_str(bits);
        self.pending.push_str(&format!("(declare-const {name} {sort})\n"));
        self.sorts.insert(name.to_string(), sort);
        name.to_string()
    }

    fn fresh_mem(&mut self, name: &str) -> String {
        let sort = "(Array (_ BitVec 32) (_ BitVec 8))".to_string();
        self.pending.push_str(&format!("(declare-const {name} {sort})\n"));
        self.sorts.insert(name.to_string(), sort);
        name.to_string()
    }

    fn not(&mut self, a: &String) -> String {
        self.def("Bool", format!("(not {a})"))
    }

    fn and(&mut self, a: &String, b: &String) -> String {
        self.def("Bool", format!("(and {a} {b})"))
    }

    fn or(&mut self, a: &String, b: &String) -> String {
        self.def("Bool", format!("(or {a} {b})"))
    }

    fn eq(&mut self, a: &String, b: &String) -> String {
        self.def("Bool", format!("(= {a} {b})"))
    }

    fn ite(&mut self, cond: &String, t: &String, f: &String) -> String {
        // Infer sort conservatively from the term prefix or emit inline via a fresh helper:
        // Actually in SMT-LIB2 `define-fun` requires the return sort!
        // Instead of guessing sort inside `ite` (Bool vs BV vs Array), emit an inline S-expr?
        // Wait: to avoid exponential size blowup on nested `ite`, track term sorts in `PipeTerm`?
        // Wait: `PipeSession` can easily track `sorts: HashMap<String, String>`!
        let sort = self.infer_sort(t);
        self.def(&sort, format!("(ite {cond} {t} {f})"))
    }

    fn array_select(&mut self, arr: &String, idx: &String) -> String {
        let arr_sort = self.infer_sort(arr);
        let elem_sort = if arr_sort.contains("Bool)") { "Bool" } else { "(_ BitVec 8)" };
        self.def(elem_sort, format!("(select {arr} {idx})"))
    }

    fn array_store(&mut self, arr: &String, idx: &String, val: &String) -> String {
        let arr_sort = self.infer_sort(arr);
        self.def(&arr_sort, format!("(store {arr} {idx} {val})"))
    }

    fn bv_add(&mut self, bits: u8, a: &String, b: &String) -> String {
        self.def(&Self::bv_sort_str(bits), format!("(bvadd {a} {b})"))
    }

    fn bv_sub(&mut self, bits: u8, a: &String, b: &String) -> String {
        self.def(&Self::bv_sort_str(bits), format!("(bvsub {a} {b})"))
    }

    fn bv_mul(&mut self, bits: u8, a: &String, b: &String) -> String {
        self.def(&Self::bv_sort_str(bits), format!("(bvmul {a} {b})"))
    }

    fn bv_sdiv(&mut self, bits: u8, a: &String, b: &String) -> String {
        self.def(&Self::bv_sort_str(bits), format!("(bvsdiv {a} {b})"))
    }

    fn bv_udiv(&mut self, bits: u8, a: &String, b: &String) -> String {
        self.def(&Self::bv_sort_str(bits), format!("(bvudiv {a} {b})"))
    }

    fn bv_srem(&mut self, bits: u8, a: &String, b: &String) -> String {
        self.def(&Self::bv_sort_str(bits), format!("(bvsrem {a} {b})"))
    }

    fn bv_urem(&mut self, bits: u8, a: &String, b: &String) -> String {
        self.def(&Self::bv_sort_str(bits), format!("(bvurem {a} {b})"))
    }

    fn bv_and(&mut self, bits: u8, a: &String, b: &String) -> String {
        self.def(&Self::bv_sort_str(bits), format!("(bvand {a} {b})"))
    }

    fn bv_or(&mut self, bits: u8, a: &String, b: &String) -> String {
        self.def(&Self::bv_sort_str(bits), format!("(bvor {a} {b})"))
    }

    fn bv_xor(&mut self, bits: u8, a: &String, b: &String) -> String {
        self.def(&Self::bv_sort_str(bits), format!("(bvxor {a} {b})"))
    }

    fn bv_shl(&mut self, bits: u8, a: &String, b: &String) -> String {
        self.def(&Self::bv_sort_str(bits), format!("(bvshl {a} {b})"))
    }

    fn bv_lshr(&mut self, bits: u8, a: &String, b: &String) -> String {
        self.def(&Self::bv_sort_str(bits), format!("(bvlshr {a} {b})"))
    }

    fn bv_ashr(&mut self, bits: u8, a: &String, b: &String) -> String {
        self.def(&Self::bv_sort_str(bits), format!("(bvashr {a} {b})"))
    }

    fn bv_rotl(&mut self, bits: u8, a: &String, b: &String) -> String {
        // Pure standard QF_ABV encoding for dynamic rotation (b is already masked & (bits - 1)):
        let width_c = self.bv_const(bits, bits as u64);
        let comp = self.bv_sub(bits, &width_c, b);
        let hi = self.bv_shl(bits, a, b);
        let lo = self.bv_lshr(bits, a, &comp);
        self.bv_or(bits, &hi, &lo)
    }

    fn bv_rotr(&mut self, bits: u8, a: &String, b: &String) -> String {
        let width_c = self.bv_const(bits, bits as u64);
        let comp = self.bv_sub(bits, &width_c, b);
        let lo = self.bv_lshr(bits, a, b);
        let hi = self.bv_shl(bits, a, &comp);
        self.bv_or(bits, &lo, &hi)
    }

    fn bv_ult(&mut self, _bits: u8, a: &String, b: &String) -> String {
        self.def("Bool", format!("(bvult {a} {b})"))
    }

    fn bv_ule(&mut self, _bits: u8, a: &String, b: &String) -> String {
        self.def("Bool", format!("(bvule {a} {b})"))
    }

    fn bv_ugt(&mut self, _bits: u8, a: &String, b: &String) -> String {
        self.def("Bool", format!("(bvugt {a} {b})"))
    }

    fn bv_uge(&mut self, _bits: u8, a: &String, b: &String) -> String {
        self.def("Bool", format!("(bvuge {a} {b})"))
    }

    fn bv_slt(&mut self, _bits: u8, a: &String, b: &String) -> String {
        self.def("Bool", format!("(bvslt {a} {b})"))
    }

    fn bv_sle(&mut self, _bits: u8, a: &String, b: &String) -> String {
        self.def("Bool", format!("(bvsle {a} {b})"))
    }

    fn bv_sgt(&mut self, _bits: u8, a: &String, b: &String) -> String {
        self.def("Bool", format!("(bvsgt {a} {b})"))
    }

    fn bv_sge(&mut self, _bits: u8, a: &String, b: &String) -> String {
        self.def("Bool", format!("(bvsge {a} {b})"))
    }

    fn bv_extract(&mut self, hi: u32, lo: u32, x: &String) -> String {
        let bits = (hi - lo + 1) as u8;
        self.def(&Self::bv_sort_str(bits), format!("((_ extract {hi} {lo}) {x})"))
    }

    fn bv_zext(&mut self, src_bits: u8, extra_bits: u8, x: &String) -> String {
        let out_bits = src_bits + extra_bits;
        self.def(&Self::bv_sort_str(out_bits), format!("((_ zero_extend {extra_bits}) {x})"))
    }

    fn bv_sext(&mut self, src_bits: u8, extra_bits: u8, x: &String) -> String {
        let out_bits = src_bits + extra_bits;
        self.def(&Self::bv_sort_str(out_bits), format!("((_ sign_extend {extra_bits}) {x})"))
    }

    fn bv_concat(&mut self, hi_bits: u8, lo_bits: u8, hi: &String, lo: &String) -> String {
        let out_bits = hi_bits + lo_bits;
        self.def(&Self::bv_sort_str(out_bits), format!("(concat {hi} {lo})"))
    }

    fn bv_not(&mut self, bits: u8, a: &String) -> String {
        self.def(&Self::bv_sort_str(bits), format!("(bvnot {a})"))
    }

    fn bv_neg(&mut self, bits: u8, a: &String) -> String {
        self.def(&Self::bv_sort_str(bits), format!("(bvneg {a})"))
    }

    fn bv_to_fp(&mut self, eb: u8, sb: u8, bv: &String) -> String {
        self.def(&Self::fp_sort_str(eb, sb), format!("((_ to_fp {eb} {sb}) {bv})"))
    }

    fn fp_to_bv_canon(
        &mut self,
        eb: u8,
        sb: u8,
        canon_nan_bv: u64,
        fp: &String,
    ) -> Result<String, SieveError> {
        let key = (fp.clone(), canon_nan_bv);
        if let Some(existing) = self.fp_bv_cache.get(&key) {
            return Ok(existing.clone());
        }
        let id = self.next_id;
        self.next_id += 1;
        let bits = eb + sb;
        let name = format!("pq{}_fpbv_{id}", self.qid);
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

    fn fp_add(&mut self, eb: u8, sb: u8, rm: FpRm, a: &String, b: &String) -> String {
        self.def(&Self::fp_sort_str(eb, sb), format!("(fp.add {} {a} {b})", rm.smt2()))
    }

    fn fp_sub(&mut self, eb: u8, sb: u8, rm: FpRm, a: &String, b: &String) -> String {
        self.def(&Self::fp_sort_str(eb, sb), format!("(fp.sub {} {a} {b})", rm.smt2()))
    }

    fn fp_mul(&mut self, eb: u8, sb: u8, rm: FpRm, a: &String, b: &String) -> String {
        self.def(&Self::fp_sort_str(eb, sb), format!("(fp.mul {} {a} {b})", rm.smt2()))
    }

    fn fp_div(&mut self, eb: u8, sb: u8, rm: FpRm, a: &String, b: &String) -> String {
        self.def(&Self::fp_sort_str(eb, sb), format!("(fp.div {} {a} {b})", rm.smt2()))
    }

    fn fp_sqrt(&mut self, eb: u8, sb: u8, rm: FpRm, a: &String) -> String {
        self.def(&Self::fp_sort_str(eb, sb), format!("(fp.sqrt {} {a})", rm.smt2()))
    }

    fn fp_rti(&mut self, eb: u8, sb: u8, rm: FpRm, a: &String) -> String {
        self.def(&Self::fp_sort_str(eb, sb), format!("(fp.roundToIntegral {} {a})", rm.smt2()))
    }

    fn fp_eq(&mut self, a: &String, b: &String) -> String {
        self.def("Bool", format!("(fp.eq {a} {b})"))
    }

    fn fp_lt(&mut self, a: &String, b: &String) -> String {
        self.def("Bool", format!("(fp.lt {a} {b})"))
    }

    fn fp_le(&mut self, a: &String, b: &String) -> String {
        self.def("Bool", format!("(fp.leq {a} {b})"))
    }

    fn fp_gt(&mut self, a: &String, b: &String) -> String {
        self.def("Bool", format!("(fp.gt {a} {b})"))
    }

    fn fp_ge(&mut self, a: &String, b: &String) -> String {
        self.def("Bool", format!("(fp.geq {a} {b})"))
    }

    fn fp_is_nan(&mut self, a: &String) -> String {
        self.def("Bool", format!("(fp.isNaN {a})"))
    }

    fn fp_is_zero(&mut self, a: &String) -> String {
        self.def("Bool", format!("(fp.isZero {a})"))
    }

    fn fp_is_neg(&mut self, a: &String) -> String {
        self.def("Bool", format!("(fp.isNegative {a})"))
    }

    fn fp_is_pos(&mut self, a: &String) -> String {
        self.def("Bool", format!("(fp.isPositive {a})"))
    }

    fn fp_is_inf(&mut self, a: &String) -> String {
        self.def("Bool", format!("(fp.isInfinite {a})"))
    }

    fn fp_from_sbv(&mut self, eb: u8, sb: u8, rm: FpRm, bv: &String) -> String {
        self.def(
            &Self::fp_sort_str(eb, sb),
            format!("((_ to_fp {eb} {sb}) {} {bv})", rm.smt2()),
        )
    }

    fn fp_from_ubv(&mut self, eb: u8, sb: u8, rm: FpRm, bv: &String) -> String {
        self.def(
            &Self::fp_sort_str(eb, sb),
            format!("((_ to_fp_unsigned {eb} {sb}) {} {bv})", rm.smt2()),
        )
    }

    fn fp_to_sbv(&mut self, bits: u8, rm: FpRm, fp: &String) -> String {
        self.def(&Self::bv_sort_str(bits), format!("((_ fp.to_sbv {bits}) {} {fp})", rm.smt2()))
    }

    fn fp_to_ubv(&mut self, bits: u8, rm: FpRm, fp: &String) -> String {
        self.def(&Self::bv_sort_str(bits), format!("((_ fp.to_ubv {bits}) {} {fp})", rm.smt2()))
    }

    fn fp_to_fp(&mut self, eb: u8, sb: u8, rm: FpRm, fp: &String) -> String {
        self.def(
            &Self::fp_sort_str(eb, sb),
            format!("((_ to_fp {eb} {sb}) {} {fp})", rm.smt2()),
        )
    }

    fn assert_formula(&mut self, cond: &String) -> Result<(), SieveError> {
        self.pending.push_str(&format!("(assert {cond})\n"));
        Ok(())
    }

    fn push(&mut self) -> Result<(), SieveError> {
        self.flush_pending()?;
        self.cache_stack.push(self.expr_cache.clone());
        self.fp_bv_cache_stack.push(self.fp_bv_cache.clone());
        self.push_depth += 1;
        self.backend.send_raw("(push 1)\n")
    }

    fn pop(&mut self) -> Result<(), SieveError> {
        self.pending.clear();
        if self.push_depth > 1 {
            self.push_depth -= 1;
            if let Some(prev) = self.cache_stack.pop() {
                self.expr_cache = prev;
            }
            if let Some(prev) = self.fp_bv_cache_stack.pop() {
                self.fp_bv_cache = prev;
            }
            self.backend.send_raw("(pop 1)\n")
        } else {
            Ok(())
        }
    }

    fn check_sat(&mut self) -> Result<RawSat, SieveError> {
        self.flush_pending()?;
        self.backend.send_raw("(check-sat)\n")?;
        let line = self.backend.read_line_checked()?;
        let trimmed = line.trim();
        match trimmed {
            "sat" => Ok(RawSat::Sat),
            "unsat" => Ok(RawSat::Unsat),
            "unknown" => Ok(RawSat::Unknown("bitwuzla returned unknown".into())),
            other => Err(SieveError::SolverError(format!("unexpected check-sat output: {other}"))),
        }
    }

    fn get_bv_u64(&mut self, term: &String, _bits: u8) -> Result<u64, SieveError> {
        self.flush_pending()?;
        self.backend.send_raw(&format!("(get-value ({term}))\n"))?;
        let resp = self.backend.read_sexpr_response()?;
        let val_str = Self::parse_get_value_atom(&resp)?;
        parse_smt_bv_literal(&val_str)
    }

    fn get_bv_u128(&mut self, term: &String, _bits: u8) -> Result<u128, SieveError> {
        self.flush_pending()?;
        self.backend.send_raw(&format!("(get-value ({term}))\n"))?;
        let resp = self.backend.read_sexpr_response()?;
        let val_str = Self::parse_get_value_atom(&resp)?;
        parse_smt_bv_literal_u128(&val_str)
    }

    fn get_bool(&mut self, term: &String) -> Result<bool, SieveError> {
        self.flush_pending()?;
        self.backend.send_raw(&format!("(get-value ({term}))\n"))?;
        let resp = self.backend.read_sexpr_response()?;
        let val_str = Self::parse_get_value_atom(&resp)?;
        match val_str.as_str() {
            "true" => Ok(true),
            "false" => Ok(false),
            other => Err(SieveError::SolverError(format!("unexpected bool value: {other}"))),
        }
    }
}

impl PipeSession<'_> {
    fn infer_sort(&self, term: &str) -> String {
        if let Some(s) = self.sorts.get(term) {
            return s.clone();
        }
        if term == "true" || term == "false" {
            return "Bool".into();
        }
        if let Some(bits) = term.strip_prefix("#b") {
            return format!("(_ BitVec {})", bits.len());
        }
        if let Some(hex) = term.strip_prefix("#x") {
            return format!("(_ BitVec {})", hex.len() * 4);
        }
        if term.starts_with("(_ bv")
            && let Some(w) = term.trim_end_matches(')').split_whitespace().last()
        {
            return format!("(_ BitVec {w})");
        }
        "(_ BitVec 32)".into()
    }
}
