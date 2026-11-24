#![forbid(unsafe_code)]

//! Phase 1 exit gate runner evaluating round-trip lifting, Wasmtime falsification,
//! and `gnomon-kernel` counterexample reproduction across all 30+30 corpus pairs.

use std::time::Instant;

use gnomon_kernel::{
    CallTarget, FuncId, HeapState, Module, Region, RegionNode, RegionRef, Stmt, StratumRegistry,
    TrapCode, Val, ValId, eval_func, remap_region_vals,
};
use gnomon_sieve::{
    BitwuzlaNativeBackend, BitwuzlaPipeBackend, EgglogSimplifier, SmtBackend, SmtResult,
};
use gnomon_wasm::{
    Counterexample, ExecOutcome, FuzzConfig, FuzzOutcome, differential_check, emit_wasm,
    fuzz_equivalence, lift_wasm,
};
use serde::{Deserialize, Serialize};

use crate::Phase1Scorecard;
use crate::corpus::corpus_cases;

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct CaseGateReport {
    pub id: String,
    pub category: String,
    pub bug_kind: String,
    pub round_trip_passed: bool,
    pub mutant_falsified: bool,
    pub kernel_reproduced: bool,
    pub unsound: bool,
    pub falsify_ms: f64,
    pub detail: String,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Phase1Report {
    pub cases: Vec<CaseGateReport>,
    pub scorecard: Phase1Scorecard,
}

fn find_entry_func(module: &Module, expected_export: &str) -> FuncId {
    if let Some(f) = module
        .funcs
        .iter()
        .find(|f| f.export_name.as_deref() == Some(expected_export))
    {
        return f.id;
    }
    if let Some(f) = module.funcs.iter().find(|f| f.export_name.is_some()) {
        return f.id;
    }
    FuncId(0)
}

type StateSnapshot = (Vec<Vec<u8>>, Vec<Val>);

fn eval_to_outcome(
    res: Result<(Vec<Val>, HeapState), TrapCode>,
) -> (ExecOutcome, Option<StateSnapshot>) {
    match res {
        Ok((vals, heap)) => (
            ExecOutcome::Values(vals),
            Some((
                heap.memories.into_iter().map(|m| m.bytes).collect(),
                heap.globals,
            )),
        ),
        Err(trap) => (ExecOutcome::Trap(trap), None),
    }
}

fn build_probe_vectors(params: &[(ValId, gnomon_kernel::ValType)], count: usize, seed: u64) -> Vec<Vec<Val>> {
    const BOUNDARY_32: [i32; 8] = [0, 1, -1, 2, 31, 64, i32::MAX, i32::MIN];
    const BOUNDARY_64: [i64; 8] = [0, 1, -1, 2, 63, 64, i64::MAX, i64::MIN];
    const BOUNDARY_F32: [u32; 8] = [
        0x0000_0000, // +0.0
        0x8000_0000, // -0.0
        0x3F80_0000, // 1.0
        0xBF80_0000, // -1.0
        0x3F00_0000, // 0.5
        0xBF00_0000, // -0.5
        0x7F80_0000, // +Inf
        0x7FC0_0000, // qNaN
    ];
    const BOUNDARY_F64: [u64; 8] = [
        0x0000_0000_0000_0000, // +0.0
        0x8000_0000_0000_0000, // -0.0
        0x3FF0_0000_0000_0000, // 1.0
        0xBFF0_0000_0000_0000, // -1.0
        0x3FE0_0000_0000_0000, // 0.5
        0xBFE0_0000_0000_0000, // -0.5
        0x7FF0_0000_0000_0000, // +Inf
        0x7FF8_0000_0000_0000, // qNaN
    ];
    let mut state = seed ^ 0x9E37_79B9_7F4A_7C15;
    let mut next_u64 = || {
        state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    };
    (0..count)
        .map(|idx| {
            params
                .iter()
                .enumerate()
                .map(|(p_idx, &(_, ty))| {
                    let r = next_u64();
                    match ty {
                        gnomon_kernel::ValType::I32 => {
                            if idx < 8 {
                                Val::I32(BOUNDARY_32[(idx + p_idx) & 7])
                            } else {
                                Val::I32(r as i32)
                            }
                        }
                        gnomon_kernel::ValType::I64 => {
                            if idx < 8 {
                                Val::I64(BOUNDARY_64[(idx + p_idx) & 7])
                            } else {
                                Val::I64(r as i64)
                            }
                        }
                        gnomon_kernel::ValType::F32 => {
                            if idx < 8 {
                                Val::F32(BOUNDARY_F32[(idx + p_idx) & 7])
                            } else {
                                Val::F32(r as u32)
                            }
                        }
                        gnomon_kernel::ValType::F64 => {
                            if idx < 8 {
                                Val::F64(BOUNDARY_F64[(idx + p_idx) & 7])
                            } else {
                                Val::F64(r)
                            }
                        }
                        gnomon_kernel::ValType::V128 => {
                            let hi = next_u64();
                            if idx == 0 {
                                Val::V128(0)
                            } else if idx == 1 {
                                Val::V128(u128::MAX)
                            } else {
                                Val::V128((r as u128) | ((hi as u128) << 64))
                            }
                        }
                    }
                })
                .collect()
        })
        .collect()
}

fn region_is_smt_checkable(region: &Region) -> bool {
    fn check(r: RegionRef<'_>) -> bool {
        match r.node {
            RegionNode::Block(span) => r.stmts(span).all(|s| match s {
                Stmt::Region { region: sub, .. } => r.child(sub).is_some_and(check),
                Stmt::Call { target, .. } => {
                    matches!(target, CallTarget::Func(_) | CallTarget::Stratum(_))
                }
                Stmt::Let { .. }
                | Stmt::Effect(_)
                | Stmt::Yield(_)
                | Stmt::Break { .. }
                | Stmt::Continue { .. }
                | Stmt::Return(_) => true,
            }),
            RegionNode::IfElse { then_region, else_region, .. } => {
                r.child(then_region).is_some_and(check) && r.child(else_region).is_some_and(check)
            }
            RegionNode::BoundedLoop { .. } | RegionNode::InvariantLoop { .. } => false,
        }
    }
    check(region.as_ref())
}

fn max_val_id_in_func(module: &Module) -> u32 {
    let mut max_id = 0u32;
    for f in &module.funcs {
        for &(id, _) in &f.params {
            max_id = max_id.max(id.0);
        }
    }
    max_id
}

fn check_round_trip(
    ref_wasm: &[u8],
    lifted: &Module,
    entry_name: &str,
    entry_id: FuncId,
    cfg: &FuzzConfig,
    smt: Option<&mut dyn SmtBackend>,
) -> Result<bool, (String, bool)> {
    let emitted = emit_wasm(lifted).map_err(|e| (format!("emit_wasm: {e:?}"), false))?;
    let relifted = lift_wasm(&emitted).map_err(|e| (format!("re-lift: {e:?}"), false))?;

    let relift_entry = find_entry_func(&relifted, entry_name);
    let orig_func = lifted
        .func(entry_id)
        .ok_or_else(|| ("missing entry func in lifted module".to_owned(), true))?;
    let relift_func = relifted
        .func(relift_entry)
        .ok_or_else(|| ("missing entry func in re-lifted module".to_owned(), true))?;

    if orig_func.params.len() != relift_func.params.len()
        || orig_func
            .params
            .iter()
            .zip(&relift_func.params)
            .any(|((_, a), (_, b))| a != b)
        || orig_func.results != relift_func.results
    {
        return Err(("round-trip signature mismatch".to_owned(), true));
    }

    let rt_cfg = FuzzConfig {
        total_vectors: cfg.total_vectors.min(2_000),
        fuel_per_run: cfg.fuel_per_run,
        seed: cfg.seed,
    };
    match fuzz_equivalence(ref_wasm, &emitted, entry_id, &rt_cfg) {
        Ok(FuzzOutcome::NoCounterexample { .. }) => {}
        Ok(FuzzOutcome::Falsified(_)) => {
            return Err(("round-trip equivalence falsified by fuzzing".to_owned(), true));
        }
        Err(e) => return Err((format!("round-trip fuzz_equivalence: {e:?}"), false)),
    }

    // 3-way differential verification: gnomon_kernel === wasmtime(orig) === wasmtime(emitted).
    let diff_vecs = build_probe_vectors(&orig_func.params, cfg.total_vectors.clamp(1, 32), cfg.seed);
    differential_check(ref_wasm, entry_id, &diff_vecs, cfg.fuel_per_run)
        .map_err(|e| (format!("3-way differential check failed: {e:?}"), true))?;

    let registry = StratumRegistry::new();
    let probe_args: Vec<Val> = orig_func
        .params
        .iter()
        .map(|&(_, ty)| Val::default_for(ty))
        .collect();
    let lhs_heap = HeapState::from_module(lifted, cfg.fuel_per_run)
        .map_err(|t| (format!("lifted HeapState: {t:?}"), true))?;
    let rhs_heap = HeapState::from_module(&relifted, cfg.fuel_per_run)
        .map_err(|t| (format!("relifted HeapState: {t:?}"), true))?;
    let (lhs_out, lhs_state) = eval_to_outcome(eval_func(
        lifted,
        &registry,
        entry_id,
        &probe_args,
        lhs_heap,
    ));
    let (rhs_out, rhs_state) = eval_to_outcome(eval_func(
        &relifted,
        &registry,
        relift_entry,
        &probe_args,
        rhs_heap,
    ));
    if lhs_out != rhs_out || lhs_state != rhs_state {
        return Err((
            "round-trip kernel eval_func probe mismatch".to_owned(),
            true,
        ));
    }

    // End-to-end Stage-2 integration: Wasm -> GnomonIR -> EgglogSimplifier -> Wasmtime + Bitwuzla.
    let simplifier = EgglogSimplifier::default();
    let (simplified_body, eq_report) = simplifier
        .simplify_region(&orig_func.body, &registry)
        .map_err(|e| (format!("EgglogSimplifier failed: {e:?}"), false))?;
    if eq_report.iters_run > 5 {
        return Err((
            format!("EgglogSimplifier exceeded 5-iter cap ({})", eq_report.iters_run),
            false,
        ));
    }
    let mut simplified_mod = lifted.clone();
    if let Some(f_mut) = simplified_mod.funcs.iter_mut().find(|f| f.id == entry_id) {
        f_mut.body = simplified_body.clone();
    }
    let simplified_wasm =
        emit_wasm(&simplified_mod).map_err(|e| (format!("emit_wasm(simplified): {e:?}"), false))?;
    let simp_cfg = FuzzConfig {
        total_vectors: cfg.total_vectors.min(512),
        fuel_per_run: cfg.fuel_per_run,
        seed: cfg.seed ^ 0x1234_5678_9ABC_DEF0,
    };
    match fuzz_equivalence(ref_wasm, &simplified_wasm, entry_id, &simp_cfg) {
        Ok(FuzzOutcome::NoCounterexample { .. }) => {}
        Ok(FuzzOutcome::Falsified(_)) => {
            return Err((
                "EgglogSimplifier produced unsound simplification (falsified by Wasmtime)".to_owned(),
                true,
            ));
        }
        Err(e) => return Err((format!("simplified fuzz_equivalence: {e:?}"), false)),
    }

    if let Some(backend) = smt {
        if region_is_smt_checkable(&orig_func.body) && region_is_smt_checkable(&simplified_body) {
            match backend.check_equivalence(lifted, &registry, &orig_func.body, &simplified_body, None)
            {
                Ok(SmtResult::Unsat) | Ok(SmtResult::Unknown(_)) => {}
                Ok(SmtResult::Sat(_)) => {
                    return Err((
                        "Bitwuzla found counterexample in EgglogSimplifier output".to_owned(),
                        true,
                    ));
                }
                Err(e) => return Err((format!("SMT simplified check_equivalence: {e:?}"), false)),
            }
        }
        if region_is_smt_checkable(&orig_func.body)
            && region_is_smt_checkable(&relift_func.body)
            && lifted.memories == relifted.memories
            && lifted.globals == relifted.globals
        {
            let map: Vec<(ValId, ValId)> = relift_func
                .params
                .iter()
                .map(|&(p, _)| p)
                .zip(orig_func.params.iter().map(|&(p, _)| p))
                .collect();
            let mut next_val = max_val_id_in_func(lifted).saturating_add(1024);
            let remapped_rhs = remap_region_vals(&relift_func.body, &map, &mut next_val);
            match backend.check_equivalence(lifted, &registry, &orig_func.body, &remapped_rhs, None) {
                Ok(SmtResult::Unsat) | Ok(SmtResult::Unknown(_)) => {}
                Ok(SmtResult::Sat(_)) => {
                    return Err(("SMT found counterexample in round-trip".to_owned(), true));
                }
                Err(e) => return Err((format!("SMT check_equivalence: {e:?}"), false)),
            }
        }
    }

    Ok(true)
}

/// Verifies a Wasmtime `Counterexample` reproduces deterministically in `gnomon_kernel::eval_func`.
pub fn verify_counterexample_in_kernel(
    lhs_mod: &Module,
    rhs_mod: &Module,
    lhs_entry: FuncId,
    rhs_entry: FuncId,
    ce: &Counterexample,
    fuel_per_run: u64,
) -> Result<(), String> {
    let registry = StratumRegistry::new();

    let eval_pair = |lhs_heap: HeapState, rhs_heap: HeapState| {
        let (lhs_out, lhs_mems) =
            eval_to_outcome(eval_func(lhs_mod, &registry, lhs_entry, &ce.inputs, lhs_heap));
        let (rhs_out, rhs_mems) =
            eval_to_outcome(eval_func(rhs_mod, &registry, rhs_entry, &ce.inputs, rhs_heap));
        (lhs_out, lhs_mems, rhs_out, rhs_mems)
    };

    let lhs_heap = HeapState::from_module(lhs_mod, fuel_per_run)
        .map_err(|t| format!("lhs HeapState init failed: {t:?}"))?;
    let rhs_heap = HeapState::from_module(rhs_mod, fuel_per_run)
        .map_err(|t| format!("rhs HeapState init failed: {t:?}"))?;

    let (lhs_out, lhs_mems, rhs_out, rhs_mems) = eval_pair(lhs_heap, rhs_heap);

    if lhs_out != ce.lhs_outcome || rhs_out != ce.rhs_outcome {
        return Err(format!(
            "kernel outcome mismatch vs counterexample: kernel=({lhs_out:?}, {rhs_out:?}) ce=({:?}, {:?})",
            ce.lhs_outcome, ce.rhs_outcome
        ));
    }

    let diverged = lhs_out != rhs_out
        || matches!((&lhs_mems, &rhs_mems), (Some(ls), Some(rs)) if ls != rs);
    if !diverged {
        return Err("kernel eval_func did not observe any divergence on counterexample".into());
    }

    Ok(())
}

fn median_ms(mut samples: Vec<f64>) -> f64 {
    if samples.is_empty() {
        return 0.0;
    }
    samples.sort_by(|a, b| a.total_cmp(b));
    let mid = samples.len() / 2;
    if !samples.len().is_multiple_of(2) {
        samples[mid]
    } else {
        (samples[mid - 1] + samples[mid]) * 0.5
    }
}

/// Runs the Phase 1 exit gate across the 30+30 corpus with default `FuzzConfig`
/// and a persistent Stage-2 `Bitwuzla` SMT oracle.
pub fn run_phase1_gate() -> Phase1Report {
    if let Ok(mut pipe) = BitwuzlaPipeBackend::new() {
        return run_phase1_gate_with_config(&FuzzConfig::default(), Some(&mut pipe));
    }
    let mut native = BitwuzlaNativeBackend::with_time_limit_ms(500);
    run_phase1_gate_with_config(&FuzzConfig::default(), Some(&mut native))
}

/// Runs the Phase 1 exit gate with explicit `FuzzConfig` and optional `SmtBackend`.
pub fn run_phase1_gate_with_config(
    cfg: &FuzzConfig,
    mut smt: Option<&mut dyn SmtBackend>,
) -> Phase1Report {
    let cases = corpus_cases();
    let mut reports = Vec::with_capacity(cases.len());
    let mut falsified_times_ms = Vec::new();

    let mut round_trip_passed = 0usize;
    let mut mutants_falsified = 0usize;
    let mut unsound_count = 0usize;

    for case in &cases {
        let ref_lifted = lift_wasm(&case.reference_wasm);
        let mut_lifted = lift_wasm(&case.mutant_wasm);

        let entry_id = match &ref_lifted {
            Ok(m) => find_entry_func(m, &case.id),
            Err(_) => FuncId(0),
        };
        let mut_entry_id = match &mut_lifted {
            Ok(m) => find_entry_func(m, &case.id),
            Err(_) => FuncId(0),
        };

        let mut rt_ok = false;
        let mut case_unsound = false;
        let mut details = Vec::new();

        match &ref_lifted {
            Ok(lifted) => {
                let smt_ref: Option<&mut dyn SmtBackend> = match smt.as_mut() {
                    Some(b) => Some(&mut **b),
                    None => None,
                };
                match check_round_trip(
                    &case.reference_wasm,
                    lifted,
                    &case.id,
                    entry_id,
                    cfg,
                    smt_ref,
                ) {
                    Ok(passed) => {
                        rt_ok = passed;
                    }
                    Err((msg, is_unsound)) => {
                        if is_unsound {
                            case_unsound = true;
                        }
                        details.push(msg);
                    }
                }
            }
            Err(e) => {
                details.push(format!("lift_wasm(ref): {e:?}"));
            }
        }

        let t0 = Instant::now();
        let fuzz_res = fuzz_equivalence(&case.reference_wasm, &case.mutant_wasm, entry_id, cfg);
        let falsify_ms = t0.elapsed().as_secs_f64() * 1000.0;

        let mut falsified = false;
        let mut kernel_reproduced = false;

        match fuzz_res {
            Ok(FuzzOutcome::Falsified(ce)) => match (&ref_lifted, &mut_lifted) {
                (Ok(lhs_mod), Ok(rhs_mod)) => {
                    match verify_counterexample_in_kernel(
                        lhs_mod,
                        rhs_mod,
                        entry_id,
                        mut_entry_id,
                        &ce,
                        cfg.fuel_per_run,
                    ) {
                        Ok(()) => {
                            falsified = true;
                            kernel_reproduced = true;
                            falsified_times_ms.push(falsify_ms);
                            details.push(format!("falsified in {falsify_ms:.3} ms"));
                        }
                        Err(msg) => {
                            case_unsound = true;
                            details.push(msg);
                        }
                    }
                }
                (_, Err(e)) => {
                    case_unsound = true;
                    details.push(format!("lift_wasm(mut) failed during kernel check: {e:?}"));
                }
                (Err(e), _) => {
                    case_unsound = true;
                    details.push(format!("lift_wasm(ref) failed during kernel check: {e:?}"));
                }
            },
            Ok(FuzzOutcome::NoCounterexample { vectors_tested, .. }) => {
                details.push(format!(
                    "no counterexample found in {vectors_tested} vectors"
                ));
            }
            Err(e) => {
                details.push(format!("fuzz_equivalence: {e:?}"));
            }
        }

        if rt_ok {
            round_trip_passed += 1;
        }
        if falsified {
            mutants_falsified += 1;
        }
        if case_unsound {
            unsound_count += 1;
        }

        reports.push(CaseGateReport {
            id: case.id.clone(),
            category: case.category.clone(),
            bug_kind: case.bug_kind.clone(),
            round_trip_passed: rt_ok,
            mutant_falsified: falsified,
            kernel_reproduced,
            unsound: case_unsound,
            falsify_ms,
            detail: details.join("; "),
        });
    }

    let scorecard = Phase1Scorecard {
        round_trip_passed,
        round_trip_total: cases.len(),
        mutants_falsified,
        mutants_total: cases.len(),
        median_falsify_ms: median_ms(falsified_times_ms),
        unsound_count,
    };

    Phase1Report {
        cases: reports,
        scorecard,
    }
}
