#![forbid(unsafe_code)]

use std::collections::{BTreeMap, BTreeSet};

use gnomon_bench::{
    Phase1Scorecard, corpus_cases, corpus_manifest, inspect_wasm_binary, run_phase1_gate,
    verify_counterexample_in_kernel,
};
use gnomon_kernel::{
    BinOp, FuncDef, FuncId, Module, Op, Region, Val, ValId, ValType,
};
use gnomon_wasm::{Counterexample, ExecOutcome};

#[test]
fn corpus_has_exactly_30_pairs_across_6_categories() {
    let cases = corpus_cases();
    let manifest = corpus_manifest();
    assert_eq!(cases.len(), 30);
    assert_eq!(manifest.len(), 30);

    let mut ids = BTreeSet::new();
    let mut by_category: BTreeMap<&str, usize> = BTreeMap::new();
    for entry in &manifest {
        assert!(ids.insert(entry.id), "duplicate case id: {}", entry.id);
        *by_category.entry(entry.category).or_insert(0) += 1;
        assert!(entry.ref_wasm_bytes > 8);
        assert!(entry.mut_wasm_bytes > 8);
    }

    assert_eq!(by_category.len(), 6);
    for (cat, count) in by_category {
        assert_eq!(count, 5, "category {cat} should have exactly 5 pairs");
    }
}

#[test]
fn all_60_wasm_binaries_parse_cleanly_and_export_entry_at_func0() {
    let cases = corpus_cases();
    assert_eq!(cases.len(), 30);

    for case in &cases {
        assert_ne!(
            case.reference_wasm, case.mutant_wasm,
            "case {} reference and mutant binaries are identical",
            case.id
        );

        for (role, wasm) in [("ref", &case.reference_wasm), ("mut", &case.mutant_wasm)] {
            assert!(
                wasm.starts_with(b"\0asm\x01\x00\x00\x00"),
                "{} ({role}) invalid wasm magic/version",
                case.id
            );
            assert!(
                wasm.len() < 8192,
                "{} ({role}) unexpectedly large ({} bytes); check for panic/fmt bloat",
                case.id,
                wasm.len()
            );

            let summary = inspect_wasm_binary(wasm)
                .unwrap_or_else(|e| panic!("{} ({role}) parse error: {e}", case.id));
            assert!(
                !summary.has_import,
                "{} ({role}) must not contain external/WASI imports",
                case.id
            );
            assert!(
                !summary.has_table && !summary.has_element,
                "{} ({role}) must not emit table/element/call_indirect sections",
                case.id
            );
            assert!(
                !summary.has_start,
                "{} ({role}) must not emit start section",
                case.id
            );
            assert!(
                summary.has_memory,
                "{} ({role}) must define linear memory",
                case.id
            );
            assert_eq!(
                summary.code_bodies, 1,
                "{} ({role}) expected single compiled code body (no unreachable unwind stubs)",
                case.id
            );
            assert_eq!(
                summary.func_exports,
                vec![(case.id.clone(), 0)],
                "{} ({role}) expected export `{}` at FuncId(0)",
                case.id,
                case.id
            );
            assert!(
                summary
                    .memory_exports
                    .iter()
                    .any(|(name, idx)| name == "memory" && *idx == 0),
                "{} ({role}) missing `memory` export at index 0",
                case.id
            );
        }
    }
}

#[test]
fn scorecard_exit_gate_invariants() {
    let passing = Phase1Scorecard {
        round_trip_passed: 30,
        round_trip_total: 30,
        mutants_falsified: 30,
        mutants_total: 30,
        median_falsify_ms: 4.2,
        unsound_count: 0,
    };
    assert!(passing.exit_gate_passed());

    assert!(!Phase1Scorecard { round_trip_passed: 29, ..passing }.exit_gate_passed());
    assert!(!Phase1Scorecard { mutants_falsified: 29, ..passing }.exit_gate_passed());
    assert!(!Phase1Scorecard { median_falsify_ms: 50.0, ..passing }.exit_gate_passed());
    assert!(!Phase1Scorecard { unsound_count: 1, ..passing }.exit_gate_passed());
    assert!(
        !Phase1Scorecard {
            round_trip_passed: 29,
            round_trip_total: 29,
            mutants_falsified: 29,
            mutants_total: 29,
            median_falsify_ms: 1.0,
            unsound_count: 0,
        }
        .exit_gate_passed()
    );
}

fn synthetic_add_or_sub_module(is_sub: bool) -> Module {
    let op = if is_sub { BinOp::I32Sub } else { BinOp::I32Add };
    Module {
        funcs: vec![FuncDef {
            id: FuncId(0),
            name: "f".into(),
            export_name: Some("f".into()),
            params: vec![(ValId(0), ValType::I32), (ValId(1), ValType::I32)],
            results: vec![ValType::I32],
            body: Region::build(|b| {
                b.push_let(ValId(2), ValType::I32, Op::Bin(op, ValId(0), ValId(1)));
                b.push_yield(&[ValId(2)]);
            }),
        }],
        ..Module::default()
    }
}

#[test]
fn verify_counterexample_in_kernel_validates_and_rejects_mismatches() {
    let lhs = synthetic_add_or_sub_module(false);
    let rhs = synthetic_add_or_sub_module(true);

    let good_ce = Counterexample {
        inputs: vec![Val::I32(10), Val::I32(3)],
        memory_snapshots: Vec::new(),
        lhs_outcome: ExecOutcome::Values(vec![Val::I32(13)]),
        rhs_outcome: ExecOutcome::Values(vec![Val::I32(7)]),
    };
    assert!(
        verify_counterexample_in_kernel(&lhs, &rhs, FuncId(0), FuncId(0), &good_ce, 10_000).is_ok()
    );

    // Equal outputs (no divergence) must be rejected.
    let no_div_ce = Counterexample {
        inputs: vec![Val::I32(10), Val::I32(0)],
        memory_snapshots: Vec::new(),
        lhs_outcome: ExecOutcome::Values(vec![Val::I32(10)]),
        rhs_outcome: ExecOutcome::Values(vec![Val::I32(10)]),
    };
    assert!(
        verify_counterexample_in_kernel(&lhs, &rhs, FuncId(0), FuncId(0), &no_div_ce, 10_000)
            .is_err()
    );

    // Counterexample outcome mismatch vs kernel must be rejected.
    let bogus_ce = Counterexample {
        inputs: vec![Val::I32(10), Val::I32(3)],
        memory_snapshots: Vec::new(),
        lhs_outcome: ExecOutcome::Values(vec![Val::I32(999)]),
        rhs_outcome: ExecOutcome::Values(vec![Val::I32(7)]),
    };
    assert!(
        verify_counterexample_in_kernel(&lhs, &rhs, FuncId(0), FuncId(0), &bogus_ce, 10_000)
            .is_err()
    );
}

#[test]
fn phase1_gate_runner_executes_all_30_cases_without_panicking() {
    let report = run_phase1_gate();
    assert_eq!(report.cases.len(), 30);
    assert_eq!(report.scorecard.round_trip_total, 30);
    assert_eq!(report.scorecard.mutants_total, 30);
    if report.scorecard.mutants_falsified > 0 {
        assert_eq!(report.scorecard.unsound_count, 0);
        assert!(
            report
                .cases
                .iter()
                .filter(|c| c.mutant_falsified)
                .all(|c| c.kernel_reproduced)
        );
    }
    assert!(report.scorecard.exit_gate_passed(), "exit gate must pass: {:?}", report.scorecard);
}

#[test]
fn stage2_egglog_and_bitwuzla_prove_and_falsify_real_corpus_modules() {
    use gnomon_kernel::{HeapState, StratumRegistry, eval_func, remap_region_vals};
    use gnomon_sieve::{BitwuzlaPipeBackend, EgglogSimplifier, SmtBackend, SmtResult};
    use gnomon_wasm::lift_wasm;

    let cases = corpus_cases();
    let simplifier = EgglogSimplifier::default();
    let reg = StratumRegistry::new();
    let mut smt = BitwuzlaPipeBackend::new().expect("spawn bitwuzla pipe");

    for id in ["ring_wrap_mask", "varint_u32_decode", "bucket_wait_time_div0", "cursor_checked_advance"] {
        let case = cases.iter().find(|c| c.id == id).unwrap();
        let ref_mod = lift_wasm(&case.reference_wasm).unwrap();
        let func = ref_mod.func(FuncId(0)).unwrap();
        let (simp_body, rep) = simplifier.simplify_region(&func.body, &reg).unwrap();
        assert!(rep.iters_run <= 5);
        assert_eq!(
            smt.check_equivalence(&ref_mod, &reg, &func.body, &simp_body, None).unwrap(),
            SmtResult::Unsat,
            "Bitwuzla must formally prove Egglog simplification on {id}"
        );
    }

    // Also prove Bitwuzla Stage-2 synthesizes a concrete Sat counterexample on a real corpus mutant
    // and reproduce that counterexample directly in gnomon_kernel::eval_func!
    let mask_case = cases.iter().find(|c| c.id == "ring_wrap_mask").unwrap();
    let ref_mod = lift_wasm(&mask_case.reference_wasm).unwrap();
    let mut_mod = lift_wasm(&mask_case.mutant_wasm).unwrap();
    let ref_fn = ref_mod.func(FuncId(0)).unwrap();
    let mut_fn = mut_mod.func(FuncId(0)).unwrap();
    let param_map: Vec<(ValId, ValId)> = mut_fn
        .params
        .iter()
        .map(|&(p, _)| p)
        .zip(ref_fn.params.iter().map(|&(p, _)| p))
        .collect();
    let mut nf = 1024;
    let mut_body = remap_region_vals(&mut_fn.body, &param_map, &mut nf);
    let smt_res = smt
        .check_equivalence(&ref_mod, &reg, &ref_fn.body, &mut_body, None)
        .unwrap();
    let SmtResult::Sat(model) = smt_res else {
        panic!("expected Sat counterexample from Bitwuzla on ring_wrap_mask mutant, got {smt_res:?}");
    };
    let args: Vec<Val> = ref_fn
        .params
        .iter()
        .map(|&(pid, ty)| {
            model
                .scalar_values
                .iter()
                .find(|&&(id, _)| id == pid)
                .map(|&(_, v)| v)
                .unwrap_or(Val::default_for(ty))
        })
        .collect();
    let h_ref = HeapState::from_module(&ref_mod, 10_000).unwrap();
    let h_mut = HeapState::from_module(&mut_mod, 10_000).unwrap();
    let out_ref = eval_func(&ref_mod, &reg, FuncId(0), &args, h_ref).map(|(v, _)| v);
    let out_mut = eval_func(&mut_mod, &reg, FuncId(0), &args, h_mut).map(|(v, _)| v);
    assert_ne!(out_ref, out_mut, "Bitwuzla counterexample must diverge in gnomon_kernel::eval_func");
}
