#![forbid(unsafe_code)]

//! Automated Step 5 Proof 2 Compute-Matched 3-Arm Ablation Release Gate.

use gnomon_bench::{ArmVerdict, DEFAULT_PROOF2_TIME_CAP_MS, Proof2Config, run_proof2_ablation};

#[test]
fn proof2_compute_matched_3arm_oms_ablation_gate() {
    let handle = std::thread::Builder::new()
        .name("proof2_ablation_gate".into())
        .stack_size(16 * 1024 * 1024)
        .spawn(|| {
            let cfg = Proof2Config {
                time_cap_ms: DEFAULT_PROOF2_TIME_CAP_MS,
                ..Proof2Config::default()
            };
            let report = run_proof2_ablation(&cfg)
                .unwrap_or_else(|e| panic!("Proof 2 ablation failed: {e}"));
            let sc = &report.scorecard;

            assert!(
                sc.held_out_total >= 8,
                "expected >= 8 held-out OMS cliff tasks, got {}",
                sc.held_out_total
            );
            assert_eq!(
                sc.arm_c_solved, sc.held_out_total,
                "Arm C (Full Gnomon) must solve 100% of held-out OMS tasks ({}/{})",
                sc.arm_c_solved, sc.held_out_total
            );
            assert!(
                sc.arm_c_solved >= 2 * sc.arm_a_solved.max(1),
                "Arm C solved ({}) must be >= 2x Arm A solved ({})",
                sc.arm_c_solved,
                sc.arm_a_solved
            );
            assert!(
                sc.arm_c_solved >= 2 * sc.arm_b_solved.max(1),
                "Arm C solved ({}) must be >= 2x Arm B solved ({})",
                sc.arm_c_solved,
                sc.arm_b_solved
            );
            assert!(
                sc.median_speedup_vs_a >= 5.0,
                "median SMT speedup vs Arm A ({:.2}x) must be >= 5.0x",
                sc.median_speedup_vs_a
            );
            assert!(
                sc.median_speedup_vs_b >= 5.0,
                "median SMT speedup vs Arm B ({:.2}x) must be >= 5.0x",
                sc.median_speedup_vs_b
            );
            assert!(
                sc.cross_rung_reuse_rate >= 0.30,
                "cross-rung Stratum/law reuse rate ({:.1}%) must be >= 30%",
                sc.cross_rung_reuse_rate * 100.0
            );
            assert!(
                sc.law_firing_reuse_rate >= 0.30,
                "explicit egglog law-firing reuse rate ({:.1}%) must be >= 30%",
                sc.law_firing_reuse_rate * 100.0
            );
            assert_eq!(
                sc.mutants_total, 2,
                "expected exactly 2 soundness-control mutants"
            );
            assert_eq!(
                sc.mutants_falsified_arm_c, 2,
                "Arm C must falsify 2/2 soundness-control mutants, got {}/2",
                sc.mutants_falsified_arm_c
            );
            assert_eq!(
                sc.false_proved_count, 0,
                "0 false PROVED allowed on buggy mutants"
            );
            assert_eq!(
                sc.unsound_admissions, 0,
                "0 unsound admissions allowed across training, consolidation, and evaluation"
            );
            for m in &report.soundness_mutants {
                assert_eq!(
                    m.arm_c.verdict,
                    ArmVerdict::Falsified,
                    "mutant {} must be FALSIFIED by Arm C",
                    m.id
                );
                assert_eq!(
                    m.counterexample_confirmed_in_kernel,
                    Some(true),
                    "mutant {} counterexample must be confirmed by gnomon-kernel",
                    m.id
                );
            }
            assert!(
                report.training.pruned_strata >= 1,
                "stitch_core consolidation must prune the 1-use scratch Stratum"
            );
            assert!(
                sc.exit_gate_passed(),
                "Proof2Scorecard::exit_gate_passed() must be true"
            );
        })
        .expect("failed to spawn proof2_ablation_gate thread");

    if let Err(payload) = handle.join() {
        std::panic::resume_unwind(payload);
    }
}
