#![forbid(unsafe_code)]

//! Step 5 — Proof 2 CLI Runner: Compute-Matched 3-Arm Ablation on `Gnomon-T2T` OMS
//! plus live `gnomon profile` (`x64` skylake + `arm64` neoverse-v2) hardware summary.

use std::path::PathBuf;
use std::process::ExitCode;

use gnomon_bench::{
    ArmVerdict, DEFAULT_PROOF2_TIME_CAP_MS, Proof2Config, run_proof2_ablation,
    run_s4_3_profile_summary,
};

fn fmt_arm_cell(verdict: ArmVerdict, ms: f64, cap_ms: u64) -> String {
    match verdict {
        ArmVerdict::Proved => format!("PROVED ({ms:>6.1}ms)"),
        ArmVerdict::Falsified => format!("FALSIF ({ms:>6.1}ms)"),
        ArmVerdict::Timeout => format!("TMO(>{cap_ms}ms)"),
    }
}

fn fmt_speedup(verdict_base: ArmVerdict, sp: f64) -> String {
    if verdict_base == ArmVerdict::Timeout {
        format!(">{sp:.1}x")
    } else {
        format!("{sp:.1}x")
    }
}

fn main() -> ExitCode {
    let mut time_cap_ms = DEFAULT_PROOF2_TIME_CAP_MS;
    let mut emit_json = false;
    let mut skip_profile = false;

    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--cap-ms" => {
                if let Some(v) = args.next() {
                    match v.parse::<u64>() {
                        Ok(ms) if ms >= 100 => time_cap_ms = ms,
                        _ => {
                            eprintln!("invalid --cap-ms value: {v}");
                            return ExitCode::FAILURE;
                        }
                    }
                }
            }
            "--json" => emit_json = true,
            "--skip-profile" => skip_profile = true,
            "--help" | "-h" => {
                println!(
                    "Usage: proof2_oms_ablation [--cap-ms <ms>] [--json] [--skip-profile]"
                );
                return ExitCode::SUCCESS;
            }
            other => {
                eprintln!("unknown argument: {other}");
                return ExitCode::FAILURE;
            }
        }
    }

    let cfg = Proof2Config { time_cap_ms, ..Proof2Config::default() };
    let report = match run_proof2_ablation(&cfg) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("Proof 2 ablation failed: {e}");
            return ExitCode::FAILURE;
        }
    };

    if emit_json {
        println!(
            "{}",
            serde_json::to_string_pretty(&report).expect("serialize Proof2Report")
        );
        return if report.scorecard.exit_gate_passed() {
            ExitCode::SUCCESS
        } else {
            ExitCode::FAILURE
        };
    }

    let tr = &report.training;
    let sc = &report.scorecard;

    println!("========================================================================================================================");
    println!(
        " Proof 2 — Compute-Matched 3-Arm Ablation on Gnomon-T2T OMS (Identical Bitwuzla Cap = {} ms/task)",
        cfg.time_cap_ms
    );
    println!("========================================================================================================================");
    println!(
        "Training Rung (Rung 1–2): {} raw Strata promoted, {} laws zero-trust UNSAT-verified in {:.1} ms",
        tr.raw_strata_promoted, tr.laws_verified_unsat, tr.training_ms
    );
    println!(
        "Consolidation (`stitch_core` MDL + `egglog` pruning): kept {} Strata ({} laws), pruned {} Strata ({} laws) in {:.1} ms | Unsound admissions: {}",
        tr.kept_strata,
        tr.kept_laws,
        tr.pruned_strata,
        tr.pruned_laws,
        tr.consolidation_ms,
        tr.unsound_admissions
    );
    println!("  Kept Strata  : {}", tr.kept_stratum_names.join(", "));
    println!("  Pruned Strata: {}", tr.pruned_stratum_names.join(", "));
    println!();

    println!(
        "{:<38} {:<4} {:<18} | {:<18} | {:<18} {:>4} | {:>8} {:>8}",
        "HELD-OUT OMS TASK", "RUNG", "ARM A (FLAT L0)", "ARM B (HELPERS)", "ARM C (GNOMON)",
        "LAWS", "C vs A", "C vs B"
    );
    println!("{}", "-".repeat(126));

    for t in &report.held_out_tasks {
        println!(
            "{:<38} R{:<3} {:<18} | {:<18} | {:<18} {:>4} | {:>8} {:>8}",
            t.id,
            t.rung,
            fmt_arm_cell(t.arm_a.verdict, t.arm_a.elapsed_ms, cfg.time_cap_ms),
            fmt_arm_cell(t.arm_b.verdict, t.arm_b.elapsed_ms, cfg.time_cap_ms),
            fmt_arm_cell(t.arm_c.verdict, t.arm_c.elapsed_ms, cfg.time_cap_ms),
            t.arm_c.laws_fired.len(),
            fmt_speedup(t.arm_a.verdict, t.speedup_vs_a),
            fmt_speedup(t.arm_b.verdict, t.speedup_vs_b),
        );
    }

    println!("{}", "-".repeat(126));
    println!("SOUNDNESS CONTROLS (BUGGY MUTANTS — MUST RETURN FALSIFIED, 0 FALSE PROVED):");
    for m in &report.soundness_mutants {
        let cex_tag = match m.counterexample_confirmed_in_kernel {
            Some(true) => "kernel-confirmed",
            Some(false) => "KERNEL-MISMATCH!",
            None => "no-model",
        };
        println!(
            "{:<38} R{:<3} {:<18} | {:<18} | {:<18} {:>4} | {}",
            m.id,
            m.rung,
            fmt_arm_cell(m.arm_a.verdict, m.arm_a.elapsed_ms, cfg.time_cap_ms),
            fmt_arm_cell(m.arm_b.verdict, m.arm_b.elapsed_ms, cfg.time_cap_ms),
            fmt_arm_cell(m.arm_c.verdict, m.arm_c.elapsed_ms, cfg.time_cap_ms),
            m.arm_c.laws_fired.len(),
            cex_tag,
        );
    }

    println!("{}", "=".repeat(126));
    println!("STEP 5 EXIT-GATE SCORECARD:");
    println!(
        "  Held-Out Solved        : Arm A = {}/{} (timeouts: {}) | Arm B = {}/{} (timeouts: {}) | Arm C = {}/{} (timeouts: {})",
        sc.arm_a_solved,
        sc.held_out_total,
        sc.arm_a_timeouts,
        sc.arm_b_solved,
        sc.held_out_total,
        sc.arm_b_timeouts,
        sc.arm_c_solved,
        sc.held_out_total,
        sc.arm_c_timeouts
    );
    println!(
        "  Median SMT Speedup     : Arm C vs Arm A = {:.1}x (gate >= 5.0x) | Arm C vs Arm B = {:.1}x (gate >= 5.0x)",
        sc.median_speedup_vs_a, sc.median_speedup_vs_b
    );
    println!(
        "  Cross-Rung Reuse Rate  : Strata/Laws = {}/{} ({:.1}%) | Explicit egglog Laws Fired = {}/{} ({:.1}%) (gate >= 30.0%)",
        sc.cross_rung_reuse_count,
        sc.held_out_total,
        sc.cross_rung_reuse_rate * 100.0,
        sc.law_firing_reuse_count,
        sc.held_out_total,
        sc.law_firing_reuse_rate * 100.0
    );
    println!(
        "  Soundness Controls     : Mutants Falsified (Arm C) = {}/{} (Arm A: {}/{}, Arm B: {}/{}) | False PROVED = {} | Unsound Admissions = {}",
        sc.mutants_falsified_arm_c,
        sc.mutants_total,
        sc.mutants_falsified_arm_a,
        sc.mutants_total,
        sc.mutants_falsified_arm_b,
        sc.mutants_total,
        sc.false_proved_count,
        sc.unsound_admissions
    );
    println!(
        "  Step 5 Exit Gate       : {} (total runtime {:.1} s)",
        if sc.exit_gate_passed() { "PASS" } else { "FAIL" },
        report.total_elapsed_ms / 1000.0
    );

    if !skip_profile {
        let workspace_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("..")
            .join("..");
        let gnomon_bin = workspace_root.join("target/release/gnomon");
        let s4_3_src = workspace_root.join("examples/oms_strata/s4_3_perf_opt_pairs.rs");
        println!();
        println!("LIVE HARDWARE PROFILE SUMMARY (`gnomon profile --targets x64,arm64` on `s4_3_perf_opt_pairs.rs`):");
        match run_s4_3_profile_summary(&gnomon_bin, &s4_3_src) {
            Ok(pairs) => {
                println!(
                    "{:<28} | {:>10} {:>10} {:>6} {:>5} {:>7} | {:>10} {:>10} {:>6} {:>5} {:>6}",
                    "OMS PERF PAIR",
                    "x64 Cyc",
                    "x64 RTh",
                    "x64Br",
                    "x64Dv",
                    "x64Spil",
                    "ARM64 Cyc",
                    "ARM64 RTh",
                    "A64Br",
                    "A64Dv",
                    "NEON"
                );
                println!("{}", "-".repeat(126));
                for p in &pairs {
                    println!(
                        "{:<28} | {:>9.2}x {:>9.2}x {:>+6} {:>+5} {:>+7} | {:>9.2}x {:>9.2}x {:>+6} {:>+5} {:>+6}",
                        p.label,
                        p.x64_cycle_speedup,
                        p.x64_rthroughput_speedup,
                        p.x64_branch_delta,
                        p.x64_div_delta,
                        p.x64_spill_delta,
                        p.arm64_cycle_speedup,
                        p.arm64_rthroughput_speedup,
                        p.arm64_branch_delta,
                        p.arm64_div_delta,
                        p.arm64_simd_delta
                    );
                }
            }
            Err(err) => {
                println!("  [skipped live profile: {err}]");
            }
        }
    }

    if sc.exit_gate_passed() {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}
