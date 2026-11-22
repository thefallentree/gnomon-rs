#![forbid(unsafe_code)]

use std::process::ExitCode;

use gnomon_bench::phase1::run_phase1_gate;

fn main() -> ExitCode {
    let json_only = std::env::args().any(|a| a == "--json");
    let report = run_phase1_gate();

    if json_only {
        match serde_json::to_string_pretty(&report) {
            Ok(s) => println!("{s}"),
            Err(e) => {
                eprintln!("failed to serialize Phase 1 report: {e}");
                return ExitCode::FAILURE;
            }
        }
    } else {
        println!(
            "{:<26} {:<14} {:<6} {:<7} {:<8} {:<10} DETAIL",
            "CASE", "CATEGORY", "RT", "FALS", "KERNEL", "TIME(ms)"
        );
        println!("{}", "-".repeat(100));
        for c in &report.cases {
            println!(
                "{:<26} {:<14} {:<6} {:<7} {:<8} {:<10.3} {}",
                c.id,
                c.category,
                if c.round_trip_passed { "PASS" } else { "FAIL" },
                if c.mutant_falsified { "PASS" } else { "FAIL" },
                if c.kernel_reproduced { "PASS" } else { "FAIL" },
                c.falsify_ms,
                c.detail
            );
        }
        println!();
        let sc = &report.scorecard;
        let summary = serde_json::json!({
            "round_trip_passed": sc.round_trip_passed,
            "round_trip_total": sc.round_trip_total,
            "mutants_falsified": sc.mutants_falsified,
            "mutants_total": sc.mutants_total,
            "median_falsify_ms": sc.median_falsify_ms,
            "unsound_count": sc.unsound_count,
            "exit_gate_passed": sc.exit_gate_passed(),
        });
        println!("{}", serde_json::to_string_pretty(&summary).unwrap_or_default());
    }

    if report.scorecard.exit_gate_passed() {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}
