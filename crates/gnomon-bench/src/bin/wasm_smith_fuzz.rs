#![forbid(unsafe_code)]

//! CLI runner for the `wasm-smith` Differential & Blowup Fuzzer Gate.
//!
//! Usage:
//!   cargo run --release -p gnomon-bench --bin wasm_smith_fuzz -- --count 1000 [--seed 0x...] [--smt-sample 1000] [--json]

use std::collections::BTreeMap;
use std::process::ExitCode;

use gnomon_bench::{
    DEFAULT_BASE_SEED, WasmSmithGateConfig, generate_wasm_for_attempt, run_wasm_smith_gate,
    scan_wasm_smith_gate,
};
use gnomon_kernel::StratumRegistry;
use gnomon_sieve::estimate_smt_cliff;
use gnomon_wasm::lift_wasm;

fn parse_u64_arg(raw: &str) -> Result<u64, String> {
    if let Some(hex) = raw.strip_prefix("0x").or_else(|| raw.strip_prefix("0X")) {
        u64::from_str_radix(hex, 16).map_err(|e| format!("invalid hex u64 `{raw}`: {e}"))
    } else {
        raw.parse::<u64>()
            .map_err(|e| format!("invalid u64 `{raw}`: {e}"))
    }
}

fn main() -> ExitCode {
    let mut cfg = WasmSmithGateConfig {
        target_lifted: 1_000,
        base_seed: DEFAULT_BASE_SEED,
        smt_sample_count: 1_000,
        ..WasmSmithGateConfig::default()
    };
    let mut emit_json = false;
    let mut scan_mode = false;
    let mut inspect_attempt: Option<usize> = None;
    let mut smt_sample_explicit = false;

    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--count" => {
                let Some(val) = args.next() else {
                    eprintln!("error: --count requires a value");
                    return ExitCode::FAILURE;
                };
                match val.parse::<usize>() {
                    Ok(n) if n > 0 => {
                        cfg.target_lifted = n;
                        cfg.max_attempts = (n.saturating_mul(10)).max(1_000);
                        if !smt_sample_explicit {
                            cfg.smt_sample_count = n;
                        }
                    }
                    _ => {
                        eprintln!("error: invalid --count value `{val}`");
                        return ExitCode::FAILURE;
                    }
                }
            }
            "--seed" => {
                let Some(val) = args.next() else {
                    eprintln!("error: --seed requires a value");
                    return ExitCode::FAILURE;
                };
                match parse_u64_arg(&val) {
                    Ok(s) => cfg.base_seed = s,
                    Err(e) => {
                        eprintln!("error: {e}");
                        return ExitCode::FAILURE;
                    }
                }
            }
            "--smt-sample" => {
                let Some(val) = args.next() else {
                    eprintln!("error: --smt-sample requires a value");
                    return ExitCode::FAILURE;
                };
                match val.parse::<usize>() {
                    Ok(n) => {
                        cfg.smt_sample_count = n;
                        smt_sample_explicit = true;
                    }
                    Err(_) => {
                        eprintln!("error: invalid --smt-sample value `{val}`");
                        return ExitCode::FAILURE;
                    }
                }
            }
            "--inputs" => {
                let Some(val) = args.next() else {
                    eprintln!("error: --inputs requires a value");
                    return ExitCode::FAILURE;
                };
                match val.parse::<usize>() {
                    Ok(n) if n > 0 => cfg.inputs_per_func = n,
                    _ => {
                        eprintln!("error: invalid --inputs value `{val}`");
                        return ExitCode::FAILURE;
                    }
                }
            }
            "--json" => emit_json = true,
            "--scan" => scan_mode = true,
            "--trace" => cfg.trace = true,
            "--inspect" => {
                let Some(val) = args.next() else {
                    eprintln!("error: --inspect requires an attempt index");
                    return ExitCode::FAILURE;
                };
                match val.parse::<usize>() {
                    Ok(idx) => inspect_attempt = Some(idx),
                    Err(_) => {
                        eprintln!("error: invalid --inspect value `{val}`");
                        return ExitCode::FAILURE;
                    }
                }
            }
            "-h" | "--help" => {
                println!(
                    "Usage: wasm_smith_fuzz [--count N] [--seed U64|0xHEX] [--smt-sample N] [--inputs N] [--scan] [--json]"
                );
                return ExitCode::SUCCESS;
            }
            other => {
                eprintln!("error: unknown argument `{other}`");
                return ExitCode::FAILURE;
            }
        }
    }

    if let Some(attempt_idx) = inspect_attempt {
        match generate_wasm_for_attempt(cfg.base_seed, attempt_idx) {
            Ok(bytes) => {
                println!(
                    "attempt={attempt_idx} base_seed=0x{:016x} wasm_len={}",
                    cfg.base_seed,
                    bytes.len()
                );
                match lift_wasm(&bytes) {
                    Ok(module) => {
                        let reg = StratumRegistry::new();
                        let cliff = estimate_smt_cliff(&module, &reg);
                        println!(
                            "funcs={} memories={} globals={} cliff={:?}",
                            module.funcs.len(),
                            module.memories.len(),
                            module.globals.len(),
                            cliff
                        );
                        for f in &module.funcs {
                            println!(
                                "--- func {:?} name={:?} export={:?} params={:?} results={:?} ---",
                                f.id, f.name, f.export_name, f.params, f.results
                            );
                        }
                        let mut fn_i = 0usize;
                        for payload in wasmparser::Parser::new(0).parse_all(&bytes) {
                            if let Ok(wasmparser::Payload::CodeSectionEntry(body)) = payload {
                                println!("=== wasm body func {fn_i} ===");
                                fn_i += 1;
                                if let Ok(mut ops) = body.get_operators_reader() {
                                    while !ops.eof() {
                                        if let Ok(op) = ops.read() {
                                            println!("  {op:?}");
                                        }
                                    }
                                }
                            }
                        }
                    }
                    Err(e) => println!("lift_wasm error: {e:?}"),
                }
            }
            Err(e) => println!("generate_wasm_for_attempt error: {e:?}"),
        }
        return ExitCode::SUCCESS;
    }

    let outcome = if scan_mode {
        scan_wasm_smith_gate(&cfg)
    } else {
        run_wasm_smith_gate(&cfg).map(|r| (r, Vec::new()))
    };

    match outcome {
        Ok((report, failures)) => {
            if emit_json {
                println!(
                    "{}",
                    serde_json::to_string_pretty(&report).expect("serialize gate report")
                );
            } else {
                println!("=== Gnomon wasm-smith Differential & Blowup Fuzzer Gate ===");
                println!("base_seed:        0x{:016x}", report.base_seed);
                println!(
                    "candidates:       attempts={} gen_err={} skipped_unsupported={} lifted={}",
                    report.attempts,
                    report.generation_errors,
                    report.skipped_unsupported,
                    report.lifted
                );
                if !report.skipped_reasons.is_empty() {
                    println!("skipped_reasons:  {:?}", report.skipped_reasons);
                }
                println!(
                    "roundtrip:        {}/{} valid & re-lifted (0 errors)",
                    report.roundtrip_ok, report.lifted
                );
                println!(
                    "differential:     funcs={} diff_checks={} fuel_or_depth_skipped={} mismatches={}",
                    report.diff_funcs_checked,
                    report.diff_checks,
                    report.diff_fuel_or_depth_skipped,
                    failures
                        .iter()
                        .filter(|f| f.stage.starts_with("diff_"))
                        .count()
                );
                println!(
                    "cliff_ms:         p50={:.3} p95={:.3} p99={:.3} max={:.3} (ceiling={:.1})",
                    report.cliff_latency.p50_ms,
                    report.cliff_latency.p95_ms,
                    report.cliff_latency.p99_ms,
                    report.cliff_latency.max_ms,
                    cfg.cliff_ceiling_ms
                );
                println!(
                    "egglog_ms:        p50={:.3} p95={:.3} p99={:.3} max={:.3} max_iters={} max_nodes_after={}",
                    report.egglog_latency.p50_ms,
                    report.egglog_latency.p95_ms,
                    report.egglog_latency.p99_ms,
                    report.egglog_latency.max_ms,
                    report.egglog_max_iters_seen,
                    report.egglog_max_nodes_after
                );
                println!(
                    "smt_reflexive:    checked={} unsat={} unknown={} sat={} enc_err={} p50={:.3}ms p95={:.3}ms p99={:.3}ms max={:.3}ms",
                    report.smt_checked,
                    report.smt_unsat,
                    report.smt_unknown,
                    report.smt_sat,
                    report.smt_encoding_errors,
                    report.smt_latency.p50_ms,
                    report.smt_latency.p95_ms,
                    report.smt_latency.p99_ms,
                    report.smt_latency.max_ms
                );
                println!("total_elapsed:    {:.2} s", report.total_elapsed_ms / 1000.0);
                if failures.is_empty() {
                    println!("STATUS:           PASS");
                } else {
                    let mut by_stage: BTreeMap<&'static str, usize> = BTreeMap::new();
                    for f in &failures {
                        *by_stage.entry(f.stage).or_insert(0) += 1;
                    }
                    println!("STATUS:           FAIL ({} failures: {:?})", failures.len(), by_stage);
                    let mut by_sig: BTreeMap<String, usize> = BTreeMap::new();
                    for f in &failures {
                        let sig = if f.detail.contains("Shadowing is not allowed") {
                            format!("{}: Shadowing is not allowed", f.stage)
                        } else {
                            format!("{}: {}", f.stage, f.detail.chars().take(80).collect::<String>())
                        };
                        *by_sig.entry(sig).or_insert(0) += 1;
                    }
                    println!("failure_groups:   {by_sig:?}");
                    let mut shown_stage: BTreeMap<&'static str, usize> = BTreeMap::new();
                    for f in &failures {
                        let cnt = shown_stage.entry(f.stage).or_insert(0);
                        if *cnt < 3 {
                            *cnt += 1;
                            println!("  sample [{}]: {}", f.stage, f);
                        }
                    }
                    return ExitCode::FAILURE;
                }
            }
            if failures.is_empty() {
                ExitCode::SUCCESS
            } else {
                ExitCode::FAILURE
            }
        }
        Err(failure) => {
            eprintln!("FAILURE: {failure}");
            ExitCode::FAILURE
        }
    }
}
