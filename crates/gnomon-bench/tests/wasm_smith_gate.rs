#![forbid(unsafe_code)]

//! Automated `wasm-smith` Differential & Blowup Fuzzer Gate integration test.

use gnomon_bench::{DEFAULT_BASE_SEED, WasmSmithGateConfig, run_wasm_smith_gate};

#[test]
fn wasm_smith_1000_module_differential_and_blowup_gate() {
    let cfg = WasmSmithGateConfig {
        target_lifted: 1_000,
        base_seed: DEFAULT_BASE_SEED,
        smt_sample_count: 300,
        ..WasmSmithGateConfig::default()
    };

    let report = run_wasm_smith_gate(&cfg)
        .unwrap_or_else(|failure| panic!("wasm-smith gate failed: {failure}"));

    assert!(
        report.lifted >= 1_000,
        "expected >= 1,000 lifted modules, got {}",
        report.lifted
    );
    assert_eq!(
        report.roundtrip_ok, report.lifted,
        "every lifted module must pass lossless round-trip"
    );
    assert!(
        report.diff_checks > 0,
        "expected concrete differential checks to run"
    );
    assert!(
        report.cliff_latency.max_ms <= cfg.cliff_ceiling_ms,
        "cliff estimator exceeded {:.1} ms ceiling: {:.2} ms",
        cfg.cliff_ceiling_ms,
        report.cliff_latency.max_ms
    );
    assert!(
        report.egglog_max_iters_seen <= cfg.egglog_config.max_iters,
        "egglog exceeded max_iters cap: {} > {}",
        report.egglog_max_iters_seen,
        cfg.egglog_config.max_iters
    );
    assert_eq!(
        report.smt_sat, 0,
        "reflexive self-equivalence must NEVER return Sat"
    );
    assert!(
        report.smt_checked >= 200,
        "expected >= 200 Bitwuzla reflexive checks, got {}",
        report.smt_checked
    );
}
