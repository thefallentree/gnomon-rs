#![forbid(unsafe_code)]

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

use serde_json::Value;

static TEST_TMP_COUNTER: AtomicU64 = AtomicU64::new(0);

struct TempDirGuard {
    path: PathBuf,
}

impl TempDirGuard {
    fn new(tag: &str) -> Self {
        let pid = std::process::id();
        let seq = TEST_TMP_COUNTER.fetch_add(1, Ordering::Relaxed);
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0);
        let path = std::env::temp_dir().join(format!("gnomon_e2e_s4v_{tag}_{pid}_{seq}_{nanos}"));
        std::fs::create_dir_all(&path).expect("create temp test dir");
        Self { path }
    }

    fn path(&self) -> &Path {
        &self.path
    }
}

impl Drop for TempDirGuard {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.path);
    }
}

fn gnomon_bin() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_gnomon"))
}

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf()
}

fn oms_rs(name: &str) -> PathBuf {
    let p = repo_root()
        .join("examples")
        .join("oms_strata")
        .join(format!("{name}.rs"));
    assert!(p.is_file(), "missing OMS Rust fixture: {}", p.display());
    p
}

fn vp_rs(name: &str) -> PathBuf {
    let p = repo_root()
        .join("examples")
        .join("vertical_packs")
        .join(format!("{name}.rs"));
    assert!(
        p.is_file(),
        "missing vertical-pack Rust fixture: {}",
        p.display()
    );
    p
}

/// Resolves prebuilt `examples/<subdir>/out/<name>.wasm` or compiles `examples/<subdir>/<name>.rs`
/// into `tmp_dir` on demand so tests remain green even on a clean checkout without `out/`.
fn fixture_wasm(subdir: &str, name: &str, simd128: bool, tmp_dir: &Path) -> PathBuf {
    let dir = repo_root().join("examples").join(subdir);
    let prebuilt = dir.join("out").join(format!("{name}.wasm"));
    if prebuilt.is_file() {
        return prebuilt;
    }
    let src = dir.join(format!("{name}.rs"));
    assert!(src.is_file(), "missing fixture source: {}", src.display());
    let out = tmp_dir.join(format!("{name}.wasm"));
    let mut cmd = Command::new("rustc");
    cmd.args([
        "--target",
        "wasm32-unknown-unknown",
        "--crate-type=cdylib",
        "-O",
        "-C",
        "panic=abort",
    ]);
    if simd128 {
        cmd.args(["-C", "target-feature=+simd128"]);
    }
    let status = cmd
        .arg(&src)
        .arg("-o")
        .arg(&out)
        .status()
        .expect("failed invoking rustc for wasm32 fixture");
    assert!(status.success(), "rustc failed compiling {}", src.display());
    out
}

fn run_cli_expect(args: &[&str], expected_exit: i32) -> Value {
    let out = Command::new(gnomon_bin())
        .args(args)
        .output()
        .expect("failed executing gnomon CLI");
    let code = out.status.code().unwrap_or(-1);
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert_eq!(
        code, expected_exit,
        "gnomon {} exited {code} (expected {expected_exit})\nstdout={stdout}\nstderr={stderr}",
        args.join(" ")
    );
    serde_json::from_str(&stdout).unwrap_or_else(|e| {
        panic!(
            "invalid JSON from gnomon {}: {e}\nstdout={stdout}\nstderr={stderr}",
            args.join(" ")
        )
    })
}

fn register_layer1_strata(state_path: &Path, register_order_id_mix: bool, register_risk_strata: bool) {
    let st = state_path.to_str().unwrap();
    if register_order_id_mix {
        let s1_3 = oms_rs("s1_3_order_id_mix");
        let v = run_cli_expect(
            &[
                "--state",
                st,
                "define-op",
                "--name",
                "order_id_mix",
                "--layer",
                "1",
                s1_3.to_str().unwrap(),
            ],
            0,
        );
        assert_eq!(v["status"], "CANDIDATE_REGISTERED");
    }
    if register_risk_strata {
        let s1_1 = oms_rs("s1_1_notional_collar");
        let v1 = run_cli_expect(
            &[
                "--state",
                st,
                "define-op",
                "--name",
                "checked_notional",
                "--entry",
                "checked_notional",
                "--layer",
                "1",
                s1_1.to_str().unwrap(),
            ],
            0,
        );
        assert_eq!(v1["status"], "CANDIDATE_REGISTERED");
        let v2 = run_cli_expect(
            &[
                "--state",
                st,
                "define-op",
                "--name",
                "price_collar_ok",
                "--entry",
                "price_collar_ok",
                "--layer",
                "1",
                s1_1.to_str().unwrap(),
            ],
            0,
        );
        assert_eq!(v2["status"], "CANDIDATE_REGISTERED");
    }
}

// ============================================================================
// Step 4 — S4.1: E2E Inbound ExecReport OMS Pipeline + Mutants
// ============================================================================

#[test]
fn test_s4_1_oms_on_exec_report_and_mutants() {
    let tmp = TempDirGuard::new("s4_1");
    let state = tmp.path().join("s4_1_state.json");
    register_layer1_strata(&state, true, false);
    let st = state.to_str().unwrap();

    let good_wasm = fixture_wasm("oms_strata", "s4_1_oms_on_exec_report", false, tmp.path());
    let buggy_wasm = fixture_wasm(
        "oms_strata",
        "s4_1_oms_on_exec_report_buggy",
        false,
        tmp.path(),
    );
    let good = good_wasm.to_str().unwrap();
    let buggy = buggy_wasm.to_str().unwrap();

    // 1. ref === opt under --ignore-dead-stack
    let eq = run_cli_expect(
        &[
            "--state",
            st,
            "check-goal",
            "--candidate",
            good,
            "--candidate-entry",
            "oms_on_exec_report_opt",
            "--spec",
            good,
            "--spec-entry",
            "oms_on_exec_report_ref",
            "--pre",
            good,
            "--pre-entry",
            "req_rx_slice",
            "--ignore-dead-stack",
            "--timeout-ms",
            "15000",
        ],
        0,
    );
    assert_eq!(eq["status"], "PROVED");

    // 2. SliceFrame: RX packet bytes remain 100% untouched (writes strictly inside OMS state)
    let sf = run_cli_expect(
        &[
            "--state",
            st,
            "check-contract",
            "--entry",
            "oms_on_exec_report_opt",
            "--requires",
            "req_rx_slice",
            "--slice-frame",
            "base=1048576,len=4096",
            "--timeout-ms",
            "15000",
            good,
        ],
        0,
    );
    assert_eq!(sf["status"], "PROVED");

    // 3. No double cancel credit contract
    let ndc = run_cli_expect(
        &[
            "--state",
            st,
            "check-contract",
            "--entry",
            "contract_e2e_no_double_cancel_credit",
            "--timeout-ms",
            "15000",
            good,
        ],
        0,
    );
    assert_eq!(ndc["status"], "PROVED");

    // 4. E2E exec report preserves OMS invariant (fills during PendingCancel never dropped)
    let pres = run_cli_expect(
        &[
            "--state",
            st,
            "check-contract",
            "--entry",
            "contract_e2e_exec_report_preserves_oms",
            "--timeout-ms",
            "15000",
            good,
        ],
        0,
    );
    assert_eq!(pres["status"], "PROVED");

    // 5. Buggy mutants MUST be FALSIFIED
    let m1 = run_cli_expect(
        &[
            "--state",
            st,
            "check-contract",
            "--entry",
            "contract_e2e_exec_report_preserves_oms_buggy",
            "--timeout-ms",
            "15000",
            buggy,
        ],
        1,
    );
    assert_eq!(m1["status"], "FALSIFIED");

    let m2 = run_cli_expect(
        &[
            "--state",
            st,
            "check-contract",
            "--entry",
            "contract_e2e_no_double_cancel_credit_buggy",
            "--timeout-ms",
            "15000",
            buggy,
        ],
        1,
    );
    assert_eq!(m2["status"], "FALSIFIED");
}

// ============================================================================
// Step 4 — S4.2: E2E Tick-to-Trade + OUCH Pipeline + Mutants
// ============================================================================

#[test]
fn test_s4_2_oms_on_tick_or_order_and_mutants() {
    let tmp = TempDirGuard::new("s4_2");
    let state = tmp.path().join("s4_2_state.json");
    register_layer1_strata(&state, false, true);
    let st = state.to_str().unwrap();

    let good_wasm = fixture_wasm("oms_strata", "s4_2_oms_on_tick_or_order", true, tmp.path());
    let buggy_wasm = fixture_wasm(
        "oms_strata",
        "s4_2_oms_on_tick_or_order_buggy",
        true,
        tmp.path(),
    );
    let good = good_wasm.to_str().unwrap();
    let buggy = buggy_wasm.to_str().unwrap();

    // 1. v128 sweep_fair_v128 === sweep_fair_scalar
    let v128_eq = run_cli_expect(
        &[
            "--state",
            st,
            "check-goal",
            "--candidate",
            good,
            "--candidate-entry",
            "sweep_fair_v128",
            "--spec",
            good,
            "--spec-entry",
            "sweep_fair_scalar",
            "--timeout-ms",
            "15000",
        ],
        0,
    );
    assert_eq!(v128_eq["status"], "PROVED");

    // 2. Kill-switch tripped => returns blocked AND --slice-frame readonly (0 live memory writes)
    let ks_ro = run_cli_expect(
        &[
            "--state",
            st,
            "check-contract",
            "--entry",
            "oms_on_tick_opt",
            "--requires",
            "req_t2t_kill_switch_tripped",
            "--ensures",
            "ens_t2t_blocked",
            "--slice-frame",
            "readonly",
            "--timeout-ms",
            "15000",
            good,
        ],
        0,
    );
    assert_eq!(ks_ro["status"], "PROVED");

    // 3. Inline kill-switch blocks OUCH contract
    let ks_contract = run_cli_expect(
        &[
            "--state",
            st,
            "check-contract",
            "--entry",
            "contract_t2t_kill_switch_blocks_ouch",
            "--timeout-ms",
            "15000",
            good,
        ],
        0,
    );
    assert_eq!(ks_contract["status"], "PROVED");

    // 4. Buggy mutant: RX clobber caught by SliceFrame
    let bug_clobber = run_cli_expect(
        &[
            "--state",
            st,
            "check-contract",
            "--entry",
            "oms_on_tick_buggy_clobbers_rx",
            "--requires",
            "req_t2t_slices",
            "--slice-frame",
            "base=1048576,len=4096",
            "--timeout-ms",
            "15000",
            buggy,
        ],
        1,
    );
    assert_eq!(bug_clobber["status"], "FALSIFIED");

    // 5. Buggy mutant: crossed quote caught by inv_t2t_oms
    let bug_cross = run_cli_expect(
        &[
            "--state",
            st,
            "check-contract",
            "--entry",
            "oms_on_tick_buggy_crossed_quote",
            "--requires",
            "req_t2t_slices",
            "--invariant",
            "inv_t2t_oms",
            "--timeout-ms",
            "15000",
            buggy,
        ],
        1,
    );
    assert_eq!(bug_cross["status"], "FALSIFIED");

    // 6. Buggy mutant: kill-switch bypass caught
    let bug_ks = run_cli_expect(
        &[
            "--state",
            st,
            "check-contract",
            "--entry",
            "contract_t2t_kill_switch_blocks_ouch_buggy",
            "--timeout-ms",
            "15000",
            buggy,
        ],
        1,
    );
    assert_eq!(bug_ks["status"], "FALSIFIED");
}

// ============================================================================
// Step 4 — S4.3: Perf-Opt Pairs (check-goal + realistic profile --bench)
// ============================================================================

#[test]
fn test_s4_3_perf_opt_pairs_check_goal_and_realistic_profile_bench() {
    let p_path = oms_rs("s4_3_perf_opt_pairs");
    let p = p_path.to_str().unwrap();

    // 1. Formal bit-exact equivalence via `-t rust`
    let goal_barrett = run_cli_expect(
        &[
            "check-goal",
            "-t",
            "rust",
            "--candidate",
            p,
            "--candidate-entry",
            "oms_bucket_opt",
            "--spec",
            p,
            "--spec-entry",
            "oms_bucket_ref",
            "--pre",
            p,
            "--pre-entry",
            "req_oms_bucket",
            "--timeout-ms",
            "15000",
        ],
        0,
    );
    assert_eq!(goal_barrett["status"], "PROVED");

    let goal_swar = run_cli_expect(
        &[
            "check-goal",
            "-t",
            "rust",
            "--candidate",
            p,
            "--candidate-entry",
            "oms_fix_digits_opt",
            "--spec",
            p,
            "--spec-entry",
            "oms_fix_digits_ref",
            "--timeout-ms",
            "15000",
        ],
        0,
    );
    assert_eq!(goal_swar["status"], "PROVED");

    let goal_fsm = run_cli_expect(
        &[
            "check-goal",
            "-t",
            "rust",
            "--candidate",
            p,
            "--candidate-entry",
            "oms_risk_fsm_opt",
            "--spec",
            p,
            "--spec-entry",
            "oms_risk_fsm_ref",
            "--timeout-ms",
            "15000",
        ],
        0,
    );
    assert_eq!(goal_fsm["status"], "PROVED");

    let goal_ouch = run_cli_expect(
        &[
            "check-goal",
            "-t",
            "rust",
            "--candidate",
            p,
            "--candidate-entry",
            "oms_ouch_pack_opt",
            "--spec",
            p,
            "--spec-entry",
            "oms_ouch_pack_ref",
            "--pre",
            p,
            "--pre-entry",
            "req_oms_ouch_pack",
            "--ignore-dead-stack",
            "--timeout-ms",
            "15000",
        ],
        0,
    );
    assert_eq!(goal_ouch["status"], "PROVED");

    let goal_vwap = run_cli_expect(
        &[
            "check-goal",
            "-t",
            "rust",
            "--candidate",
            p,
            "--candidate-entry",
            "oms_vwap_vec_opt",
            "--spec",
            p,
            "--spec-entry",
            "oms_vwap_scalar_ref",
            "--pre",
            p,
            "--pre-entry",
            "req_oms_vwap",
            "--timeout-ms",
            "15000",
        ],
        0,
    );
    assert_eq!(goal_vwap["status"], "PROVED");

    // 2. Profile --compare --targets x64,arm64 --bench with realistic hot-path inputs!
    let prof_swar = run_cli_expect(
        &[
            "profile",
            p,
            "--entry",
            "oms_fix_digits_ref",
            "--opt-entry",
            "oms_fix_digits_opt",
            "--targets",
            "x64,arm64",
            "--bench",
            "--bench-preset",
            "ascii-digits",
        ],
        0,
    );
    assert_eq!(prof_swar["status"], "OK");
    assert_eq!(prof_swar["profile"]["bench_mode"], "preset:ascii-digits");
    let swar_deltas = prof_swar["comparison"]["target_deltas"].as_array().unwrap();
    assert_eq!(swar_deltas.len(), 2);
    for d in swar_deltas {
        assert!(d["branch_delta"].as_i64().unwrap() < 0, "expected branch drop: {d}");
    }
    let swar_host = prof_swar["comparison"]["host_speedup"].as_f64().unwrap();
    assert!(
        swar_host > 1.0,
        "expected realistic SWAR FIX host_speedup > 1.0, got {swar_host}"
    );

    let prof_fsm = run_cli_expect(
        &[
            "profile",
            p,
            "--entry",
            "oms_risk_fsm_ref",
            "--opt-entry",
            "oms_risk_fsm_opt",
            "--targets",
            "x64,arm64",
            "--bench",
            "--bench-preset",
            "oms-valid",
        ],
        0,
    );
    assert_eq!(prof_fsm["status"], "OK");
    assert_eq!(prof_fsm["profile"]["bench_mode"], "preset:oms-valid");
    let fsm_deltas = prof_fsm["comparison"]["target_deltas"].as_array().unwrap();
    assert_eq!(fsm_deltas.len(), 2);
    for d in fsm_deltas {
        assert!(d["branch_delta"].as_i64().unwrap() < 0, "expected FSM branch drop: {d}");
    }
    let fsm_host = prof_fsm["comparison"]["host_speedup"].as_f64().unwrap();
    assert!(
        fsm_host > 1.0,
        "expected realistic Branchless Risk FSM host_speedup > 1.0, got {fsm_host}"
    );

    let prof_ouch = run_cli_expect(
        &[
            "profile",
            p,
            "--entry",
            "oms_ouch_pack_ref",
            "--opt-entry",
            "oms_ouch_pack_opt",
            "--targets",
            "x64,arm64",
            "--bench",
            "--bench-inputs",
            r#"[[null, 64, 1001, 4702111234474983745, 1850000, 4755801464197546484], ["buf", 64, 1002, 4702111234474983745, 1850500, 5980780362835558900]]"#,
        ],
        0,
    );
    assert_eq!(prof_ouch["status"], "OK");
    assert_eq!(prof_ouch["profile"]["bench_mode"], "custom:2_tuples");
    let ouch_deltas = prof_ouch["comparison"]["target_deltas"].as_array().unwrap();
    assert_eq!(ouch_deltas.len(), 2);
    for d in ouch_deltas {
        assert!(
            d["stack_frame_delta"].as_i64().unwrap() < 0,
            "expected OUCH stack frame elimination: {d}"
        );
    }
    let ouch_host = prof_ouch["comparison"]["host_speedup"].as_f64().unwrap();
    assert!(
        ouch_host > 1.0,
        "expected realistic OUCH zero-copy host_speedup > 1.0, got {ouch_host}"
    );
}

// ============================================================================
// Step 6 — Vertical Pack 1: AI Inference (llama.cpp / GGML Q8_0 Quantization)
// ============================================================================

#[test]
fn test_vertical_pack_1_ai_q8_0_quant_and_mutants() {
    let tmp = TempDirGuard::new("vp1_ai");
    let good_w = fixture_wasm("vertical_packs", "ai_q8_0_quant", true, tmp.path());
    let buggy_w = fixture_wasm("vertical_packs", "ai_q8_0_quant_buggy", true, tmp.path());
    let good = good_w.to_str().unwrap();
    let buggy = buggy_w.to_str().unwrap();

    let eq = run_cli_expect(
        &[
            "check-goal",
            "--candidate",
            good,
            "--candidate-entry",
            "q8_0_quant_4_v128",
            "--spec",
            good,
            "--spec-entry",
            "q8_0_quant_4_ref",
            "--timeout-ms",
            "15000",
        ],
        0,
    );
    assert_eq!(eq["status"], "PROVED");

    let safe = run_cli_expect(
        &[
            "check-contract",
            good,
            "--entry",
            "q8_0_quant_4_v128",
            "--requires",
            "req_finite_block",
            "--ensures",
            "ens_q8_0_safe",
            "--timeout-ms",
            "15000",
        ],
        0,
    );
    assert_eq!(safe["status"], "PROVED");

    let inline = run_cli_expect(
        &[
            "check-contract",
            good,
            "--entry",
            "contract_q8_0_quant_4",
            "--timeout-ms",
            "15000",
        ],
        0,
    );
    assert_eq!(inline["status"], "PROVED");

    let bug_nan = run_cli_expect(
        &[
            "check-contract",
            buggy,
            "--entry",
            "q8_0_buggy_zero_nan",
            "--requires",
            "req_finite_block",
            "--ensures",
            "ens_q8_0_safe",
            "--timeout-ms",
            "15000",
        ],
        1,
    );
    assert_eq!(bug_nan["status"], "FALSIFIED");
}

// ============================================================================
// Step 6 — Vertical Pack 2: Columnar DB / Parquet Varint Slice + ZigZag
// ============================================================================

#[test]
fn test_vertical_pack_2_db_parquet_varint_slice_and_mutants() {
    let tmp = TempDirGuard::new("vp2_db");
    let good_w = fixture_wasm("vertical_packs", "db_parquet_varint_slice", false, tmp.path());
    let buggy_w = fixture_wasm(
        "vertical_packs",
        "db_parquet_varint_slice_buggy",
        false,
        tmp.path(),
    );
    let good = good_w.to_str().unwrap();
    let buggy = buggy_w.to_str().unwrap();

    let eq = run_cli_expect(
        &[
            "check-goal",
            "--candidate",
            good,
            "--candidate-entry",
            "varint_decode_opt",
            "--spec",
            good,
            "--spec-entry",
            "varint_decode_ref",
            "--pre",
            good,
            "--pre-entry",
            "req_varint_slice",
            "--ignore-dead-stack",
        ],
        0,
    );
    assert_eq!(eq["status"], "PROVED");

    let ro = run_cli_expect(
        &[
            "check-contract",
            good,
            "--entry",
            "varint_decode_opt",
            "--requires",
            "req_varint_slice",
            "--slice-frame",
            "readonly",
        ],
        0,
    );
    assert_eq!(ro["status"], "PROVED");

    let zz = run_cli_expect(
        &[
            "check-goal",
            "--candidate",
            good,
            "--candidate-entry",
            "zigzag_enc_dec_roundtrip",
            "--spec",
            good,
            "--spec-entry",
            "identity_i64",
        ],
        0,
    );
    assert_eq!(zz["status"], "PROVED");

    let br_eq = run_cli_expect(
        &[
            "check-goal",
            "--candidate",
            good,
            "--candidate-entry",
            "varint_decode_branchless_opt",
            "--spec",
            good,
            "--spec-entry",
            "varint_decode_branchy_ref",
        ],
        0,
    );
    assert_eq!(br_eq["status"], "PROVED");

    let bug_short = run_cli_expect(
        &[
            "check-contract",
            buggy,
            "--entry",
            "varint_decode_buggy_short_read",
            "--requires",
            "req_varint_slice",
        ],
        1,
    );
    assert_eq!(bug_short["status"], "FALSIFIED");

    let bug_shift = run_cli_expect(
        &[
            "check-goal",
            "--candidate",
            buggy,
            "--candidate-entry",
            "varint_decode_buggy_shift_overflow",
            "--spec",
            good,
            "--spec-entry",
            "varint_decode_ref",
            "--pre",
            good,
            "--pre-entry",
            "req_varint_slice",
            "--ignore-dead-stack",
        ],
        1,
    );
    assert_eq!(bug_shift["status"], "FALSIFIED");
}

// ============================================================================
// Step 6 — Vertical Pack 3: Networking / WireGuard RFC 6479 Anti-Replay Window
// ============================================================================

#[test]
fn test_vertical_pack_3_net_wireguard_replay_and_mutants() {
    let tmp = TempDirGuard::new("vp3_net");
    let good_w = fixture_wasm("vertical_packs", "net_wireguard_replay", false, tmp.path());
    let buggy_w = fixture_wasm(
        "vertical_packs",
        "net_wireguard_replay_buggy",
        false,
        tmp.path(),
    );
    let good = good_w.to_str().unwrap();
    let buggy = buggy_w.to_str().unwrap();

    let inv = run_cli_expect(
        &[
            "check-contract",
            good,
            "--init",
            "init_replay",
            "--ops",
            "accept_nonce",
            "--invariant",
            "inv_replay_window",
        ],
        0,
    );
    assert_eq!(inv["status"], "PROVED");

    let dup = run_cli_expect(
        &[
            "check-contract",
            good,
            "--entry",
            "contract_duplicate_always_rejected",
        ],
        0,
    );
    assert_eq!(dup["status"], "PROVED");

    let jump = run_cli_expect(
        &[
            "check-contract",
            good,
            "--entry",
            "contract_large_jump_clears_stale",
        ],
        0,
    );
    assert_eq!(jump["status"], "PROVED");

    let eq = run_cli_expect(
        &[
            "check-goal",
            "--candidate",
            good,
            "--candidate-entry",
            "replay_check_branchless",
            "--spec",
            good,
            "--spec-entry",
            "replay_check_branchy",
        ],
        0,
    );
    assert_eq!(eq["status"], "PROVED");

    let bug_jump = run_cli_expect(
        &[
            "check-contract",
            buggy,
            "--entry",
            "contract_large_jump_clears_stale",
        ],
        1,
    );
    assert_eq!(bug_jump["status"], "FALSIFIED");

    let bug_wrap = run_cli_expect(
        &[
            "check-goal",
            "--candidate",
            buggy,
            "--candidate-entry",
            "accept_nonce_buggy_shift64_wrap",
            "--spec",
            good,
            "--spec-entry",
            "accept_nonce",
        ],
        1,
    );
    assert_eq!(bug_wrap["status"], "FALSIFIED");
}

// ============================================================================
// Step 6 — Vertical Pack 4: Distributed Cloud Quota / Reservation Saga
// ============================================================================

#[test]
fn test_vertical_pack_4_cloud_quota_saga_and_mutants() {
    let tmp = TempDirGuard::new("vp4_cloud");
    let good_w = fixture_wasm("vertical_packs", "cloud_quota_saga", false, tmp.path());
    let buggy_w = fixture_wasm(
        "vertical_packs",
        "cloud_quota_saga_buggy",
        false,
        tmp.path(),
    );
    let good = good_w.to_str().unwrap();
    let buggy = buggy_w.to_str().unwrap();

    let inv = run_cli_expect(
        &[
            "check-contract",
            good,
            "--init",
            "init_quota",
            "--ops",
            "reserve,commit,cancel_reserve",
            "--invariant",
            "inv_quota_saga",
            "--timeout-ms",
            "20000",
        ],
        0,
    );
    assert_eq!(inv["status"], "PROVED");

    let no_double_commit = run_cli_expect(
        &[
            "check-contract",
            good,
            "--entry",
            "contract_no_double_commit",
            "--timeout-ms",
            "15000",
        ],
        0,
    );
    assert_eq!(no_double_commit["status"], "PROVED");

    let bug_double_rel = run_cli_expect(
        &[
            "check-contract",
            buggy,
            "--entry",
            "contract_no_double_release",
            "--timeout-ms",
            "15000",
        ],
        1,
    );
    assert_eq!(bug_double_rel["status"], "FALSIFIED");
}

// ============================================================================
// Vertical Pack 5: Cryptography / Constant-Time TLS & AEAD Security
// ============================================================================

#[test]
fn test_vertical_pack_5_crypto_ct_tls_record_and_mutants() {
    let tmp = TempDirGuard::new("vp5_crypto");
    let good_w = fixture_wasm("vertical_packs", "crypto_ct_tls_record", true, tmp.path());
    let buggy_w = fixture_wasm(
        "vertical_packs",
        "crypto_ct_tls_record_buggy",
        true,
        tmp.path(),
    );
    let good = good_w.to_str().unwrap();
    let buggy = buggy_w.to_str().unwrap();
    let rs_path = vp_rs("crypto_ct_tls_record");
    let rs = rs_path.to_str().unwrap();

    // 1. Zero-stack PKCS#7 opt === shadow-stack ref under --ignore-dead-stack
    let pkcs7_eq = run_cli_expect(
        &[
            "check-goal",
            "--candidate",
            good,
            "--candidate-entry",
            "pkcs7_unpad16_opt",
            "--spec",
            good,
            "--spec-entry",
            "pkcs7_unpad16_ref",
            "--pre",
            good,
            "--pre-entry",
            "req_block16_slice",
            "--ignore-dead-stack",
            "--timeout-ms",
            "15000",
        ],
        0,
    );
    assert_eq!(pkcs7_eq["status"], "PROVED");

    // 2. Complete RFC 5652 postcondition + SliceFrame readonly (opt & ref --ignore-dead-stack)
    let pkcs7_ro = run_cli_expect(
        &[
            "check-contract",
            good,
            "--entry",
            "pkcs7_unpad16_opt",
            "--requires",
            "req_block16_slice",
            "--ensures",
            "ens_pkcs7_unpad16",
            "--slice-frame",
            "readonly",
            "--timeout-ms",
            "15000",
        ],
        0,
    );
    assert_eq!(pkcs7_ro["status"], "PROVED");

    let pkcs7_ref_ro = run_cli_expect(
        &[
            "check-contract",
            good,
            "--entry",
            "pkcs7_unpad16_ref",
            "--requires",
            "req_block16_slice",
            "--slice-frame",
            "readonly",
            "--ignore-dead-stack",
            "--timeout-ms",
            "15000",
        ],
        0,
    );
    assert_eq!(pkcs7_ref_ro["status"], "PROVED");

    // 3. Exact constant-time SWAR branchless === branchy across all 2^128 16-byte blocks
    let ct_eq = run_cli_expect(
        &[
            "check-goal",
            "--candidate",
            good,
            "--candidate-entry",
            "pkcs7_unpad16_branchless",
            "--spec",
            good,
            "--spec-entry",
            "pkcs7_unpad16_branchy",
            "--timeout-ms",
            "15000",
        ],
        0,
    );
    assert_eq!(ct_eq["status"], "PROVED");

    // 4. 16-byte AEAD MAC SIMD equivalence + 1-bit forgery rejection
    let mac_eq = run_cli_expect(
        &[
            "check-goal",
            "--candidate",
            good,
            "--candidate-entry",
            "ct_mac16_eq_v128",
            "--spec",
            good,
            "--spec-entry",
            "ct_mac16_eq_ref",
            "--timeout-ms",
            "15000",
        ],
        0,
    );
    assert_eq!(mac_eq["status"], "PROVED");

    let mac_flip = run_cli_expect(
        &[
            "check-contract",
            good,
            "--entry",
            "contract_mac16_1bit_flip_rejected",
            "--timeout-ms",
            "15000",
        ],
        0,
    );
    assert_eq!(mac_flip["status"], "PROVED");

    // 5. RFC 8439 ChaCha20 4-lane u32x4 SIMD equivalence + 64B SliceFrame containment
    let chacha_eq = run_cli_expect(
        &[
            "check-goal",
            "--candidate",
            good,
            "--candidate-entry",
            "chacha20_col_round_v128",
            "--spec",
            good,
            "--spec-entry",
            "chacha20_col_round_ref",
            "--pre",
            good,
            "--pre-entry",
            "req_chacha_state",
            "--timeout-ms",
            "15000",
        ],
        0,
    );
    assert_eq!(chacha_eq["status"], "PROVED");

    let chacha_sf = run_cli_expect(
        &[
            "check-contract",
            good,
            "--entry",
            "chacha20_col_round_v128",
            "--requires",
            "req_chacha_state",
            "--slice-frame",
            "param:0:64",
            "--timeout-ms",
            "15000",
        ],
        0,
    );
    assert_eq!(chacha_sf["status"], "PROVED");

    // 6. All 3 cryptographic buggy mutants MUST be FALSIFIED
    let bug_pad = run_cli_expect(
        &[
            "check-contract",
            buggy,
            "--entry",
            "pkcs7_unpad16_buggy_zero_pad_oracle",
            "--requires",
            "req_block16_slice",
            "--ensures",
            "ens_pkcs7_unpad16",
            "--timeout-ms",
            "15000",
        ],
        1,
    );
    assert_eq!(bug_pad["status"], "FALSIFIED");

    let bug_mac = run_cli_expect(
        &[
            "check-contract",
            buggy,
            "--entry",
            "contract_mac16_1bit_flip_rejected",
            "--timeout-ms",
            "15000",
        ],
        1,
    );
    assert_eq!(bug_mac["status"], "FALSIFIED");

    let bug_chacha = run_cli_expect(
        &[
            "check-goal",
            "--candidate",
            buggy,
            "--candidate-entry",
            "chacha20_col_round_buggy_rot",
            "--spec",
            good,
            "--spec-entry",
            "chacha20_col_round_ref",
            "--pre",
            good,
            "--pre-entry",
            "req_chacha_state",
            "--timeout-ms",
            "15000",
        ],
        1,
    );
    assert_eq!(bug_chacha["status"], "FALSIFIED");

    // 7. Native x64 & ARM64 constant-time audit: 0 secret-dependent branches on BOTH targets!
    let prof = run_cli_expect(
        &[
            "profile",
            rs,
            "--entry",
            "pkcs7_unpad16_branchy",
            "--opt-entry",
            "pkcs7_unpad16_branchless",
            "--targets",
            "x64,arm64",
            "--bench",
            "--bench-inputs",
            r#"[["0x4142434445464748","0x04040404494a4b4c"],["0x1122334455667788","0x0808080808080808"],["0x0c0c0c0c41424344","0x0c0c0c0c0c0c0c0c"],["0x1010101010101010","0x1010101010101010"],["0x10101010101010ff","0x1010101010101010"]]"#,
        ],
        0,
    );
    assert_eq!(prof["status"], "OK");
    let opt_targets = prof["opt_profile"]["targets"].as_array().unwrap();
    assert_eq!(opt_targets.len(), 2);
    for t in opt_targets {
        assert_eq!(
            t["branch_count"].as_u64().unwrap(),
            0,
            "expected constant-time 0 branches on {}: {t}",
            t["arch"]
        );
    }
    let deltas = prof["comparison"]["target_deltas"].as_array().unwrap();
    assert_eq!(deltas.len(), 2);
    for d in deltas {
        assert!(d["branch_delta"].as_i64().unwrap() < 0, "expected branch elimination: {d}");
        assert!(d["cycle_speedup"].as_f64().unwrap() > 2.0, "expected >2x cycle speedup: {d}");
        assert!(d["rthroughput_speedup"].as_f64().unwrap() > 2.0, "expected >2x RTh speedup: {d}");
    }
    assert!(prof["opt_profile"]["host_ns_per_op"].as_f64().is_some());
}

// ============================================================================
// Vertical Pack 6: Safety-Critical Robotics / Aerospace Flight PID + 4-Motor Mixer
// ============================================================================

#[test]
fn test_vertical_pack_6_robotics_flight_pid_mixer_and_mutants() {
    let tmp = TempDirGuard::new("vp6_robotics");
    let good_w = fixture_wasm(
        "vertical_packs",
        "robotics_flight_pid_mixer",
        true,
        tmp.path(),
    );
    let buggy_w = fixture_wasm(
        "vertical_packs",
        "robotics_flight_pid_mixer_buggy",
        true,
        tmp.path(),
    );
    let good = good_w.to_str().unwrap();
    let buggy = buggy_w.to_str().unwrap();
    let rs_path = vp_rs("robotics_flight_pid_mixer");
    let rs = rs_path.to_str().unwrap();

    // 1. Inductive stateful IEEE-754 QF_ABVFP PID safety invariant
    let inv = run_cli_expect(
        &[
            "check-contract",
            good,
            "--init",
            "init_pid",
            "--ops",
            "step_pid,clear_estop",
            "--invariant",
            "inv_pid_safe",
            "--timeout-ms",
            "20000",
        ],
        0,
    );
    assert_eq!(inv["status"], "PROVED");

    // 2. E-stop dominance, NaN sensor fault isolation, and slew-rate bound
    for entry in [
        "contract_estop_forces_zero",
        "contract_nan_sensor_never_poisons",
        "contract_slew_rate_bounded",
    ] {
        let res = run_cli_expect(
            &[
                "check-contract",
                good,
                "--entry",
                entry,
                "--timeout-ms",
                "20000",
            ],
            0,
        );
        assert_eq!(res["status"], "PROVED", "failed contract {entry}");
    }

    // 3. Quadrotor 4-motor mixer: IEEE-754 2^23 magic-bias opt === v128 === scalar + safety
    let eq_v128 = run_cli_expect(
        &[
            "check-goal",
            "--candidate",
            good,
            "--candidate-entry",
            "quad_mixer_4_opt",
            "--spec",
            good,
            "--spec-entry",
            "quad_mixer_4_v128",
            "--timeout-ms",
            "15000",
        ],
        0,
    );
    assert_eq!(eq_v128["status"], "PROVED");

    let eq_scalar = run_cli_expect(
        &[
            "check-goal",
            "--candidate",
            good,
            "--candidate-entry",
            "quad_mixer_4_opt",
            "--spec",
            good,
            "--spec-entry",
            "quad_mixer_4_scalar",
            "--timeout-ms",
            "15000",
        ],
        0,
    );
    assert_eq!(eq_scalar["status"], "PROVED");

    let mixer_safe = run_cli_expect(
        &[
            "check-contract",
            good,
            "--entry",
            "quad_mixer_4_opt",
            "--ensures",
            "ens_quad_mixer_safe",
            "--timeout-ms",
            "15000",
        ],
        0,
    );
    assert_eq!(mixer_safe["status"], "PROVED");

    // 4. Buggy mutants: NaN integrator poisoning & NaN full-throttle crash MUST be FALSIFIED
    let bug_pid = run_cli_expect(
        &[
            "check-contract",
            buggy,
            "--init",
            "init_pid",
            "--ops",
            "step_pid_buggy_nan_clamp,clear_estop",
            "--invariant",
            "inv_pid_safe",
            "--timeout-ms",
            "15000",
        ],
        1,
    );
    assert_eq!(bug_pid["status"], "FALSIFIED");

    let bug_nan = run_cli_expect(
        &[
            "check-contract",
            buggy,
            "--entry",
            "contract_nan_sensor_never_poisons",
            "--timeout-ms",
            "15000",
        ],
        1,
    );
    assert_eq!(bug_nan["status"], "FALSIFIED");

    let bug_throttle = run_cli_expect(
        &[
            "check-contract",
            buggy,
            "--entry",
            "quad_mixer_buggy_nan_full_throttle",
            "--ensures",
            "ens_quad_mixer_safe",
            "--timeout-ms",
            "15000",
        ],
        1,
    );
    assert_eq!(bug_throttle["status"], "FALSIFIED");

    // 5. Native x64 & ARM64 NEON profile + host bench (also exercises LLVM 23.1 f0x normalization!)
    let prof = run_cli_expect(
        &[
            "profile",
            rs,
            "--entry",
            "quad_mixer_4_scalar",
            "--opt-entry",
            "quad_mixer_4_opt",
            "--targets",
            "x64,arm64",
            "--bench",
            "--bench-inputs",
            "[[0.65,0.08,-0.05,0.02,0],[0.50,-0.12,0.10,-0.04,0],[0.85,0.20,0.15,0.05,0],[0.20,-0.25,-0.10,0.08,0]]",
        ],
        0,
    );
    assert_eq!(prof["status"], "OK");
    for t in prof["opt_profile"]["targets"].as_array().unwrap() {
        assert_eq!(t["branch_count"].as_u64().unwrap(), 0, "expected 0 branches: {t}");
    }
    let deltas = prof["comparison"]["target_deltas"].as_array().unwrap();
    assert_eq!(deltas.len(), 2);
    for d in deltas {
        assert!(d["branch_delta"].as_i64().unwrap() < 0, "expected branch drop: {d}");
        assert!(d["rthroughput_speedup"].as_f64().unwrap() > 1.2, "expected RTh speedup: {d}");
    }
    assert!(
        prof["comparison"]["host_speedup"].as_f64().unwrap() > 1.0,
        "expected host speedup > 1.0: {}",
        prof["comparison"]
    );
}

// ============================================================================
// Vertical Pack 7: OS Kernel / Hypervisor W^X MMU & Vectorized 4-Way TLB
// ============================================================================

#[test]
fn test_vertical_pack_7_os_mmu_wx_tlb_and_mutants() {
    let tmp = TempDirGuard::new("vp7_os_mmu");
    let good_w = fixture_wasm("vertical_packs", "os_mmu_wx_tlb", true, tmp.path());
    let buggy_w = fixture_wasm("vertical_packs", "os_mmu_wx_tlb_buggy", true, tmp.path());
    let good = good_w.to_str().unwrap();
    let buggy = buggy_w.to_str().unwrap();
    let rs_path = vp_rs("os_mmu_wx_tlb");
    let rs = rs_path.to_str().unwrap();

    // 1. Inductive 4-region W^X + page alignment + zero wraparound + pairwise disjointness
    let inv = run_cli_expect(
        &[
            "check-contract",
            good,
            "--init",
            "init_mmu",
            "--ops",
            "map_region,mprotect_region,unmap_region",
            "--invariant",
            "inv_mmu_wx",
            "--timeout-ms",
            "20000",
        ],
        0,
    );
    assert_eq!(inv["status"], "PROVED");

    // 2. Global virtual-address W^X non-interference & immediate unmap revocation
    let no_wx = run_cli_expect(
        &[
            "check-contract",
            good,
            "--entry",
            "contract_no_wx_escalation",
            "--timeout-ms",
            "15000",
        ],
        0,
    );
    assert_eq!(no_wx["status"], "PROVED");

    let unmap_rev = run_cli_expect(
        &[
            "check-contract",
            good,
            "--entry",
            "contract_unmap_revokes_access",
            "--timeout-ms",
            "20000",
        ],
        0,
    );
    assert_eq!(unmap_rev["status"], "PROVED");

    // 3. 4-way TLB lookup: v128 === branchless === ref + SliceFrame readonly
    let tlb_v128 = run_cli_expect(
        &[
            "check-goal",
            "--candidate",
            good,
            "--candidate-entry",
            "tlb_check_4_v128",
            "--spec",
            good,
            "--spec-entry",
            "tlb_check_4_ref",
            "--pre",
            good,
            "--pre-entry",
            "req_tlb_tables",
            "--timeout-ms",
            "15000",
        ],
        0,
    );
    assert_eq!(tlb_v128["status"], "PROVED");

    let tlb_bl = run_cli_expect(
        &[
            "check-goal",
            "--candidate",
            good,
            "--candidate-entry",
            "tlb_check_4_branchless",
            "--spec",
            good,
            "--spec-entry",
            "tlb_check_4_ref",
            "--pre",
            good,
            "--pre-entry",
            "req_tlb_tables",
            "--timeout-ms",
            "15000",
        ],
        0,
    );
    assert_eq!(tlb_bl["status"], "PROVED");

    let tlb_ro = run_cli_expect(
        &[
            "check-contract",
            good,
            "--entry",
            "tlb_check_4_branchless",
            "--requires",
            "req_tlb_tables",
            "--slice-frame",
            "readonly",
            "--timeout-ms",
            "15000",
        ],
        0,
    );
    assert_eq!(tlb_ro["status"], "PROVED");

    let tlb_v128_ro = run_cli_expect(
        &[
            "check-contract",
            good,
            "--entry",
            "tlb_check_4_v128",
            "--requires",
            "req_tlb_tables",
            "--slice-frame",
            "readonly",
            "--timeout-ms",
            "15000",
        ],
        0,
    );
    assert_eq!(tlb_v128_ro["status"], "PROVED");

    // 4. All 3 OS kernel CVE mutants MUST be FALSIFIED
    let bug_wrap = run_cli_expect(
        &[
            "check-contract",
            buggy,
            "--init",
            "init_mmu",
            "--ops",
            "map_region_buggy_wrap_overlap,unmap_region",
            "--invariant",
            "inv_mmu_wx",
            "--timeout-ms",
            "15000",
        ],
        1,
    );
    assert_eq!(bug_wrap["status"], "FALSIFIED");

    let bug_wx = run_cli_expect(
        &[
            "check-contract",
            buggy,
            "--entry",
            "contract_no_wx_escalation",
            "--timeout-ms",
            "15000",
        ],
        1,
    );
    assert_eq!(bug_wx["status"], "FALSIFIED");

    let bug_signed = run_cli_expect(
        &[
            "check-goal",
            "--candidate",
            buggy,
            "--candidate-entry",
            "tlb_check_4_buggy_signed_cmp",
            "--spec",
            good,
            "--spec-entry",
            "tlb_check_4_ref",
            "--pre",
            good,
            "--pre-entry",
            "req_tlb_tables",
            "--timeout-ms",
            "15000",
        ],
        1,
    );
    assert_eq!(bug_signed["status"], "FALSIFIED");

    // 5. Native x64 (AVX2) & ARM64 (NEON) 4-way parallel TLB profile + host bench
    let prof = run_cli_expect(
        &[
            "profile",
            rs,
            "--entry",
            "tlb_check_4_ref",
            "--opt-entry",
            "tlb_check_4_branchless",
            "--targets",
            "x64,arm64",
            "--bench",
            "--bench-inputs",
            "[[[4096,65536,131072,262144],[4096,8192,16384,32768],[5,3,1,5],266240,4],[[4096,65536,131072,262144],[4096,8192,16384,32768],[5,3,1,5],135168,1],[[4096,65536,131072,262144],[4096,8192,16384,32768],[5,3,1,5],524288,1],[[4096,65536,131072,262144],[4096,8192,16384,32768],[5,3,1,5],270336,2]]",
        ],
        0,
    );
    assert_eq!(prof["status"], "OK");
    for t in prof["opt_profile"]["targets"].as_array().unwrap() {
        assert_eq!(t["branch_count"].as_u64().unwrap(), 0, "expected 0 branches: {t}");
        assert!(t["simd_count"].as_u64().unwrap() > 0, "expected SIMD/NEON vectorization: {t}");
    }
    let deltas = prof["comparison"]["target_deltas"].as_array().unwrap();
    assert_eq!(deltas.len(), 2);
    for d in deltas {
        assert!(d["branch_delta"].as_i64().unwrap() < 0, "expected branch drop: {d}");
        assert!(d["simd_delta"].as_i64().unwrap() > 0, "expected SIMD gain: {d}");
        assert!(d["rthroughput_speedup"].as_f64().unwrap() > 1.5, "expected RTh speedup: {d}");
    }
    assert!(prof["opt_profile"]["host_ns_per_op"].as_f64().is_some());
}

// ============================================================================
// Regression E2E: LLVM 23.1 -> 23.0 IR Float Literal Normalization in Profiler
// ============================================================================

#[test]
fn test_profiler_llvm23_1_float_literal_normalization_e2e() {
    let tmp = TempDirGuard::new("prof_llvm23_fp");
    let src_path = tmp.path().join("llvm23_fp_edge_cases.rs");
    let src = r#"#![no_std]

#[unsafe(no_mangle)]
pub static ESCAPED_BS: [u8; 4] = *b"foo\\";

#[unsafe(no_mangle)]
pub extern "C" fn f32_all_edge_literals(x: f32) -> f32 {
    let a = x + 0.1f32;
    let b = a + 8_388_608.0f32;
    let c = b + f32::from_bits(1);
    if c < f32::INFINITY && c > f32::NEG_INFINITY {
        c + f32::MAX
    } else if c == f32::INFINITY {
        f32::from_bits(0x7FC0_1234)
    } else if c == f32::NEG_INFINITY {
        f32::from_bits(0x7F80_0001)
    } else {
        f32::NAN
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn f64_all_edge_literals(x: f64) -> f64 {
    let a = x + 3.141592653589793f64;
    let b = a + f64::from_bits(1);
    if b < f64::INFINITY && b > f64::NEG_INFINITY {
        b + f64::MAX
    } else if b == f64::INFINITY {
        f64::from_bits(0x7FF8_0000_0000_1234)
    } else {
        f64::from_bits(0x7FF0_0000_0000_0001)
    }
}
"#;
    std::fs::write(&src_path, src).expect("write llvm23_fp_edge_cases.rs");
    let p = src_path.to_str().unwrap();

    for entry in ["f32_all_edge_literals", "f64_all_edge_literals"] {
        let prof = run_cli_expect(
            &["profile", p, "--entry", entry, "--targets", "x64,arm64"],
            0,
        );
        assert_eq!(prof["status"], "OK", "profile failed for {entry}: {prof}");
        let targets = prof["profile"]["targets"].as_array().unwrap();
        assert_eq!(targets.len(), 2, "expected x64+arm64 for {entry}: {prof}");
        for t in targets {
            assert!(
                t["instruction_count"].as_u64().unwrap() > 0,
                "expected non-empty asm for {entry}: {t}"
            );
        }
    }
}
