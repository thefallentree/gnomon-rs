use std::io::{BufRead, BufReader, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use gnomon_mcp::{
    CheckContractRequest, ContractPred, GnomonEngine, InputType, load_artifact_bytes,
};
use serde_json::{Value, json};

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

fn temp_dir(tag: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "gnomon_oms_e2e_{tag}_{}_{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// Resolves a pre-built OMS Strata `.wasm` fixture under `examples/oms_strata/out/`, or
/// compiles it into `fallback_dir` with `rustc --target wasm32-unknown-unknown` if absent.
fn oms_fixture_wasm(name: &str, fallback_dir: &Path) -> PathBuf {
    let oms_dir = repo_root().join("examples").join("oms_strata");
    let prebuilt = oms_dir.join("out").join(format!("{name}.wasm"));
    if prebuilt.is_file() {
        return prebuilt;
    }
    let src = oms_dir.join(format!("{name}.rs"));
    let out = fallback_dir.join(format!("{name}.wasm"));
    let status = Command::new("rustc")
        .args([
            "--target",
            "wasm32-unknown-unknown",
            "--crate-type=cdylib",
            "-O",
            "-C",
            "panic=abort",
            "--edition",
            "2024",
        ])
        .arg(&src)
        .arg("-o")
        .arg(&out)
        .status()
        .expect("failed to invoke rustc for wasm32 fixture");
    assert!(status.success(), "rustc failed compiling {}", src.display());
    out
}

fn load_wasm_artifact(path: &Path) -> gnomon_mcp::LoadedArtifact {
    let bytes = std::fs::read(path).unwrap();
    load_artifact_bytes(&bytes, InputType::Wasm, path.to_str())
        .unwrap()
        .1
}

#[test]
fn test_oms_s1_1_notional_and_price_collar_engine_and_cli() {
    let dir = temp_dir("s1_1");
    let wasm_path = oms_fixture_wasm("s1_1_notional_collar", &dir);
    let art = load_wasm_artifact(&wasm_path);
    let eng = GnomonEngine::new();

    // 1. Engine checks on all 5 S1.1 targets
    let cases: &[(&str, &str, &str, &str)] = &[
        ("checked_notional", "req_notional", "ens_notional", "PROVED"),
        (
            "checked_notional_buggy_overflow",
            "req_notional",
            "ens_notional",
            "FALSIFIED",
        ),
        (
            "price_collar_ok",
            "req_price_collar",
            "ens_price_collar",
            "PROVED",
        ),
        (
            "price_collar_buggy_div0",
            "req_price_collar",
            "ens_price_collar",
            "FALSIFIED",
        ),
        (
            "price_collar_buggy_overflow",
            "req_price_collar",
            "ens_price_collar",
            "FALSIFIED",
        ),
    ];

    for &(entry, req, ens, expected_status) in cases {
        let out = eng
            .check_contract(CheckContractRequest {
                artifact: Some(art.clone()),
                entry: Some(entry.into()),
                requires: Some(ContractPred::FuncName(req.into())),
                ensures: Some(ContractPred::FuncName(ens.into())),
                timeout_ms: 15_000,
                ..CheckContractRequest::default()
            })
            .unwrap_or_else(|e| panic!("engine check_contract failed on {entry}: {e}"));
        assert_eq!(
            out.status, expected_status,
            "engine S1.1 {entry}: expected {expected_status}, got {out:?}"
        );
        assert_eq!(out.mode, "single");
        assert_eq!(out.entry.as_deref(), Some(entry));
        if expected_status == "FALSIFIED" {
            let cex = out
                .counterexample
                .as_ref()
                .expect("FALSIFIED contract must include counterexample");
            assert_eq!(
                cex.scalar_values.len(),
                3,
                "expected 3 scalar params in counterexample for {entry}: {cex:?}"
            );
        } else {
            assert!(out.counterexample.is_none());
        }
    }

    // 2. CLI checks on all 5 S1.1 targets (verifying exit codes 0 vs 1 and JSON schema)
    for &(entry, req, ens, expected_status) in cases {
        let output = Command::new(gnomon_bin())
            .args([
                "check-contract",
                wasm_path.to_str().unwrap(),
                "--entry",
                entry,
                "--requires",
                req,
                "--ensures",
                ens,
                "--timeout-ms",
                "15000",
            ])
            .output()
            .unwrap();
        let expected_code = if expected_status == "PROVED" { 0 } else { 1 };
        assert_eq!(
            output.status.code(),
            Some(expected_code),
            "CLI S1.1 {entry}: stdout={} stderr={}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        let v: Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(v["status"], expected_status);
        assert_eq!(v["entry"], entry);
        if expected_status == "FALSIFIED" {
            assert!(v["counterexample"]["scalar_values"].is_array());
            assert!(v["counterexample"]["global_values"].is_array());
            assert!(v["counterexample"]["memory_bytes"].is_array());
        }
    }

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn test_oms_s3_1_child_fsm_inductive_suite_harnesses_and_buggy_mutants() {
    let dir = temp_dir("s3_1");
    let clean_wasm = oms_fixture_wasm("s3_1_child_fsm", &dir);
    let buggy_wasm = oms_fixture_wasm("s3_1_child_fsm_buggy", &dir);
    let clean_art = load_wasm_artifact(&clean_wasm);
    let buggy_art = load_wasm_artifact(&buggy_wasm);
    let eng = GnomonEngine::new();

    let all_ops = [
        "submit_new",
        "on_ack",
        "request_cancel",
        "request_replace",
        "on_fill",
        "on_cancel_ack",
        "on_replace_ack",
        "on_reject",
    ];

    // 1. Engine inductive multi-op suite on clean S3.1 FSM -> PROVED (1 init + 8 ops)
    let suite_out = eng
        .check_contract(CheckContractRequest {
            artifact: Some(clean_art.clone()),
            init: Some("init_empty".into()),
            ops: all_ops.iter().map(|s| (*s).to_string()).collect(),
            invariant: Some(ContractPred::FuncName("inv_child_fsm".into())),
            timeout_ms: 15_000,
            ..CheckContractRequest::default()
        })
        .unwrap();
    assert_eq!(suite_out.status, "PROVED", "suite_out: {suite_out:?}");
    assert_eq!(suite_out.mode, "inductive_suite");
    assert_eq!(suite_out.op_results.len(), 9);
    assert_eq!(suite_out.op_results[0].entry, "init_empty");
    assert_eq!(suite_out.op_results[0].role, "init");
    assert!(suite_out.op_results[0].use_initial_state);
    assert_eq!(suite_out.op_results[0].status, "PROVED");
    for (idx, op_name) in all_ops.iter().enumerate() {
        let r = &suite_out.op_results[idx + 1];
        assert_eq!(r.entry, *op_name);
        assert_eq!(r.role, "op");
        assert!(!r.use_initial_state);
        assert_eq!(r.status, "PROVED");
    }

    // 2. CLI inductive suite on clean S3.1 FSM -> exit 0, PROVED
    let cli_suite = Command::new(gnomon_bin())
        .args([
            "check-contract",
            clean_wasm.to_str().unwrap(),
            "--init",
            "init_empty",
            "--ops",
            &all_ops.join(","),
            "--invariant",
            "inv_child_fsm",
            "--timeout-ms",
            "15000",
        ])
        .output()
        .unwrap();
    assert_eq!(
        cli_suite.status.code(),
        Some(0),
        "stdout={} stderr={}",
        String::from_utf8_lossy(&cli_suite.stdout),
        String::from_utf8_lossy(&cli_suite.stderr)
    );
    let sv: Value = serde_json::from_slice(&cli_suite.stdout).unwrap();
    assert_eq!(sv["status"], "PROVED");
    assert_eq!(sv["mode"], "inductive_suite");
    assert_eq!(sv["op_results"].as_array().unwrap().len(), 9);

    // 3. CLI single-op `--init-state` check on `init_empty` -> PROVED
    let cli_init = Command::new(gnomon_bin())
        .args([
            "check-contract",
            clean_wasm.to_str().unwrap(),
            "--entry",
            "init_empty",
            "--invariant",
            "inv_child_fsm",
            "--init-state",
        ])
        .output()
        .unwrap();
    assert_eq!(cli_init.status.code(), Some(0));
    let iv: Value = serde_json::from_slice(&cli_init.stdout).unwrap();
    assert_eq!(iv["status"], "PROVED");
    assert_eq!(iv["use_initial_state"], true);

    // 4. All 3 clean inline relational harnesses -> PROVED (via CLI)
    for harness in [
        "contract_fill_during_pending_cancel",
        "contract_no_terminal_resurrection",
        "contract_replace_pessimistic_exposure",
    ] {
        let out = Command::new(gnomon_bin())
            .args([
                "check-contract",
                clean_wasm.to_str().unwrap(),
                "--entry",
                harness,
                "--timeout-ms",
                "15000",
            ])
            .output()
            .unwrap();
        assert_eq!(
            out.status.code(),
            Some(0),
            "clean harness {harness}: stdout={} stderr={}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        let v: Value = serde_json::from_slice(&out.stdout).unwrap();
        assert_eq!(v["status"], "PROVED");
    }

    // 5. All 3 buggy inline relational harnesses in `s3_1_child_fsm_buggy.wasm` -> FALSIFIED (exit 1)
    for buggy_harness in [
        "contract_fill_during_pending_cancel_buggy",
        "contract_no_terminal_resurrection_buggy",
        "contract_replace_pessimistic_exposure_buggy",
    ] {
        let out = Command::new(gnomon_bin())
            .args([
                "check-contract",
                buggy_wasm.to_str().unwrap(),
                "--entry",
                buggy_harness,
                "--timeout-ms",
                "15000",
            ])
            .output()
            .unwrap();
        assert_eq!(
            out.status.code(),
            Some(1),
            "buggy harness {buggy_harness}: stdout={} stderr={}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        let v: Value = serde_json::from_slice(&out.stdout).unwrap();
        assert_eq!(v["status"], "FALSIFIED");
        assert!(v["counterexample"].is_object());
        assert!(
            !v["counterexample"]["memory_bytes"]
                .as_array()
                .unwrap()
                .is_empty(),
            "expected memory_bytes counterexample witness for stateful mutant {buggy_harness}: {v}"
        );
    }

    // 6. Buggy inductive suite: `request_replace_buggy_optimistic_leaves` violates `inv_child_fsm`
    let buggy_suite = eng
        .check_contract(CheckContractRequest {
            artifact: Some(buggy_art),
            init: Some("init_empty".into()),
            ops: vec![
                "submit_new".into(),
                "request_replace_buggy_optimistic_leaves".into(),
            ],
            invariant: Some(ContractPred::FuncName("inv_child_fsm".into())),
            timeout_ms: 15_000,
            ..CheckContractRequest::default()
        })
        .unwrap();
    assert_eq!(buggy_suite.status, "FALSIFIED");
    assert_eq!(buggy_suite.op_results.len(), 3);
    assert_eq!(buggy_suite.op_results[0].status, "PROVED");
    assert_eq!(buggy_suite.op_results[1].status, "PROVED");
    assert_eq!(buggy_suite.op_results[2].status, "FALSIFIED");
    assert!(buggy_suite.counterexample.is_some());

    // 7. `--state` active-module fallback without passing INPUT to `check-contract`
    let state = dir.join("state.json");
    let lift_out = Command::new(gnomon_bin())
        .args(["--state", state.to_str().unwrap(), "lift"])
        .arg(&clean_wasm)
        .output()
        .unwrap();
    assert_eq!(lift_out.status.code(), Some(0));

    let state_cc = Command::new(gnomon_bin())
        .args([
            "--state",
            state.to_str().unwrap(),
            "check-contract",
            "--entry",
            "contract_fill_during_pending_cancel",
        ])
        .stdin(Stdio::null())
        .output()
        .unwrap();
    assert_eq!(
        state_cc.status.code(),
        Some(0),
        "stdout={} stderr={}",
        String::from_utf8_lossy(&state_cc.stdout),
        String::from_utf8_lossy(&state_cc.stderr)
    );
    let scv: Value = serde_json::from_slice(&state_cc.stdout).unwrap();
    assert_eq!(scv["status"], "PROVED");

    // 8. Negative CLI gates: invalid args / missing function -> exit code 2
    let bad_fn = Command::new(gnomon_bin())
        .args([
            "check-contract",
            clean_wasm.to_str().unwrap(),
            "--entry",
            "does_not_exist",
        ])
        .output()
        .unwrap();
    assert_eq!(bad_fn.status.code(), Some(2));

    let bad_combo = Command::new(gnomon_bin())
        .args([
            "check-contract",
            clean_wasm.to_str().unwrap(),
            "--entry",
            "submit_new",
            "--ops",
            "on_ack",
        ])
        .output()
        .unwrap();
    assert_eq!(bad_combo.status.code(), Some(2));

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn test_oms_strata_e2e_via_mcp_stdio_gnomon_check_contract() {
    let dir = temp_dir("mcp_oms");
    let s1_wasm = oms_fixture_wasm("s1_1_notional_collar", &dir);
    let s3_wasm = oms_fixture_wasm("s3_1_child_fsm", &dir);
    let s3_buggy_wasm = oms_fixture_wasm("s3_1_child_fsm_buggy", &dir);

    let mut child = Command::new(gnomon_bin())
        .arg("mcp")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();

    let mut stdin = child.stdin.take().unwrap();
    let stdout = child.stdout.take().unwrap();
    let mut reader = BufReader::new(stdout);

    let send_recv = |stdin: &mut std::process::ChildStdin,
                     reader: &mut BufReader<std::process::ChildStdout>,
                     msg: Value|
     -> Value {
        let line = serde_json::to_string(&msg).unwrap();
        writeln!(stdin, "{line}").unwrap();
        stdin.flush().unwrap();
        let mut resp_line = String::new();
        reader.read_line(&mut resp_line).unwrap();
        assert!(
            !resp_line.trim().is_empty(),
            "MCP server closed stdout unexpectedly"
        );
        serde_json::from_str(&resp_line)
            .unwrap_or_else(|e| panic!("corrupted JSON-RPC stdout '{resp_line}': {e}"))
    };

    // Initialize and verify server instructions mention gnomon_check_contract
    let init_resp = send_recv(
        &mut stdin,
        &mut reader,
        json!({
            "jsonrpc": "2.0",
            "id": 1,
            "method": "initialize",
            "params": {
                "protocolVersion": "2024-11-05",
                "capabilities": {},
                "clientInfo": { "name": "oms-e2e", "version": "0.1.0" }
            }
        }),
    );
    assert!(
        init_resp["result"]["instructions"]
            .as_str()
            .unwrap()
            .contains("gnomon_check_contract")
    );
    writeln!(
        stdin,
        "{}",
        json!({ "jsonrpc": "2.0", "method": "notifications/initialized" })
    )
    .unwrap();
    stdin.flush().unwrap();

    let call_tool = |stdin: &mut std::process::ChildStdin,
                     reader: &mut BufReader<std::process::ChildStdout>,
                     id: u64,
                     name: &str,
                     args: Value|
     -> Value {
        let resp = send_recv(
            stdin,
            reader,
            json!({
                "jsonrpc": "2.0",
                "id": id,
                "method": "tools/call",
                "params": { "name": name, "arguments": args }
            }),
        );
        assert!(resp["error"].is_null(), "MCP tool '{name}' failed: {resp}");
        let text = resp["result"]["content"][0]["text"].as_str().unwrap();
        serde_json::from_str(text).unwrap()
    };

    // 1. S1.1 checked_notional PROVED + buggy_overflow FALSIFIED
    let s1_ok = call_tool(
        &mut stdin,
        &mut reader,
        2,
        "gnomon_check_contract",
        json!({
            "path": s1_wasm.to_str().unwrap(),
            "entry": "checked_notional",
            "requires": "req_notional",
            "ensures": "ens_notional",
            "timeout_ms": 15000
        }),
    );
    assert_eq!(s1_ok["status"], "PROVED");

    let s1_bug = call_tool(
        &mut stdin,
        &mut reader,
        3,
        "gnomon_check_contract",
        json!({
            "path": s1_wasm.to_str().unwrap(),
            "entry": "checked_notional_buggy_overflow",
            "requires": "req_notional",
            "ensures": "ens_notional",
            "timeout_ms": 15000
        }),
    );
    assert_eq!(s1_bug["status"], "FALSIFIED");
    assert_eq!(
        s1_bug["counterexample"]["scalar_values"]
            .as_array()
            .unwrap()
            .len(),
        3
    );

    // 2. S3.1 full inductive suite PROVED via MCP
    let s3_suite = call_tool(
        &mut stdin,
        &mut reader,
        4,
        "gnomon_check_contract",
        json!({
            "path": s3_wasm.to_str().unwrap(),
            "init": "init_empty",
            "ops": [
                "submit_new",
                "on_ack",
                "request_cancel",
                "request_replace",
                "on_fill",
                "on_cancel_ack",
                "on_replace_ack",
                "on_reject"
            ],
            "invariant": "inv_child_fsm",
            "timeout_ms": 15000
        }),
    );
    assert_eq!(s3_suite["status"], "PROVED", "s3_suite: {s3_suite}");
    assert_eq!(s3_suite["mode"], "inductive_suite");
    assert_eq!(s3_suite["op_results"].as_array().unwrap().len(), 9);

    // 3. S3.1 buggy mutant FALSIFIED via MCP
    let s3_bug = call_tool(
        &mut stdin,
        &mut reader,
        5,
        "gnomon_check_contract",
        json!({
            "path": s3_buggy_wasm.to_str().unwrap(),
            "entry": "contract_no_terminal_resurrection_buggy",
            "timeout_ms": 15000
        }),
    );
    assert_eq!(s3_bug["status"], "FALSIFIED", "s3_bug: {s3_bug}");
    assert!(s3_bug["counterexample"].is_object());

    drop(stdin);
    let status = child.wait().unwrap();
    assert!(status.success());
    let _ = std::fs::remove_dir_all(&dir);
}
