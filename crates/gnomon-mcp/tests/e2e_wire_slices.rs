use std::io::{BufRead, BufReader, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use gnomon_kernel::{MemId, ValId};
use gnomon_mcp::{SliceFrameParam, parse_slice_frame_spec};
use gnomon_sieve::{SliceBoundExpr, SliceFrameSpec};
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

fn oms_rs(name: &str) -> PathBuf {
    repo_root()
        .join("examples")
        .join("oms_strata")
        .join(format!("{name}.rs"))
}

fn run_cli(args: &[&str]) -> (i32, Value, String) {
    let out = Command::new(gnomon_bin())
        .args(args)
        .output()
        .expect("failed to execute gnomon CLI");
    let code = out.status.code().unwrap_or(-1);
    let stderr = String::from_utf8_lossy(&out.stderr).to_string();
    let stdout = String::from_utf8_lossy(&out.stdout).to_string();
    let json = if stdout.trim().is_empty() {
        Value::Null
    } else {
        serde_json::from_str(&stdout).unwrap_or_else(|e| {
            panic!("invalid JSON from `gnomon {}`: {e}\nstdout={stdout}\nstderr={stderr}", args.join(" "))
        })
    };
    (code, json, stderr)
}

#[test]
fn test_slice_frame_parser_and_mcp_param_validation() {
    assert_eq!(
        parse_slice_frame_spec("readonly").unwrap(),
        SliceFrameSpec {
            mem: MemId(0),
            base: SliceBoundExpr::Const(0),
            len: SliceBoundExpr::Const(0),
        }
    );
    assert_eq!(
        parse_slice_frame_spec("mem=1,readonly").unwrap(),
        SliceFrameSpec {
            mem: MemId(1),
            base: SliceBoundExpr::Const(0),
            len: SliceBoundExpr::Const(0),
        }
    );
    assert_eq!(
        parse_slice_frame_spec("base=param:2,len=32").unwrap(),
        SliceFrameSpec {
            mem: MemId(0),
            base: SliceBoundExpr::Param(ValId(2)),
            len: SliceBoundExpr::Const(32),
        }
    );
    assert_eq!(
        parse_slice_frame_spec("mem=0,base=param:0,len=param:1").unwrap(),
        SliceFrameSpec {
            mem: MemId(0),
            base: SliceBoundExpr::Param(ValId(0)),
            len: SliceBoundExpr::Param(ValId(1)),
        }
    );
    assert_eq!(
        parse_slice_frame_spec("param:2:32").unwrap(),
        SliceFrameSpec {
            mem: MemId(0),
            base: SliceBoundExpr::Param(ValId(2)),
            len: SliceBoundExpr::Const(32),
        }
    );
    assert_eq!(
        parse_slice_frame_spec("param:0:param:1").unwrap(),
        SliceFrameSpec {
            mem: MemId(0),
            base: SliceBoundExpr::Param(ValId(0)),
            len: SliceBoundExpr::Param(ValId(1)),
        }
    );
    assert_eq!(
        parse_slice_frame_spec("base=0x100040,len=0x20").unwrap(),
        SliceFrameSpec {
            mem: MemId(0),
            base: SliceBoundExpr::Const(0x10_0040),
            len: SliceBoundExpr::Const(0x20),
        }
    );

    // Invalid CLI specs must fail cleanly with crisp diagnostics
    for bad in [
        "",
        "base=param:2",
        "len=32",
        "readonly,base=param:0,len=32",
        "mem=0,foo=1,base=0,len=1",
        "base=param:x,len=32",
        "base=0,base=1,len=4",
        "param:2",
    ] {
        assert!(
            parse_slice_frame_spec(bad).is_err(),
            "expected parse_slice_frame_spec({bad:?}) to fail"
        );
    }

    // MCP SliceFrameParam validation
    assert_eq!(
        SliceFrameParam { readonly: true, ..Default::default() }
            .into_spec()
            .unwrap(),
        SliceFrameSpec {
            mem: MemId(0),
            base: SliceBoundExpr::Const(0),
            len: SliceBoundExpr::Const(0),
        }
    );
    assert_eq!(
        SliceFrameParam {
            mem: 0,
            base_param: Some(2),
            len_const: Some(32),
            ..Default::default()
        }
        .into_spec()
        .unwrap(),
        SliceFrameSpec {
            mem: MemId(0),
            base: SliceBoundExpr::Param(ValId(2)),
            len: SliceBoundExpr::Const(32),
        }
    );
    assert!(
        SliceFrameParam {
            readonly: true,
            base_param: Some(0),
            ..Default::default()
        }
        .into_spec()
        .is_err()
    );
    assert!(
        SliceFrameParam {
            base_param: Some(0),
            base_const: Some(0),
            len_const: Some(4),
            ..Default::default()
        }
        .into_spec()
        .is_err()
    );

    // CLI rejects malformed `--slice-frame` with exit code 2
    let s2_3 = oms_rs("s2_3_wire_rx_decode");
    let (code, _, stderr) = run_cli(&[
        "-t",
        "rust",
        "check-contract",
        s2_3.to_str().unwrap(),
        "--entry",
        "itch_validate_header",
        "--slice-frame",
        "bad=spec",
    ]);
    assert_eq!(code, 2, "expected exit code 2 for invalid --slice-frame; stderr={stderr}");
    assert!(stderr.contains("invalid --slice-frame"), "stderr={stderr}");
}

#[test]
fn test_s2_3_wire_rx_decode_cli_rust_e2e() {
    let clean = oms_rs("s2_3_wire_rx_decode");
    let buggy = oms_rs("s2_3_wire_rx_decode_buggy");
    let clean_s = clean.to_str().unwrap();
    let buggy_s = buggy.to_str().unwrap();

    // 1. `itch_decode_ref` vs `itch_decode_opt` under `req_itch_decode`:
    //    WITHOUT `--ignore-dead-stack` -> FALSIFIED (dirty dead stack bytes below SP_in)
    let (code, v, stderr) = run_cli(&[
        "-t",
        "rust",
        "check-goal",
        "--candidate",
        clean_s,
        "--candidate-entry",
        "itch_decode_ref",
        "--spec",
        clean_s,
        "--spec-entry",
        "itch_decode_opt",
        "--pre",
        clean_s,
        "--pre-entry",
        "req_itch_decode",
        "--timeout-ms",
        "15000",
    ]);
    assert_eq!(code, 1, "expected FALSIFIED without --ignore-dead-stack: v={v} stderr={stderr}");
    assert_eq!(v["status"], "FALSIFIED");
    assert!(v["counterexample"].is_object());

    // 2. `itch_decode_ref` vs `itch_decode_opt` under `req_itch_decode`:
    //    WITH `--ignore-dead-stack` -> PROVED!
    let (code, v, stderr) = run_cli(&[
        "-t",
        "rust",
        "check-goal",
        "--candidate",
        clean_s,
        "--candidate-entry",
        "itch_decode_ref",
        "--spec",
        clean_s,
        "--spec-entry",
        "itch_decode_opt",
        "--pre",
        clean_s,
        "--pre-entry",
        "req_itch_decode",
        "--ignore-dead-stack",
        "--timeout-ms",
        "15000",
    ]);
    assert_eq!(code, 0, "expected PROVED with --ignore-dead-stack: v={v} stderr={stderr}");
    assert_eq!(v["status"], "PROVED");
    assert!(v["cliff_warnings"].is_array());

    // 3. `itch_validate_header` with `--slice-frame readonly` under `req_itch_validate` -> PROVED!
    let (code, v, stderr) = run_cli(&[
        "-t",
        "rust",
        "check-contract",
        clean_s,
        "--entry",
        "itch_validate_header",
        "--requires",
        "req_itch_validate",
        "--slice-frame",
        "readonly",
        "--timeout-ms",
        "15000",
    ]);
    assert_eq!(code, 0, "itch_validate_header readonly failed: v={v} stderr={stderr}");
    assert_eq!(v["status"], "PROVED");

    // 4. `itch_decode_opt` with `--ignore-dead-stack --slice-frame base=param:2,len=32` -> PROVED!
    let (code, v, stderr) = run_cli(&[
        "-t",
        "rust",
        "check-contract",
        clean_s,
        "--entry",
        "itch_decode_opt",
        "--requires",
        "req_itch_decode",
        "--ignore-dead-stack",
        "--slice-frame",
        "base=param:2,len=32",
        "--timeout-ms",
        "15000",
    ]);
    assert_eq!(code, 0, "itch_decode_opt SliceFrame failed: v={v} stderr={stderr}");
    assert_eq!(v["status"], "PROVED");

    // 5. `itch_decode_ref` with `--ignore-dead-stack --slice-frame param:2:32` (shorthand) -> PROVED!
    let (code, v, stderr) = run_cli(&[
        "-t",
        "rust",
        "check-contract",
        clean_s,
        "--entry",
        "itch_decode_ref",
        "--requires",
        "req_itch_decode",
        "--ignore-dead-stack",
        "--slice-frame",
        "param:2:32",
        "--timeout-ms",
        "15000",
    ]);
    assert_eq!(code, 0, "itch_decode_ref SliceFrame failed: v={v} stderr={stderr}");
    assert_eq!(v["status"], "PROVED");

    // 6. Mutant 1: `itch_decode_buggy_short_pkt` -> trap-freedom FALSIFIED!
    let (code, v, stderr) = run_cli(&[
        "-t",
        "rust",
        "check-contract",
        buggy_s,
        "--entry",
        "itch_decode_buggy_short_pkt",
        "--requires",
        "req_itch_decode",
        "--timeout-ms",
        "15000",
    ]);
    assert_eq!(code, 1, "itch_decode_buggy_short_pkt must be FALSIFIED: v={v} stderr={stderr}");
    assert_eq!(v["status"], "FALSIFIED");
    assert!(v["counterexample"].is_object());

    // 7. Mutant 2: `itch_decode_buggy_endian` vs `itch_decode_opt` -> equiv FALSIFIED!
    let (code, v, stderr) = run_cli(&[
        "-t",
        "rust",
        "check-goal",
        "--candidate",
        buggy_s,
        "--candidate-entry",
        "itch_decode_buggy_endian",
        "--spec",
        clean_s,
        "--spec-entry",
        "itch_decode_opt",
        "--pre",
        clean_s,
        "--pre-entry",
        "req_itch_decode",
        "--timeout-ms",
        "15000",
    ]);
    assert_eq!(code, 1, "itch_decode_buggy_endian equiv must be FALSIFIED: v={v} stderr={stderr}");
    assert_eq!(v["status"], "FALSIFIED");
    assert!(v["counterexample"].is_object());

    // 8. Mutant 3: `itch_decode_buggy_clobber_rx` -> `SliceFrame([out_ptr, out_ptr + 32))` FALSIFIED!
    let (code, v, stderr) = run_cli(&[
        "-t",
        "rust",
        "check-contract",
        buggy_s,
        "--entry",
        "itch_decode_buggy_clobber_rx",
        "--requires",
        "req_itch_decode",
        "--slice-frame",
        "base=param:2,len=32",
        "--timeout-ms",
        "15000",
    ]);
    assert_eq!(code, 1, "itch_decode_buggy_clobber_rx SliceFrame must be FALSIFIED: v={v} stderr={stderr}");
    assert_eq!(v["status"], "FALSIFIED");
    assert!(
        !v["counterexample"]["memory_bytes"]
            .as_array()
            .unwrap()
            .is_empty(),
        "expected memory_bytes witness for clobber_rx: {v}"
    );
}

#[test]
fn test_s2_4_wire_tx_encode_cli_rust_e2e() {
    let clean = oms_rs("s2_4_wire_tx_encode");
    let buggy = oms_rs("s2_4_wire_tx_encode_buggy");
    let clean_s = clean.to_str().unwrap();
    let buggy_s = buggy.to_str().unwrap();

    // 1. `ouch_encode_ref` vs `ouch_encode_opt` under `req_ouch_encode`:
    //    WITHOUT `--ignore-dead-stack` -> FALSIFIED!
    let (code, v, stderr) = run_cli(&[
        "-t",
        "rust",
        "check-goal",
        "--candidate",
        clean_s,
        "--candidate-entry",
        "ouch_encode_ref",
        "--spec",
        clean_s,
        "--spec-entry",
        "ouch_encode_opt",
        "--pre",
        clean_s,
        "--pre-entry",
        "req_ouch_encode",
        "--timeout-ms",
        "15000",
    ]);
    assert_eq!(code, 1, "expected FALSIFIED without --ignore-dead-stack: v={v} stderr={stderr}");
    assert_eq!(v["status"], "FALSIFIED");
    assert!(v["counterexample"].is_object());

    // 2. `ouch_encode_ref` vs `ouch_encode_opt` under `req_ouch_encode`:
    //    WITH `--ignore-dead-stack` -> PROVED!
    let (code, v, stderr) = run_cli(&[
        "-t",
        "rust",
        "check-goal",
        "--candidate",
        clean_s,
        "--candidate-entry",
        "ouch_encode_ref",
        "--spec",
        clean_s,
        "--spec-entry",
        "ouch_encode_opt",
        "--pre",
        clean_s,
        "--pre-entry",
        "req_ouch_encode",
        "--ignore-dead-stack",
        "--timeout-ms",
        "15000",
    ]);
    assert_eq!(code, 0, "expected PROVED with --ignore-dead-stack: v={v} stderr={stderr}");
    assert_eq!(v["status"], "PROVED");

    // 3. `ouch_encode_opt` with `--ignore-dead-stack --slice-frame base=param:0,len=48` -> PROVED!
    let (code, v, stderr) = run_cli(&[
        "-t",
        "rust",
        "check-contract",
        clean_s,
        "--entry",
        "ouch_encode_opt",
        "--requires",
        "req_ouch_encode",
        "--ignore-dead-stack",
        "--slice-frame",
        "base=param:0,len=48",
        "--timeout-ms",
        "15000",
    ]);
    assert_eq!(code, 0, "ouch_encode_opt SliceFrame failed: v={v} stderr={stderr}");
    assert_eq!(v["status"], "PROVED");

    // 4. `ouch_encode_ref` with `--ignore-dead-stack --slice-frame mem=0,base=param:0,len=48` -> PROVED!
    let (code, v, stderr) = run_cli(&[
        "-t",
        "rust",
        "check-contract",
        clean_s,
        "--entry",
        "ouch_encode_ref",
        "--requires",
        "req_ouch_encode",
        "--ignore-dead-stack",
        "--slice-frame",
        "mem=0,base=param:0,len=48",
        "--timeout-ms",
        "15000",
    ]);
    assert_eq!(code, 0, "ouch_encode_ref SliceFrame failed: v={v} stderr={stderr}");
    assert_eq!(v["status"], "PROVED");

    // 5. Mutant 1: `ouch_encode_buggy_overrun` -> `SliceFrame([tx_ptr, tx_ptr + 48))` FALSIFIED!
    let (code, v, stderr) = run_cli(&[
        "-t",
        "rust",
        "check-contract",
        buggy_s,
        "--entry",
        "ouch_encode_buggy_overrun",
        "--requires",
        "req_ouch_encode",
        "--slice-frame",
        "base=param:0,len=48",
        "--timeout-ms",
        "15000",
    ]);
    assert_eq!(code, 1, "ouch_encode_buggy_overrun SliceFrame must be FALSIFIED: v={v} stderr={stderr}");
    assert_eq!(v["status"], "FALSIFIED");
    assert!(
        !v["counterexample"]["memory_bytes"]
            .as_array()
            .unwrap()
            .is_empty(),
        "expected memory_bytes witness for overrun: {v}"
    );

    // 6. Mutant 2: `ouch_encode_buggy_endian` vs `ouch_encode_opt` -> equiv FALSIFIED!
    let (code, v, stderr) = run_cli(&[
        "-t",
        "rust",
        "check-goal",
        "--candidate",
        buggy_s,
        "--candidate-entry",
        "ouch_encode_buggy_endian",
        "--spec",
        clean_s,
        "--spec-entry",
        "ouch_encode_opt",
        "--pre",
        clean_s,
        "--pre-entry",
        "req_ouch_encode",
        "--timeout-ms",
        "15000",
    ]);
    assert_eq!(code, 1, "ouch_encode_buggy_endian equiv must be FALSIFIED: v={v} stderr={stderr}");
    assert_eq!(v["status"], "FALSIFIED");
    assert!(v["counterexample"].is_object());

    // 7. Mutant 3: `ouch_encode_buggy_short_buf` -> trap-freedom FALSIFIED!
    let (code, v, stderr) = run_cli(&[
        "-t",
        "rust",
        "check-contract",
        buggy_s,
        "--entry",
        "ouch_encode_buggy_short_buf",
        "--requires",
        "req_ouch_encode",
        "--timeout-ms",
        "15000",
    ]);
    assert_eq!(code, 1, "ouch_encode_buggy_short_buf trap-freedom must be FALSIFIED: v={v} stderr={stderr}");
    assert_eq!(v["status"], "FALSIFIED");
    assert!(v["counterexample"].is_object());
}

#[test]
fn test_static_smt_cliff_warnings_across_lift_goal_and_contract() {
    // 1. Existing OMS fixture `s1_3_order_id_mix.rs` (64-bit fmix64 mul chain)
    let mix_rs = oms_rs("s1_3_order_id_mix");
    let (code, v, stderr) = run_cli(&["-t", "rust", "lift", mix_rs.to_str().unwrap()]);
    assert_eq!(code, 0, "lift s1_3_order_id_mix failed: v={v} stderr={stderr}");
    assert!(v["cliff_report"].is_object(), "missing cliff_report: {v}");
    let level = v["cliff_report"]["level"].as_str().unwrap();
    assert!(
        level == "Medium" || level == "High",
        "expected Medium/High cliff on s1_3_order_id_mix, got {level}: {v}"
    );
    let warnings = v["cliff_warnings"].as_array().unwrap();
    assert!(
        !warnings.is_empty(),
        "expected non-empty cliff_warnings on s1_3_order_id_mix: {v}"
    );

    // 2. High-cliff fixture with deep 64-bit nonlinear chain (depth >= 3)
    let tmp_dir = std::env::temp_dir().join(format!(
        "gnomon_cliff_e2e_{}_{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    std::fs::create_dir_all(&tmp_dir).unwrap();
    let high_cliff_rs = tmp_dir.join("high_cliff.rs");
    std::fs::write(
        &high_cliff_rs,
        r#"#![no_std]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

#[unsafe(no_mangle)]
pub extern "C" fn deep_mix64(x: i64) -> i64 {
    let mut z = x as u64;
    z ^= z >> 33;
    z = z.wrapping_mul(0xff51_afd7_ed55_8ccd);
    z ^= z >> 33;
    z = z.wrapping_mul(0xc4ce_b9fe_1a85_ec53);
    z ^= z >> 33;
    z = z.wrapping_mul(0x9e37_79b9_7f4a_7c15);
    z ^= z >> 33;
    z as i64
}
"#,
    )
    .unwrap();

    let rs_s = high_cliff_rs.to_str().unwrap();
    let (code, lift_v, stderr) = run_cli(&["-t", "rust", "lift", rs_s]);
    assert_eq!(code, 0, "lift high_cliff.rs failed: stderr={stderr}");
    assert_eq!(lift_v["cliff_report"]["level"], "High", "lift_v={lift_v}");
    assert!(
        lift_v["cliff_report"]["max_nonlinear64_chain_depth"]
            .as_u64()
            .unwrap()
            >= 3
    );
    assert!(
        !lift_v["cliff_warnings"].as_array().unwrap().is_empty(),
        "expected cliff_warnings in lift: {lift_v}"
    );

    // `check-goal` (reflexive) also surfaces `cliff_warnings`
    let (code, goal_v, stderr) = run_cli(&[
        "-t",
        "rust",
        "check-goal",
        "--candidate",
        rs_s,
        "--candidate-entry",
        "deep_mix64",
        "--spec",
        rs_s,
        "--spec-entry",
        "deep_mix64",
    ]);
    assert_eq!(code, 0, "reflexive check-goal failed: goal_v={goal_v} stderr={stderr}");
    assert_eq!(goal_v["status"], "PROVED");
    assert!(
        !goal_v["cliff_warnings"].as_array().unwrap().is_empty(),
        "expected cliff_warnings in check-goal: {goal_v}"
    );

    // `check-contract` (trap-freedom) also surfaces `cliff_warnings`
    let (code, cc_v, stderr) = run_cli(&[
        "-t",
        "rust",
        "check-contract",
        rs_s,
        "--entry",
        "deep_mix64",
    ]);
    assert_eq!(code, 0, "check-contract deep_mix64 failed: cc_v={cc_v} stderr={stderr}");
    assert_eq!(cc_v["status"], "PROVED");
    assert!(
        !cc_v["cliff_warnings"].as_array().unwrap().is_empty(),
        "expected cliff_warnings in check-contract: {cc_v}"
    );

    let _ = std::fs::remove_dir_all(&tmp_dir);
}

#[test]
fn test_s2_3_and_s2_4_wire_slices_via_mcp_stdio() {
    let s2_3 = oms_rs("s2_3_wire_rx_decode");
    let s2_3_buggy = oms_rs("s2_3_wire_rx_decode_buggy");
    let s2_4 = oms_rs("s2_4_wire_tx_encode");
    let s2_4_buggy = oms_rs("s2_4_wire_tx_encode_buggy");
    let s1_3 = oms_rs("s1_3_order_id_mix");

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
        assert!(!resp_line.trim().is_empty(), "MCP server closed stdout unexpectedly");
        serde_json::from_str(&resp_line)
            .unwrap_or_else(|e| panic!("corrupted JSON-RPC stdout '{resp_line}': {e}"))
    };

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
                "clientInfo": { "name": "wire-e2e", "version": "0.1.0" }
            }
        }),
    );
    let instructions = init_resp["result"]["instructions"].as_str().unwrap();
    assert!(instructions.contains("ignore_dead_stack"), "instructions={instructions}");
    assert!(instructions.contains("slice_frame"), "instructions={instructions}");
    assert!(instructions.contains("cliff"), "instructions={instructions}");

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

    fn path_str(p: &Path) -> &str {
        p.to_str().unwrap()
    }

    // 1. gnomon_lift_check emits cliff_report + cliff_warnings on s1_3_order_id_mix.rs
    let lift = call_tool(
        &mut stdin,
        &mut reader,
        2,
        "gnomon_lift_check",
        json!({ "path": path_str(&s1_3), "input_type": "rust" }),
    );
    assert!(lift["cliff_report"].is_object());
    assert!(!lift["cliff_warnings"].as_array().unwrap().is_empty());

    // 2. S2.3 gnomon_check_goal: FALSIFIED without ignore_dead_stack, PROVED with ignore_dead_stack
    let s23_no_sr = call_tool(
        &mut stdin,
        &mut reader,
        3,
        "gnomon_check_goal",
        json!({
            "candidate_path": path_str(&s2_3),
            "candidate_entry": "itch_decode_ref",
            "spec_path": path_str(&s2_3),
            "spec_entry": "itch_decode_opt",
            "pre_path": path_str(&s2_3),
            "pre_entry": "req_itch_decode",
            "input_type": "rust",
            "timeout_ms": 15000
        }),
    );
    assert_eq!(s23_no_sr["status"], "FALSIFIED", "s23_no_sr={s23_no_sr}");

    let s23_sr = call_tool(
        &mut stdin,
        &mut reader,
        4,
        "gnomon_check_goal",
        json!({
            "candidate_path": path_str(&s2_3),
            "candidate_entry": "itch_decode_ref",
            "spec_path": path_str(&s2_3),
            "spec_entry": "itch_decode_opt",
            "pre_path": path_str(&s2_3),
            "pre_entry": "req_itch_decode",
            "input_type": "rust",
            "ignore_dead_stack": true,
            "timeout_ms": 15000
        }),
    );
    assert_eq!(s23_sr["status"], "PROVED", "s23_sr={s23_sr}");

    // 3. S2.3 gnomon_check_contract: readonly + SliceFrame + clobber mutant
    let s23_ro = call_tool(
        &mut stdin,
        &mut reader,
        5,
        "gnomon_check_contract",
        json!({
            "path": path_str(&s2_3),
            "input_type": "rust",
            "entry": "itch_validate_header",
            "requires": "req_itch_validate",
            "slice_frame": { "readonly": true },
            "timeout_ms": 15000
        }),
    );
    assert_eq!(s23_ro["status"], "PROVED", "s23_ro={s23_ro}");

    let s23_ref_sf = call_tool(
        &mut stdin,
        &mut reader,
        6,
        "gnomon_check_contract",
        json!({
            "path": path_str(&s2_3),
            "input_type": "rust",
            "entry": "itch_decode_ref",
            "requires": "req_itch_decode",
            "ignore_dead_stack": true,
            "slice_frame": { "mem": 0, "base_param": 2, "len_const": 32 },
            "timeout_ms": 15000
        }),
    );
    assert_eq!(s23_ref_sf["status"], "PROVED", "s23_ref_sf={s23_ref_sf}");

    let s23_clobber = call_tool(
        &mut stdin,
        &mut reader,
        7,
        "gnomon_check_contract",
        json!({
            "path": path_str(&s2_3_buggy),
            "input_type": "rust",
            "entry": "itch_decode_buggy_clobber_rx",
            "requires": "req_itch_decode",
            "slice_frame": { "base_param": 2, "len_const": 32 },
            "timeout_ms": 15000
        }),
    );
    assert_eq!(s23_clobber["status"], "FALSIFIED", "s23_clobber={s23_clobber}");

    // 4. S2.4 gnomon_check_goal: FALSIFIED without ignore_dead_stack, PROVED with ignore_dead_stack
    let s24_no_sr = call_tool(
        &mut stdin,
        &mut reader,
        8,
        "gnomon_check_goal",
        json!({
            "candidate_path": path_str(&s2_4),
            "candidate_entry": "ouch_encode_ref",
            "spec_path": path_str(&s2_4),
            "spec_entry": "ouch_encode_opt",
            "pre_path": path_str(&s2_4),
            "pre_entry": "req_ouch_encode",
            "input_type": "rust",
            "timeout_ms": 15000
        }),
    );
    assert_eq!(s24_no_sr["status"], "FALSIFIED", "s24_no_sr={s24_no_sr}");

    let s24_sr = call_tool(
        &mut stdin,
        &mut reader,
        9,
        "gnomon_check_goal",
        json!({
            "candidate_path": path_str(&s2_4),
            "candidate_entry": "ouch_encode_ref",
            "spec_path": path_str(&s2_4),
            "spec_entry": "ouch_encode_opt",
            "pre_path": path_str(&s2_4),
            "pre_entry": "req_ouch_encode",
            "input_type": "rust",
            "ignore_dead_stack": true,
            "timeout_ms": 15000
        }),
    );
    assert_eq!(s24_sr["status"], "PROVED", "s24_sr={s24_sr}");

    // 5. S2.4 gnomon_check_contract: SliceFrame PROVED + overrun mutant FALSIFIED
    let s24_ref_sf = call_tool(
        &mut stdin,
        &mut reader,
        10,
        "gnomon_check_contract",
        json!({
            "path": path_str(&s2_4),
            "input_type": "rust",
            "entry": "ouch_encode_ref",
            "requires": "req_ouch_encode",
            "ignore_dead_stack": true,
            "slice_frame": { "mem": 0, "base_param": 0, "len_const": 48 },
            "timeout_ms": 15000
        }),
    );
    assert_eq!(s24_ref_sf["status"], "PROVED", "s24_ref_sf={s24_ref_sf}");

    let s24_overrun = call_tool(
        &mut stdin,
        &mut reader,
        11,
        "gnomon_check_contract",
        json!({
            "path": path_str(&s2_4_buggy),
            "input_type": "rust",
            "entry": "ouch_encode_buggy_overrun",
            "requires": "req_ouch_encode",
            "slice_frame": { "base_param": 0, "len_const": 48 },
            "timeout_ms": 15000
        }),
    );
    assert_eq!(s24_overrun["status"], "FALSIFIED", "s24_overrun={s24_overrun}");

    drop(stdin);
    let status = child.wait().unwrap();
    assert!(status.success());
}
