use std::io::{BufRead, BufReader, Write};
use std::path::PathBuf;
use std::process::{Command, Stdio};

use base64::Engine as _;
use gnomon_kernel::{
    BinOp, CallTarget, EffectOp, FuncDef, FuncId, MemId, MemWidth, MemoryDef, Module, Op, Region,
    StratumId, ValId, ValType,
};
use gnomon_mcp::{IrDocument, MCP_TOOL_NAMES};
use gnomon_wasm::emit_wasm;
use serde_json::{Value, json};

fn gnomon_bin() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_gnomon"))
}

fn temp_dir(tag: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "gnomon_e2e_{tag}_{}_{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

fn build_sample_wasm_div_mod() -> Vec<u8> {
    // fn entry(a: i32, b: i32) -> i32 { a / b }
    let body = Region::build(|b| {
        b.push_let(ValId(2), ValType::I32, Op::Bin(BinOp::I32DivS, ValId(0), ValId(1)));
        b.push_yield(&[ValId(2)]);
    });
    let m = Module {
        memories: Vec::new(),
        globals: Vec::new(),
        funcs: vec![FuncDef {
            id: FuncId(0),
            name: "entry".into(),
            export_name: Some("entry".into()),
            params: vec![(ValId(0), ValType::I32), (ValId(1), ValType::I32)],
            results: vec![ValType::I32],
            body,
        }],
        host_contracts: Vec::new(),
        memory_exports: Vec::new(),
        global_exports: Vec::new(),
    };
    emit_wasm(&m).unwrap()
}

fn wrap_inc_body_ir() -> String {
    // wrap_inc(x, mask) = (x + 1) & mask
    let body = Region::build(|b| {
        b.push_let(ValId(2), ValType::I32, Op::ConstI32(1));
        b.push_let(ValId(3), ValType::I32, Op::Bin(BinOp::I32Add, ValId(0), ValId(2)));
        b.push_let(ValId(4), ValType::I32, Op::Bin(BinOp::I32And, ValId(3), ValId(1)));
        b.push_yield(&[ValId(4)]);
    });
    let doc = IrDocument::from_region(
        &[(ValId(0), ValType::I32), (ValId(1), ValType::I32)],
        &[ValType::I32],
        &body,
    );
    serde_json::to_string_pretty(&doc).unwrap()
}

fn unused_op_body_ir() -> String {
    // mix_xor(x, y) = (x ^ y) + x
    let body = Region::build(|b| {
        b.push_let(ValId(2), ValType::I32, Op::Bin(BinOp::I32Xor, ValId(0), ValId(1)));
        b.push_let(ValId(3), ValType::I32, Op::Bin(BinOp::I32Add, ValId(2), ValId(0)));
        b.push_yield(&[ValId(3)]);
    });
    let doc = IrDocument::from_region(
        &[(ValId(0), ValType::I32), (ValId(1), ValType::I32)],
        &[ValType::I32],
        &body,
    );
    serde_json::to_string_pretty(&doc).unwrap()
}

fn region_ir(params: &[(ValId, ValType)], results: &[ValType], reg: &Region) -> String {
    serde_json::to_string_pretty(&IrDocument::from_region(params, results, reg)).unwrap()
}

#[test]
fn test_cli_e2e_wasm_ir_files_and_stdin_with_t_flag() {
    let dir = temp_dir("cli_io");
    let wasm_bytes = build_sample_wasm_div_mod();
    let wasm_path = dir.join("div.wasm");
    std::fs::write(&wasm_path, &wasm_bytes).unwrap();

    // 1. CLI lift -t wasm <file.wasm> --emit-ir
    let out = Command::new(gnomon_bin())
        .args(["lift", "-t", "wasm", "--emit-ir"])
        .arg(&wasm_path)
        .output()
        .unwrap();
    assert!(out.status.success(), "stderr: {}", String::from_utf8_lossy(&out.stderr));
    let v: Value = serde_json::from_slice(&out.stdout).unwrap();
    assert_eq!(v["input_type"], "wasm");
    assert_eq!(v["artifact_kind"], "module");
    assert_eq!(v["roundtrip_wasm_valid"], true);
    assert_eq!(v["functions"][0]["name"], "entry");
    let ir_json = serde_json::to_string_pretty(&v["ir"]).unwrap();
    let ir_path = dir.join("div.ir");
    std::fs::write(&ir_path, &ir_json).unwrap();

    // 2. CLI lift -t wasm via STDIN (piped raw .wasm binary)
    let mut child = Command::new(gnomon_bin())
        .args(["lift", "-t", "wasm", "-"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child.stdin.as_mut().unwrap().write_all(&wasm_bytes).unwrap();
    let out = child.wait_with_output().unwrap();
    assert!(out.status.success(), "stderr: {}", String::from_utf8_lossy(&out.stderr));
    let v: Value = serde_json::from_slice(&out.stdout).unwrap();
    assert_eq!(v["input_type"], "wasm");
    assert_eq!(v["roundtrip_wasm_valid"], true);

    // 3. CLI lift -t ir <file.ir>
    let out = Command::new(gnomon_bin())
        .args(["lift", "-t", "ir"])
        .arg(&ir_path)
        .output()
        .unwrap();
    assert!(out.status.success(), "stderr: {}", String::from_utf8_lossy(&out.stderr));
    let v: Value = serde_json::from_slice(&out.stdout).unwrap();
    assert_eq!(v["input_type"], "ir");
    assert_eq!(v["functions"][0]["name"], "entry");

    // 4. CLI lift -t ir via STDIN (omitted path reads stdin)
    let mut child = Command::new(gnomon_bin())
        .args(["lift", "-t", "ir"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child.stdin.as_mut().unwrap().write_all(ir_json.as_bytes()).unwrap();
    let out = child.wait_with_output().unwrap();
    assert!(out.status.success(), "stderr: {}", String::from_utf8_lossy(&out.stderr));
    let v: Value = serde_json::from_slice(&out.stdout).unwrap();
    assert_eq!(v["input_type"], "ir");

    // 5. CLI auto-detection (-t auto default) on both .wasm and .ir files
    let out_w = Command::new(gnomon_bin()).args(["lift"]).arg(&wasm_path).output().unwrap();
    assert!(out_w.status.success());
    let vw: Value = serde_json::from_slice(&out_w.stdout).unwrap();
    assert_eq!(vw["input_type"], "wasm");

    let out_i = Command::new(gnomon_bin()).args(["lift"]).arg(&ir_path).output().unwrap();
    assert!(out_i.status.success());
    let vi: Value = serde_json::from_slice(&out_i.stdout).unwrap();
    assert_eq!(vi["input_type"], "ir");

    // 6. CLI trace -t wasm: concrete OK and DivByZero trap
    let out_ok = Command::new(gnomon_bin())
        .args([
            "trace",
            "-t",
            "wasm",
            "--inputs",
            r#"[{"ty":"i32","val":42},{"ty":"i32","val":6}]"#,
        ])
        .arg(&wasm_path)
        .output()
        .unwrap();
    assert!(out_ok.status.success());
    let vok: Value = serde_json::from_slice(&out_ok.stdout).unwrap();
    assert_eq!(vok["status"], "OK");
    assert_eq!(vok["outputs"][0]["val"], 7);

    let out_trap = Command::new(gnomon_bin())
        .args([
            "trace",
            "-t",
            "wasm",
            "--inputs",
            r#"[{"ty":"i32","val":42},{"ty":"i32","val":0}]"#,
        ])
        .arg(&wasm_path)
        .output()
        .unwrap();
    assert!(!out_trap.status.success());
    let vtrap: Value = serde_json::from_slice(&out_trap.stdout).unwrap();
    assert_eq!(vtrap["status"], "TRAP");
    assert_eq!(vtrap["trap"], "div_by_zero");

    // 7. CLI trace -t ir via stdin with memory store diff
    let mem_mod = Module {
        memories: vec![MemoryDef {
            id: MemId(0),
            min_pages: 1,
            max_pages: Some(1),
            init_data: Vec::new(),
        }],
        globals: Vec::new(),
        funcs: vec![FuncDef {
            id: FuncId(0),
            name: "write_byte".into(),
            export_name: Some("write_byte".into()),
            params: vec![(ValId(0), ValType::I32), (ValId(1), ValType::I32)],
            results: Vec::new(),
            body: Region::build(|b| {
                b.push_effect(EffectOp::Store {
                    mem: MemId(0),
                    addr: ValId(0),
                    offset: 0,
                    width: MemWidth::B1,
                    val: ValId(1),
                });
                b.push_yield(&[]);
            }),
        }],
        host_contracts: Vec::new(),
        memory_exports: Vec::new(),
        global_exports: Vec::new(),
    };
    let mem_ir = serde_json::to_string(&IrDocument::from_module(&mem_mod)).unwrap();
    let mut child = Command::new(gnomon_bin())
        .args([
            "trace",
            "-t",
            "ir",
            "--inputs",
            r#"[{"ty":"i32","val":16},{"ty":"i32","val":171}]"#,
        ])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child.stdin.as_mut().unwrap().write_all(mem_ir.as_bytes()).unwrap();
    let out = child.wait_with_output().unwrap();
    assert!(out.status.success(), "stderr: {}", String::from_utf8_lossy(&out.stderr));
    let vmem: Value = serde_json::from_slice(&out.stdout).unwrap();
    assert_eq!(vmem["status"], "OK");
    assert_eq!(vmem["memory_diff"][0]["mem_id"], 0);
    assert_eq!(vmem["memory_diff"][0]["offset"], 16);
    assert_eq!(vmem["memory_diff"][0]["after"], 171);

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn test_cli_e2e_full_sieve_flywheel_workflow() {
    let dir = temp_dir("cli_flywheel");
    let state = dir.join("state.json");
    let params2 = [(ValId(0), ValType::I32), (ValId(1), ValType::I32)];

    let op1_path = dir.join("wrap_inc.ir");
    std::fs::write(&op1_path, wrap_inc_body_ir()).unwrap();
    let op2_path = dir.join("mix_xor.ir");
    std::fs::write(&op2_path, unused_op_body_ir()).unwrap();

    // 1. define-op wrap_inc (id=1) & mix_xor (id=2)
    let out = Command::new(gnomon_bin())
        .args([
            "--state",
            state.to_str().unwrap(),
            "-t",
            "ir",
            "define-op",
            "--name",
            "wrap_inc",
            "--layer",
            "1",
            "--doc",
            "Ring index increment modulo mask",
        ])
        .arg(&op1_path)
        .output()
        .unwrap();
    assert!(out.status.success(), "stderr: {}", String::from_utf8_lossy(&out.stderr));
    let v: Value = serde_json::from_slice(&out.stdout).unwrap();
    assert_eq!(v["stratum_id"], 1);
    assert_eq!(v["status"], "CANDIDATE_REGISTERED");

    let out = Command::new(gnomon_bin())
        .args([
            "--state",
            state.to_str().unwrap(),
            "-t",
            "ir",
            "define-op",
            "--name",
            "mix_xor",
            "--layer",
            "1",
        ])
        .arg(&op2_path)
        .output()
        .unwrap();
    assert!(out.status.success());

    // 2. prove-law: valid primary law `wrap_inc(x, m) & m == wrap_inc(x, m)`
    let lhs_primary = Region::build(|b| {
        b.push_call(
            &[(ValId(2), ValType::I32)],
            CallTarget::Stratum(StratumId(1)),
            &[ValId(0), ValId(1)],
        );
        b.push_let(ValId(3), ValType::I32, Op::Bin(BinOp::I32And, ValId(2), ValId(1)));
        b.push_yield(&[ValId(3)]);
    });
    let rhs_primary = Region::build(|b| {
        b.push_call(
            &[(ValId(2), ValType::I32)],
            CallTarget::Stratum(StratumId(1)),
            &[ValId(0), ValId(1)],
        );
        b.push_yield(&[ValId(2)]);
    });
    let lhs_p_path = dir.join("lhs_p.ir");
    let rhs_p_path = dir.join("rhs_p.ir");
    std::fs::write(&lhs_p_path, region_ir(&params2, &[ValType::I32], &lhs_primary)).unwrap();
    std::fs::write(&rhs_p_path, region_ir(&params2, &[ValType::I32], &rhs_primary)).unwrap();

    let out = Command::new(gnomon_bin())
        .args([
            "--state",
            state.to_str().unwrap(),
            "-t",
            "ir",
            "prove-law",
            "--op",
            "wrap_inc",
            "--name",
            "wrap_inc_mask_idem",
            "--lhs",
            lhs_p_path.to_str().unwrap(),
            "--rhs",
            rhs_p_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(out.status.success(), "stderr: {}", String::from_utf8_lossy(&out.stderr));
    let v: Value = serde_json::from_slice(&out.stdout).unwrap();
    assert_eq!(v["status"], "PROVED");
    assert_eq!(v["stage"], "stage3_kernel_admitted");
    assert!(v["proof_digest_hex"].as_str().unwrap().len() == 64);

    // 3. prove-law: buggy law `wrap_inc(x, m) == x` must be FALSIFIED at Stage-1!
    let buggy_rhs_path = dir.join("buggy_rhs.ir");
    std::fs::write(
        &buggy_rhs_path,
        region_ir(&params2, &[ValType::I32], &Region::yield_vals(&[ValId(0)])),
    )
    .unwrap();
    let out = Command::new(gnomon_bin())
        .args([
            "--state",
            state.to_str().unwrap(),
            "-t",
            "ir",
            "prove-law",
            "--op",
            "wrap_inc",
            "--name",
            "buggy_law",
            "--lhs",
            rhs_p_path.to_str().unwrap(),
            "--rhs",
            buggy_rhs_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(!out.status.success());
    let v: Value = serde_json::from_slice(&out.stdout).unwrap();
    assert_eq!(v["status"], "FALSIFIED");
    assert!(v["counterexample"].is_object());

    // 4. prove-law: redundant double-mask law on wrap_inc + 1 law on mix_xor
    let lhs_red = Region::build(|b| {
        b.push_call(
            &[(ValId(2), ValType::I32)],
            CallTarget::Stratum(StratumId(1)),
            &[ValId(0), ValId(1)],
        );
        b.push_let(ValId(3), ValType::I32, Op::Bin(BinOp::I32And, ValId(2), ValId(1)));
        b.push_let(ValId(4), ValType::I32, Op::Bin(BinOp::I32And, ValId(3), ValId(1)));
        b.push_yield(&[ValId(4)]);
    });
    let lhs_red_path = dir.join("lhs_red.ir");
    std::fs::write(&lhs_red_path, region_ir(&params2, &[ValType::I32], &lhs_red)).unwrap();
    let out = Command::new(gnomon_bin())
        .args([
            "--state",
            state.to_str().unwrap(),
            "-t",
            "ir",
            "prove-law",
            "--op",
            "wrap_inc",
            "--name",
            "wrap_inc_double_mask_redundant",
            "--lhs",
            lhs_red_path.to_str().unwrap(),
            "--rhs",
            rhs_p_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(out.status.success());

    let mix_lhs = Region::build(|b| {
        b.push_call(
            &[(ValId(2), ValType::I32)],
            CallTarget::Stratum(StratumId(2)),
            &[ValId(0), ValId(1)],
        );
        b.push_let(ValId(3), ValType::I32, Op::ConstI32(0));
        b.push_let(ValId(4), ValType::I32, Op::Bin(BinOp::I32Xor, ValId(2), ValId(3)));
        b.push_yield(&[ValId(4)]);
    });
    let mix_rhs = Region::build(|b| {
        b.push_call(
            &[(ValId(2), ValType::I32)],
            CallTarget::Stratum(StratumId(2)),
            &[ValId(0), ValId(1)],
        );
        b.push_yield(&[ValId(2)]);
    });
    let mix_l_path = dir.join("mix_l.ir");
    let mix_r_path = dir.join("mix_r.ir");
    std::fs::write(&mix_l_path, region_ir(&params2, &[ValType::I32], &mix_lhs)).unwrap();
    std::fs::write(&mix_r_path, region_ir(&params2, &[ValType::I32], &mix_rhs)).unwrap();
    let out = Command::new(gnomon_bin())
        .args([
            "--state",
            state.to_str().unwrap(),
            "-t",
            "ir",
            "prove-law",
            "--op",
            "mix_xor",
            "--name",
            "mix_xor_zero",
            "--lhs",
            mix_l_path.to_str().unwrap(),
            "--rhs",
            mix_r_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(out.status.success());

    // 5. check-goal twice with solutions using wrap_inc -> PROVED + law fires!
    let out1 = Command::new(gnomon_bin())
        .args([
            "--state",
            state.to_str().unwrap(),
            "-t",
            "ir",
            "check-goal",
            "--candidate",
            lhs_p_path.to_str().unwrap(),
            "--spec",
            rhs_p_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(out1.status.success(), "stderr: {}", String::from_utf8_lossy(&out1.stderr));
    let v1: Value = serde_json::from_slice(&out1.stdout).unwrap();
    assert_eq!(v1["status"], "PROVED");
    assert!(
        v1["laws_fired"]
            .as_array()
            .unwrap()
            .iter()
            .any(|x| x.as_str().unwrap().contains("wrap_inc")),
        "expected wrap_inc law to fire, got: {v1}"
    );

    let out2 = Command::new(gnomon_bin())
        .args([
            "--state",
            state.to_str().unwrap(),
            "-t",
            "ir",
            "check-goal",
            "--candidate",
            lhs_red_path.to_str().unwrap(),
            "--spec",
            rhs_p_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(out2.status.success());

    // 6. consolidate: keeps wrap_inc (2 solutions), prunes mix_xor (0 solutions) and redundant law!
    let out_c = Command::new(gnomon_bin())
        .args(["--state", state.to_str().unwrap(), "consolidate"])
        .output()
        .unwrap();
    assert!(out_c.status.success(), "stderr: {}", String::from_utf8_lossy(&out_c.stderr));
    let vc: Value = serde_json::from_slice(&out_c.stdout).unwrap();
    assert_eq!(vc["kept_strata"], json!([1]));
    assert_eq!(vc["pruned_strata"], json!([2]));
    assert_eq!(vc["kept_laws"], 1);
    assert!(vc["autodoc_markdown"].as_str().unwrap().contains("wrap_inc"));
    assert!(!vc["autodoc_markdown"].as_str().unwrap().contains("mix_xor"));

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn test_mcp_e2e_stdio_jsonrpc_all_6_tools() {
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

    // 1. initialize
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
                "clientInfo": { "name": "e2e-test", "version": "0.1.0" }
            }
        }),
    );
    assert_eq!(init_resp["id"], 1);
    assert_eq!(init_resp["result"]["serverInfo"]["name"], "gnomon");

    // 2. notifications/initialized (no response expected)
    writeln!(
        stdin,
        "{}",
        json!({ "jsonrpc": "2.0", "method": "notifications/initialized" })
    )
    .unwrap();
    stdin.flush().unwrap();

    // 3. tools/list -> must expose all 6 exact Gnomon tools
    let list_resp = send_recv(
        &mut stdin,
        &mut reader,
        json!({ "jsonrpc": "2.0", "id": 2, "method": "tools/list", "params": {} }),
    );
    let tools = list_resp["result"]["tools"].as_array().unwrap();
    let names: Vec<&str> = tools.iter().map(|t| t["name"].as_str().unwrap()).collect();
    for expected in MCP_TOOL_NAMES {
        assert!(names.contains(&expected), "missing MCP tool '{expected}' in {names:?}");
    }
    assert_eq!(names.len(), 6);

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

    // 4. gnomon_lift_check (base64 .wasm)
    let wasm_b64 = base64::engine::general_purpose::STANDARD.encode(build_sample_wasm_div_mod());
    let lift_res = call_tool(
        &mut stdin,
        &mut reader,
        3,
        "gnomon_lift_check",
        json!({ "content": wasm_b64, "input_type": "wasm" }),
    );
    assert_eq!(lift_res["input_type"], "wasm");
    assert_eq!(lift_res["roundtrip_wasm_valid"], true);

    // 5. gnomon_run_trace on lifted module (default active module)
    let trace_res = call_tool(
        &mut stdin,
        &mut reader,
        4,
        "gnomon_run_trace",
        json!({ "inputs": [{"ty": "i32", "val": 20}, {"ty": "i32", "val": 4}] }),
    );
    assert_eq!(trace_res["status"], "OK");
    assert_eq!(trace_res["outputs"][0]["val"], 5);

    // 6. gnomon_define_op (wrap_inc + unused_op)
    let def1 = call_tool(
        &mut stdin,
        &mut reader,
        5,
        "gnomon_define_op",
        json!({
            "name": "wrap_inc",
            "layer": 1,
            "body_content": wrap_inc_body_ir(),
            "input_type": "ir",
            "docstring": "Increment ring index modulo mask"
        }),
    );
    assert_eq!(def1["stratum_id"], 1);

    let def2 = call_tool(
        &mut stdin,
        &mut reader,
        6,
        "gnomon_define_op",
        json!({
            "name": "mix_xor",
            "layer": 1,
            "body_content": unused_op_body_ir(),
            "input_type": "ir"
        }),
    );
    assert_eq!(def2["stratum_id"], 2);

    // 7. gnomon_prove_law (valid algebraic law + memory-frame check + buggy law)
    let params2 = [(ValId(0), ValType::I32), (ValId(1), ValType::I32)];
    let lhs_p = Region::build(|b| {
        b.push_call(
            &[(ValId(2), ValType::I32)],
            CallTarget::Stratum(StratumId(1)),
            &[ValId(0), ValId(1)],
        );
        b.push_let(ValId(3), ValType::I32, Op::Bin(BinOp::I32And, ValId(2), ValId(1)));
        b.push_yield(&[ValId(3)]);
    });
    let rhs_p = Region::build(|b| {
        b.push_call(
            &[(ValId(2), ValType::I32)],
            CallTarget::Stratum(StratumId(1)),
            &[ValId(0), ValId(1)],
        );
        b.push_yield(&[ValId(2)]);
    });
    let prove_ok = call_tool(
        &mut stdin,
        &mut reader,
        7,
        "gnomon_prove_law",
        json!({
            "op": "wrap_inc",
            "name": "wrap_inc_mask_idem",
            "lhs_content": region_ir(&params2, &[ValType::I32], &lhs_p),
            "rhs_content": region_ir(&params2, &[ValType::I32], &rhs_p),
            "input_type": "ir"
        }),
    );
    assert_eq!(prove_ok["status"], "PROVED");

    let prove_bad = call_tool(
        &mut stdin,
        &mut reader,
        8,
        "gnomon_prove_law",
        json!({
            "op": "wrap_inc",
            "name": "false_identity",
            "lhs_content": region_ir(&params2, &[ValType::I32], &rhs_p),
            "rhs_content": region_ir(&params2, &[ValType::I32], &Region::yield_vals(&[ValId(0)])),
            "input_type": "ir"
        }),
    );
    assert_eq!(prove_bad["status"], "FALSIFIED");
    assert!(prove_bad["counterexample"].is_object());

    // Also prove a memory-frame law on a memory-writing op (writes MemId(0), untouched MemId(1))!
    let mem_wr_body = Region::build(|b| {
        b.push_effect(EffectOp::Store {
            mem: MemId(0),
            addr: ValId(0),
            offset: 0,
            width: MemWidth::B1,
            val: ValId(1),
        });
        b.push_yield(&[]);
    });
    let def_mem = call_tool(
        &mut stdin,
        &mut reader,
        9,
        "gnomon_define_op",
        json!({
            "name": "write_m0",
            "layer": 1,
            "body_content": region_ir(&params2, &[], &mem_wr_body),
            "input_type": "ir"
        }),
    );
    let mem_op_id = def_mem["stratum_id"].as_u64().unwrap() as u32;
    let call_mem = Region::build(|b| {
        b.push_call(&[], CallTarget::Stratum(StratumId(mem_op_id)), &[ValId(0), ValId(1)]);
        b.push_yield(&[]);
    });
    let prove_frame = call_tool(
        &mut stdin,
        &mut reader,
        10,
        "gnomon_prove_law",
        json!({
            "op": "write_m0",
            "name": "write_m0_preserves_m1",
            "kind": "memory_frame",
            "untouched_mem": 1,
            "lhs_content": region_ir(&params2, &[], &call_mem),
            "input_type": "ir"
        }),
    );
    assert_eq!(prove_frame["status"], "PROVED", "frame law result: {prove_frame}");

    // 8. gnomon_check_goal twice (verifies egglog law firing + accumulates 2 verified solutions!)
    let goal1 = call_tool(
        &mut stdin,
        &mut reader,
        11,
        "gnomon_check_goal",
        json!({
            "candidate_content": region_ir(&params2, &[ValType::I32], &lhs_p),
            "spec_content": region_ir(&params2, &[ValType::I32], &rhs_p),
            "input_type": "ir"
        }),
    );
    assert_eq!(goal1["status"], "PROVED");
    assert!(!goal1["laws_fired"].as_array().unwrap().is_empty());

    let goal2 = call_tool(
        &mut stdin,
        &mut reader,
        12,
        "gnomon_check_goal",
        json!({
            "candidate_content": region_ir(&params2, &[ValType::I32], &rhs_p),
            "spec_content": region_ir(&params2, &[ValType::I32], &rhs_p),
            "input_type": "ir"
        }),
    );
    assert_eq!(goal2["status"], "PROVED");

    // 9. gnomon_consolidate over live stdio JSON-RPC (MUST NOT corrupt stdout!)
    let cons = call_tool(
        &mut stdin,
        &mut reader,
        13,
        "gnomon_consolidate",
        json!({}),
    );
    assert_eq!(cons["kept_strata"], json!([1]));
    assert!(cons["autodoc_markdown"].as_str().unwrap().contains("wrap_inc"));

    // Clean EOF shutdown.
    drop(stdin);
    let status = child.wait().unwrap();
    assert!(status.success());
}

#[test]
fn test_e2e_adversarial_memory_frame_invariant_loop_mixed_wasm_ir_and_negative_gates() {
    let dir = temp_dir("adversarial");
    let state = dir.join("state.json");
    let params2 = [(ValId(0), ValType::I32), (ValId(1), ValType::I32)];

    // 1. Mixed `.wasm` candidate vs `.ir` spec in `gnomon check-goal` (`-t auto`)!
    let wasm_bytes = build_sample_wasm_div_mod();
    let wasm_path = dir.join("div_cand.wasm");
    std::fs::write(&wasm_path, &wasm_bytes).unwrap();
    let spec_div = Region::build(|b| {
        b.push_let(ValId(9), ValType::I32, Op::Bin(BinOp::I32DivS, ValId(0), ValId(1)));
        b.push_yield(&[ValId(9)]);
    });
    let spec_path = dir.join("div_spec.ir");
    std::fs::write(&spec_path, region_ir(&params2, &[ValType::I32], &spec_div)).unwrap();

    let out = Command::new(gnomon_bin())
        .args([
            "check-goal",
            "--candidate",
            wasm_path.to_str().unwrap(),
            "--spec",
            spec_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(out.status.success(), "mixed wasm/ir check-goal failed: {}", String::from_utf8_lossy(&out.stderr));
    let v: Value = serde_json::from_slice(&out.stdout).unwrap();
    assert_eq!(v["status"], "PROVED");

    // 2. Value-returning + trapping op writing MemId(0):
    //    - MemoryFrame { untouched_mem: 1 } MUST be PROVED (tests Bug #1a & #1b!)
    //    - MemoryFrame { untouched_mem: 0 } MUST be FALSIFIED (writes MemId(0)!)
    let trap_store_body = Region::build(|b| {
        b.push_let(ValId(2), ValType::I32, Op::Bin(BinOp::I32DivS, ValId(0), ValId(1)));
        b.push_effect(EffectOp::Store {
            mem: MemId(0),
            addr: ValId(0),
            offset: 0,
            width: MemWidth::B1,
            val: ValId(2),
        });
        b.push_yield(&[ValId(2)]);
    });
    let op_path = dir.join("div_and_store_m0.ir");
    std::fs::write(&op_path, region_ir(&params2, &[ValType::I32], &trap_store_body)).unwrap();

    let def = Command::new(gnomon_bin())
        .args([
            "--state",
            state.to_str().unwrap(),
            "-t",
            "ir",
            "define-op",
            "--name",
            "div_and_store_m0",
            "--layer",
            "1",
        ])
        .arg(&op_path)
        .output()
        .unwrap();
    assert!(def.status.success(), "stderr: {}", String::from_utf8_lossy(&def.stderr));

    // Negative gate: duplicate op name MUST be rejected!
    let dup = Command::new(gnomon_bin())
        .args([
            "--state",
            state.to_str().unwrap(),
            "-t",
            "ir",
            "define-op",
            "--name",
            "div_and_store_m0",
            "--layer",
            "1",
        ])
        .arg(&op_path)
        .output()
        .unwrap();
    assert!(!dup.status.success());
    assert!(String::from_utf8_lossy(&dup.stderr).contains("duplicate stratum op name"));

    // Negative gate: Layer-0 op MUST be rejected by TCB!
    let l0 = Command::new(gnomon_bin())
        .args([
            "--state",
            state.to_str().unwrap(),
            "-t",
            "ir",
            "define-op",
            "--name",
            "bad_layer0",
            "--layer",
            "0",
        ])
        .arg(&op_path)
        .output()
        .unwrap();
    assert!(!l0.status.success());

    let call_op = Region::build(|b| {
        b.push_call(
            &[(ValId(2), ValType::I32)],
            CallTarget::Stratum(StratumId(1)),
            &[ValId(0), ValId(1)],
        );
        b.push_yield(&[ValId(2)]);
    });
    let call_path = dir.join("call_div_store.ir");
    std::fs::write(&call_path, region_ir(&params2, &[ValType::I32], &call_op)).unwrap();

    // Valid frame law: untouched_mem = 1 -> PROVED even though op returns i32 AND can trap DivByZero/OOB(m0)!
    let frame_ok = Command::new(gnomon_bin())
        .args([
            "--state",
            state.to_str().unwrap(),
            "-t",
            "ir",
            "prove-law",
            "--op",
            "div_and_store_m0",
            "--name",
            "preserves_m1",
            "--kind",
            "memory-frame",
            "--untouched-mem",
            "1",
            "--lhs",
            call_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(frame_ok.status.success(), "stdout: {}\nstderr: {}", String::from_utf8_lossy(&frame_ok.stdout), String::from_utf8_lossy(&frame_ok.stderr));
    let v_ok: Value = serde_json::from_slice(&frame_ok.stdout).unwrap();
    assert_eq!(v_ok["status"], "PROVED");

    // Bogus frame law: untouched_mem = 0 -> MUST BE FALSIFIED because op stores to MemId(0)!
    let frame_bad = Command::new(gnomon_bin())
        .args([
            "--state",
            state.to_str().unwrap(),
            "-t",
            "ir",
            "prove-law",
            "--op",
            "div_and_store_m0",
            "--name",
            "bogus_preserves_m0",
            "--kind",
            "memory-frame",
            "--untouched-mem",
            "0",
            "--lhs",
            call_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(!frame_bad.status.success());
    let v_bad: Value = serde_json::from_slice(&frame_bad.stdout).unwrap();
    assert_eq!(v_bad["status"], "FALSIFIED");

    // Anti-smuggling test: even if caller passes an empty no-op `lhs` for `div_and_store_m0`
    // claiming `untouched_mem = 0`, Stage-2 MUST verify `target_op.body` and FALSIFY it!
    let empty_path = dir.join("empty_smuggle.ir");
    std::fs::write(&empty_path, region_ir(&params2, &[], &Region::empty())).unwrap();
    let smuggle = Command::new(gnomon_bin())
        .args([
            "--state",
            state.to_str().unwrap(),
            "-t",
            "ir",
            "prove-law",
            "--op",
            "div_and_store_m0",
            "--name",
            "smuggled_frame_m0",
            "--kind",
            "memory-frame",
            "--untouched-mem",
            "0",
            "--lhs",
            empty_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(!smuggle.status.success());
    let v_smuggle: Value = serde_json::from_slice(&smuggle.stdout).unwrap();
    assert_eq!(v_smuggle["status"], "FALSIFIED");

    // 3. InvariantLoop 3-way VC splitting via `gnomon check-goal`:
    //    Valid countdown loop: pre (n >= 0), state i = n, cond (i > 0), inv (i >= 0),
    //    fuel (i64.extend_i32_u(i)), body (i - 1), post (i == 0).
    let pre_n = Region::build(|b| {
        b.push_let(ValId(10), ValType::I32, Op::ConstI32(0));
        b.push_let(ValId(11), ValType::I32, Op::Bin(BinOp::I32GeS, ValId(0), ValId(10)));
        b.push_yield(&[ValId(11)]);
    });
    let cond = Region::build(|b| {
        b.push_let(ValId(10), ValType::I32, Op::ConstI32(0));
        b.push_let(ValId(11), ValType::I32, Op::Bin(BinOp::I32GtS, ValId(1), ValId(10)));
        b.push_yield(&[ValId(11)]);
    });
    let inv = Region::build(|b| {
        b.push_let(ValId(10), ValType::I32, Op::ConstI32(0));
        b.push_let(ValId(11), ValType::I32, Op::Bin(BinOp::I32GeS, ValId(1), ValId(10)));
        b.push_yield(&[ValId(11)]);
    });
    let fuel = Region::build(|b| {
        b.push_let(ValId(10), ValType::I64, Op::Un(gnomon_kernel::UnOp::I64ExtendI32U, ValId(1)));
        b.push_yield(&[ValId(10)]);
    });
    let body = Region::build(|b| {
        b.push_let(ValId(10), ValType::I32, Op::ConstI32(1));
        b.push_let(ValId(11), ValType::I32, Op::Bin(BinOp::I32Sub, ValId(1), ValId(10)));
        b.push_yield(&[ValId(11)]);
    });
    let post = Region::build(|b| {
        b.push_let(ValId(10), ValType::I32, Op::ConstI32(0));
        b.push_let(ValId(11), ValType::I32, Op::Bin(BinOp::I32Eq, ValId(1), ValId(10)));
        b.push_yield(&[ValId(11)]);
    });
    let valid_loop = Region::invariant_loop(
        &[ValId(0)],
        &[(ValId(1), ValType::I32)],
        &cond,
        &inv,
        &fuel,
        &body,
    );
    let broken_body = Region::build(|b| {
        b.push_yield(&[ValId(1)]); // fuel does NOT decrease -> preservation VC MUST fail!
    });
    let broken_loop = Region::invariant_loop(
        &[ValId(0)],
        &[(ValId(1), ValType::I32)],
        &cond,
        &inv,
        &fuel,
        &broken_body,
    );

    let p1 = [(ValId(0), ValType::I32)];
    let pre_p = dir.join("loop_pre.ir");
    let post_p = dir.join("loop_post.ir");
    let good_lp_p = dir.join("good_loop.ir");
    let bad_lp_p = dir.join("bad_loop.ir");
    std::fs::write(&pre_p, region_ir(&p1, &[ValType::I32], &pre_n)).unwrap();
    std::fs::write(&post_p, region_ir(&[(ValId(1), ValType::I32)], &[ValType::I32], &post)).unwrap();
    std::fs::write(&good_lp_p, region_ir(&p1, &[ValType::I32], &valid_loop)).unwrap();
    std::fs::write(&bad_lp_p, region_ir(&p1, &[ValType::I32], &broken_loop)).unwrap();

    let lp_ok = Command::new(gnomon_bin())
        .args([
            "-t",
            "ir",
            "check-goal",
            "--candidate",
            good_lp_p.to_str().unwrap(),
            "--spec",
            post_p.to_str().unwrap(),
            "--pre",
            pre_p.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(lp_ok.status.success(), "stdout: {}\nstderr: {}", String::from_utf8_lossy(&lp_ok.stdout), String::from_utf8_lossy(&lp_ok.stderr));
    let v_lp: Value = serde_json::from_slice(&lp_ok.stdout).unwrap();
    assert_eq!(v_lp["status"], "PROVED");
    assert_eq!(v_lp["vc_results"], json!(["init:PROVED", "preservation:PROVED", "exit:PROVED"]));

    let lp_bad = Command::new(gnomon_bin())
        .args([
            "-t",
            "ir",
            "check-goal",
            "--candidate",
            bad_lp_p.to_str().unwrap(),
            "--spec",
            post_p.to_str().unwrap(),
            "--pre",
            pre_p.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(!lp_bad.status.success());
    let v_bad_lp: Value = serde_json::from_slice(&lp_bad.stdout).unwrap();
    assert_eq!(v_bad_lp["status"], "FALSIFIED");

    let _ = std::fs::remove_dir_all(&dir);
}

