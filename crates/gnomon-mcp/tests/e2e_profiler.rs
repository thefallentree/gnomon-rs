#![forbid(unsafe_code)]

use std::io::{BufRead, BufReader, Write};
use std::path::PathBuf;
use std::process::{Command, Stdio};

use gnomon_mcp::{
    DEFAULT_ARM64_CPU, DEFAULT_X64_CPU, GnomonEngine, MCP_TOOL_NAMES, ProfileArch, ProfileRequest,
};
use serde_json::{Value, json};

fn gnomon_bin() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_gnomon"))
}

fn oms_fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples/oms_strata")
        .join(name)
}

const DIV_VS_BARRETT_RS: &str = r#"#![no_std]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[unsafe(no_mangle)]
pub extern "C" fn rem_hw_u32(key: u32, denom: u32, _magic: u64) -> u32 {
    if denom == 0 {
        return 0;
    }
    key % denom
}

#[unsafe(no_mangle)]
pub extern "C" fn rem_barrett_u32(key: u32, denom: u32, magic: u64) -> u32 {
    if denom == 0 {
        return 0;
    }
    let u_key = key as u64;
    let u_denom = denom as u64;
    let q_est = u_key.wrapping_mul(magic) >> 32;
    let rem_est = u_key.wrapping_sub(q_est.wrapping_mul(u_denom));
    let rem = if rem_est >= u_denom {
        rem_est.wrapping_sub(u_denom)
    } else {
        rem_est
    };
    rem as u32
}
"#;

const SPILL_CONTRAST_RS: &str = r#"#![no_std]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[unsafe(no_mangle)]
pub extern "C" fn high_reg_pressure_20(
    a0: u64, a1: u64, a2: u64, a3: u64,
    a4: u64, a5: u64, a6: u64, a7: u64,
) -> u64 {
    let mut x0 = a0.wrapping_add(1);
    let mut x1 = a1.wrapping_add(3);
    let mut x2 = a2.wrapping_add(5);
    let mut x3 = a3.wrapping_add(7);
    let mut x4 = a4.wrapping_add(11);
    let mut x5 = a5.wrapping_add(13);
    let mut x6 = a6.wrapping_add(17);
    let mut x7 = a7.wrapping_add(19);
    let mut x8 = a0 ^ a1;
    let mut x9 = a2 ^ a3;
    let mut x10 = a4 ^ a5;
    let mut x11 = a6 ^ a7;
    let mut x12 = a0.wrapping_mul(a7);
    let mut x13 = a1.wrapping_mul(a6);
    let mut x14 = a2.wrapping_mul(a5);
    let mut x15 = a3.wrapping_mul(a4);
    let mut x16 = a0.wrapping_add(a4);
    let mut x17 = a1.wrapping_add(a5);
    let mut x18 = a2.wrapping_add(a6);
    let mut x19 = a3.wrapping_add(a7);

    let mut i = 0u32;
    while i < 8 {
        x0 = x0.wrapping_mul(0x9e37_79b9_7f4a_7c15).wrapping_add(x1 ^ x19);
        x1 = x1.rotate_left(7).wrapping_add(x2 ^ x18);
        x2 = x2.wrapping_mul(0xbf58_476d_1ce4_e5b9).wrapping_add(x3 ^ x17);
        x3 = x3.rotate_left(13).wrapping_add(x4 ^ x16);
        x4 = x4.wrapping_mul(0x94d0_49bb_1331_11eb).wrapping_add(x5 ^ x15);
        x5 = x5.rotate_left(17).wrapping_add(x6 ^ x14);
        x6 = x6.wrapping_mul(0x2545_f491_4f6c_dd1d).wrapping_add(x7 ^ x13);
        x7 = x7.rotate_left(23).wrapping_add(x8 ^ x12);
        x8 = x8.wrapping_mul(0x6c62_272e_07bb_0142).wrapping_add(x9 ^ x11);
        x9 = x9.rotate_left(29).wrapping_add(x10 ^ x10.rotate_right(3));
        x10 = x10.wrapping_add(x11 ^ x0);
        x11 = x11.wrapping_add(x12 ^ x1);
        x12 = x12.wrapping_add(x13 ^ x2);
        x13 = x13.wrapping_add(x14 ^ x3);
        x14 = x14.wrapping_add(x15 ^ x4);
        x15 = x15.wrapping_add(x16 ^ x5);
        x16 = x16.wrapping_add(x17 ^ x6);
        x17 = x17.wrapping_add(x18 ^ x7);
        x18 = x18.wrapping_add(x19 ^ x8);
        x19 = x19.wrapping_add(x0 ^ x9);
        i += 1;
    }
    x0 ^ x1 ^ x2 ^ x3 ^ x4 ^ x5 ^ x6 ^ x7 ^ x8 ^ x9
        ^ x10 ^ x11 ^ x12 ^ x13 ^ x14 ^ x15 ^ x16 ^ x17 ^ x18 ^ x19
}

#[unsafe(no_mangle)]
pub extern "C" fn lean_mix_4(a0: u64, a1: u64, a2: u64, a3: u64) -> u64 {
    let mut x0 = a0.wrapping_add(1);
    let mut x1 = a1.wrapping_add(3);
    let mut x2 = a2.wrapping_add(5);
    let mut x3 = a3.wrapping_add(7);
    let mut i = 0u32;
    while i < 4 {
        x0 = x0.wrapping_mul(0x9e37_79b9_7f4a_7c15).wrapping_add(x1);
        x1 = x1.rotate_left(7).wrapping_add(x2);
        x2 = x2.wrapping_mul(0xbf58_476d_1ce4_e5b9).wrapping_add(x3);
        x3 = x3.rotate_left(13).wrapping_add(x0);
        i += 1;
    }
    x0 ^ x1 ^ x2 ^ x3
}
"#;

#[test]
fn test_profile_div_vs_barrett_x64_and_arm64() {
    let eng = GnomonEngine::new();
    let req = ProfileRequest {
        content: Some(DIV_VS_BARRETT_RS.to_string()),
        path: None,
        entry: Some("rem_hw_u32".to_string()),
        compare_content: None,
        compare_path: None,
        opt_entry: Some("rem_barrett_u32".to_string()),
        targets: vec![ProfileArch::X64, ProfileArch::Arm64],
        x64_cpu: DEFAULT_X64_CPU.to_string(),
        arm64_cpu: DEFAULT_ARM64_CPU.to_string(),
        bench: false,
    };

    let out = eng.profile(&req).expect("profile div vs barrett");
    assert_eq!(out.status, "OK");
    assert_eq!(out.profile.entry, "rem_hw_u32");
    let opt = out.opt_profile.as_ref().expect("opt_profile");
    assert_eq!(opt.entry, "rem_barrett_u32");
    let cmp = out.comparison.as_ref().expect("comparison");
    assert_eq!(cmp.target_deltas.len(), 2);

    // Check x86-64 (skylake): div_count drops 1 -> 0, llvm-mca shows real cycle & RThroughput speedup.
    let ref_x64 = out
        .profile
        .targets
        .iter()
        .find(|t| t.arch == ProfileArch::X64)
        .expect("ref x64");
    let opt_x64 = opt
        .targets
        .iter()
        .find(|t| t.arch == ProfileArch::X64)
        .expect("opt x64");
    assert_eq!(ref_x64.cpu, "skylake");
    assert_eq!(ref_x64.div_count, 1, "expected 1 hardware div on x64:\n{}", ref_x64.assembly);
    assert_eq!(opt_x64.div_count, 0, "expected 0 hardware div in Barrett:\n{}", opt_x64.assembly);
    assert!(ref_x64.total_cycles.is_some());
    assert!(opt_x64.total_cycles.is_some());
    assert!(ref_x64.block_rthroughput.is_some());
    assert!(opt_x64.block_rthroughput.is_some());
    assert!(ref_x64.ipc.is_some());
    assert!(ref_x64.uops_per_cycle.is_some());
    assert!(ref_x64.raw_mca_summary.contains("Total Cycles:"));

    let delta_x64 = cmp
        .target_deltas
        .iter()
        .find(|d| d.arch == ProfileArch::X64)
        .expect("x64 delta");
    assert_eq!(delta_x64.div_delta, -1);
    assert!(
        delta_x64.cycle_speedup.unwrap_or(0.0) > 1.0,
        "expected x64 cycle_speedup > 1.0, got {:?}",
        delta_x64.cycle_speedup
    );
    assert!(
        delta_x64.rthroughput_speedup.unwrap_or(0.0) > 1.0,
        "expected x64 rthroughput_speedup > 1.0, got {:?}",
        delta_x64.rthroughput_speedup
    );

    // Check ARM64 (neoverse-v2): udiv drops 1 -> 0, real ARM64 assembly + llvm-mca metrics!
    let ref_arm = out
        .profile
        .targets
        .iter()
        .find(|t| t.arch == ProfileArch::Arm64)
        .expect("ref arm64");
    let opt_arm = opt
        .targets
        .iter()
        .find(|t| t.arch == ProfileArch::Arm64)
        .expect("opt arm64");
    assert_eq!(ref_arm.cpu, "neoverse-v2");
    assert_eq!(ref_arm.div_count, 1, "expected 1 udiv on arm64:\n{}", ref_arm.assembly);
    assert_eq!(opt_arm.div_count, 0, "expected 0 udiv in Barrett on arm64:\n{}", opt_arm.assembly);
    assert!(ref_arm.total_cycles.is_some());
    assert!(opt_arm.total_cycles.is_some());
    assert!(ref_arm.block_rthroughput.is_some());
    assert!(opt_arm.block_rthroughput.is_some());

    let delta_arm = cmp
        .target_deltas
        .iter()
        .find(|d| d.arch == ProfileArch::Arm64)
        .expect("arm64 delta");
    assert_eq!(delta_arm.div_delta, -1);
    assert!(
        delta_arm.cycle_speedup.unwrap_or(0.0) > 1.0,
        "expected arm64 cycle_speedup > 1.0, got {:?}",
        delta_arm.cycle_speedup
    );
}

#[test]
fn test_profile_register_spill_detection_x64_vs_arm64_and_lean() {
    let eng = GnomonEngine::new();
    let req = ProfileRequest {
        content: Some(SPILL_CONTRAST_RS.to_string()),
        path: None,
        entry: Some("high_reg_pressure_20".to_string()),
        compare_content: None,
        compare_path: None,
        opt_entry: Some("lean_mix_4".to_string()),
        targets: vec![ProfileArch::X64, ProfileArch::Arm64],
        x64_cpu: DEFAULT_X64_CPU.to_string(),
        arm64_cpu: DEFAULT_ARM64_CPU.to_string(),
        bench: false,
    };

    let out = eng.profile(&req).expect("profile spill contrast");
    let heavy_x64 = out
        .profile
        .targets
        .iter()
        .find(|t| t.arch == ProfileArch::X64)
        .unwrap();
    let heavy_arm = out
        .profile
        .targets
        .iter()
        .find(|t| t.arch == ProfileArch::Arm64)
        .unwrap();
    let opt = out.opt_profile.as_ref().unwrap();
    let lean_x64 = opt
        .targets
        .iter()
        .find(|t| t.arch == ProfileArch::X64)
        .unwrap();
    let lean_arm = opt
        .targets
        .iter()
        .find(|t| t.arch == ProfileArch::Arm64)
        .unwrap();

    assert!(
        heavy_x64.register_spills > 0,
        "expected x64 spills > 0 on 20-var kernel:\n{}",
        heavy_x64.assembly
    );
    assert!(
        heavy_x64.register_reloads > 0,
        "expected x64 reloads > 0 on 20-var kernel:\n{}",
        heavy_x64.assembly
    );
    assert_eq!(
        heavy_arm.register_spills, 0,
        "expected 0 body register spills on ARM64 (31 GPRs):\n{}",
        heavy_arm.assembly
    );
    assert_eq!(
        heavy_arm.register_reloads, 0,
        "expected 0 body register reloads on ARM64 (31 GPRs):\n{}",
        heavy_arm.assembly
    );
    assert_eq!(lean_x64.register_spills, 0, "expected 0 spills on lean x64 kernel");
    assert_eq!(lean_arm.register_spills, 0, "expected 0 spills on lean ARM64 kernel");

    let cmp = out.comparison.as_ref().unwrap();
    let x64_delta = cmp
        .target_deltas
        .iter()
        .find(|d| d.arch == ProfileArch::X64)
        .unwrap();
    assert!(x64_delta.spill_delta < 0, "expected negative spill_delta on x64");
}

#[test]
fn test_profile_cli_oms_fixture_and_bench() {
    let fixture = oms_fixture("s1_2_barrett_tick_fee.rs");
    assert!(fixture.is_file(), "missing fixture {}", fixture.display());

    // Single-function CLI profile on real Wasm-authored OMS fixture (with core::arch::wasm32::unreachable)
    let out = Command::new(gnomon_bin())
        .args([
            "profile",
            fixture.to_str().unwrap(),
            "--entry",
            "tick_round_down",
            "--compare",
            fixture.to_str().unwrap(),
            "--opt-entry",
            "bucket_index_barrett_u32",
            "--targets",
            "x64,arm64",
            "--x64-cpu",
            "skylake",
            "--arm64-cpu",
            "neoverse-v2",
            "--bench",
        ])
        .output()
        .expect("run gnomon profile CLI");

    assert!(
        out.status.success(),
        "gnomon profile failed:\nstdout={}\nstderr={}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    let json: Value = serde_json::from_slice(&out.stdout).expect("valid JSON output");
    assert_eq!(json["status"], "OK");
    assert_eq!(json["profile"]["entry"], "tick_round_down");
    assert_eq!(json["opt_profile"]["entry"], "bucket_index_barrett_u32");

    let ref_ns = json["profile"]["host_ns_per_op"]
        .as_f64()
        .expect("finite host_ns_per_op for ref");
    let opt_ns = json["opt_profile"]["host_ns_per_op"]
        .as_f64()
        .expect("finite host_ns_per_op for opt");
    assert!(ref_ns.is_finite() && ref_ns > 0.0);
    assert!(opt_ns.is_finite() && opt_ns > 0.0);

    let host_speedup = json["comparison"]["host_speedup"]
        .as_f64()
        .expect("finite host_speedup");
    assert!(host_speedup.is_finite() && host_speedup > 0.0);
}

#[test]
fn test_profile_mcp_stdio_jsonrpc_live() {
    let mut child = Command::new(gnomon_bin())
        .arg("mcp")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn gnomon mcp");

    let mut stdin = child.stdin.take().unwrap();
    let stdout = child.stdout.take().unwrap();
    let mut reader = BufReader::new(stdout);

    let send_recv = |stdin: &mut std::process::ChildStdin,
                     reader: &mut BufReader<std::process::ChildStdout>,
                     msg: Value|
     -> Value {
        writeln!(stdin, "{msg}").unwrap();
        stdin.flush().unwrap();
        let mut line = String::new();
        reader.read_line(&mut line).unwrap();
        serde_json::from_str(&line).unwrap_or_else(|e| {
            panic!("invalid JSON-RPC response on stdout (stdio must stay 100% clean!): {e}\nline={line:?}")
        })
    };

    // 1. initialize
    let init = send_recv(
        &mut stdin,
        &mut reader,
        json!({
            "jsonrpc": "2.0",
            "id": 1,
            "method": "initialize",
            "params": {
                "protocolVersion": "2024-11-05",
                "capabilities": {},
                "clientInfo": { "name": "e2e-profiler", "version": "0.1.0" }
            }
        }),
    );
    assert!(
        init["result"]["instructions"]
            .as_str()
            .unwrap_or("")
            .contains("gnomon_profile")
    );

    writeln!(
        stdin,
        "{}",
        json!({ "jsonrpc": "2.0", "method": "notifications/initialized" })
    )
    .unwrap();
    stdin.flush().unwrap();

    // 2. tools/list -> 8 atomic tools including gnomon_profile
    let list = send_recv(
        &mut stdin,
        &mut reader,
        json!({ "jsonrpc": "2.0", "id": 2, "method": "tools/list", "params": {} }),
    );
    let tools = list["result"]["tools"].as_array().unwrap();
    let names: Vec<&str> = tools.iter().map(|t| t["name"].as_str().unwrap()).collect();
    assert_eq!(names.len(), 8);
    for expected in MCP_TOOL_NAMES {
        assert!(names.contains(&expected), "missing tool {expected}");
    }

    // 3. tools/call -> gnomon_profile (compare mode with x64 + arm64 + bench)
    let resp = send_recv(
        &mut stdin,
        &mut reader,
        json!({
            "jsonrpc": "2.0",
            "id": 3,
            "method": "tools/call",
            "params": {
                "name": "gnomon_profile",
                "arguments": {
                    "content": DIV_VS_BARRETT_RS,
                    "entry": "rem_hw_u32",
                    "opt_entry": "rem_barrett_u32",
                    "targets": ["x64", "arm64"],
                    "x64_cpu": "skylake",
                    "arm64_cpu": "neoverse-v2",
                    "bench": true
                }
            }
        }),
    );
    assert!(resp["error"].is_null(), "gnomon_profile MCP error: {resp}");
    let text = resp["result"]["content"][0]["text"].as_str().unwrap();
    let parsed: Value = serde_json::from_str(text).expect("parse gnomon_profile JSON payload");
    assert_eq!(parsed["status"], "OK");
    assert_eq!(parsed["comparison"]["ref_entry"], "rem_hw_u32");
    assert_eq!(parsed["comparison"]["opt_entry"], "rem_barrett_u32");
    assert_eq!(parsed["comparison"]["target_deltas"].as_array().unwrap().len(), 2);
    assert!(parsed["profile"]["host_ns_per_op"].as_f64().unwrap() > 0.0);
    assert!(parsed["opt_profile"]["host_ns_per_op"].as_f64().unwrap() > 0.0);

    drop(stdin);
    let status = child.wait().unwrap();
    assert!(status.success());
}

#[test]
fn test_profile_cfg_wasm32_panic_handler_with_bench() {
    let src = r#"#![no_std]

#[cfg(target_arch = "wasm32")]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

#[unsafe(no_mangle)]
pub extern "C" fn first_exported_after_cfg_panic(a: u64, b: u64) -> u64 {
    a.wrapping_mul(0x9e37_79b9_7f4a_7c15).wrapping_add(b)
}
"#;
    let eng = GnomonEngine::new();
    let req = ProfileRequest {
        content: Some(src.to_string()),
        path: None,
        entry: Some("first_exported_after_cfg_panic".to_string()),
        compare_content: None,
        compare_path: None,
        opt_entry: None,
        targets: vec![ProfileArch::X64, ProfileArch::Arm64],
        x64_cpu: DEFAULT_X64_CPU.to_string(),
        arm64_cpu: DEFAULT_ARM64_CPU.to_string(),
        bench: true,
    };
    let out = eng.profile(&req).expect("profile cfg(wasm32) panic handler with bench");
    assert_eq!(out.status, "OK");
    assert_eq!(out.profile.targets.len(), 2);
    let ns = out
        .profile
        .host_ns_per_op
        .expect("host_ns_per_op must succeed when #[cfg(target_arch = \"wasm32\")] precedes #[panic_handler]");
    assert!(ns.is_finite() && ns > 0.0, "expected finite positive host_ns_per_op, got {ns}");
}
