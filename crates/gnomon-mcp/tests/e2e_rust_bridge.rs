use std::io::{BufRead, BufReader, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::Instant;

use gnomon_kernel::{
    BinOp, CallTarget, FuncDef, FuncId, HostCallId, HostContract, Module, Op, Region, RegionNode,
    StratumId, StratumOp, StratumRegistry, Val, ValId, ValType,
};
use gnomon_mcp::{
    GnomonEngine, GnomonError, InputType, bind_stratum_imports, compile_rust_to_wasm,
    generate_strata_rs, looks_like_rust_source, lower_module_strata, module_has_stratum_calls,
    module_has_stratum_imports, resolve_input_type, sanitize_rust_ident,
};
use gnomon_wasm::{ExecOutcome, emit_wasm, lift_wasm, run_wasmtime_func};
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
        "gnomon_rust_bridge_{tag}_{}_{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// Reference SplitMix64 / Murmur3 `fmix64` bit-mixer in host Rust for concrete oracle checks.
fn ref_fmix64(x: i64) -> i64 {
    let mut z = x as u64;
    z ^= z >> 30;
    z = z.wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z ^= z >> 27;
    z = z.wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^= z >> 31;
    z as i64
}

const FMIX64_RS: &str = r#"#![no_std]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

#[unsafe(no_mangle)]
pub extern "C" fn order_id_mix(x: i64) -> i64 {
    let mut z = x as u64;
    z ^= z >> 30;
    z = z.wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z ^= z >> 27;
    z = z.wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^= z >> 31;
    z as i64
}
"#;

#[test]
fn test_input_type_detection_and_sanitize_ident() {
    assert_eq!(
        resolve_input_type(InputType::Auto, Some("foo/bar.rs"), b""),
        InputType::Rust
    );
    assert_eq!(
        resolve_input_type(InputType::Auto, None, FMIX64_RS.as_bytes()),
        InputType::Rust
    );
    assert_eq!(
        resolve_input_type(InputType::Rust, Some("foo.txt"), b"anything"),
        InputType::Rust
    );
    assert_eq!(
        resolve_input_type(InputType::Auto, None, b"\0asm\x01\0\0\0"),
        InputType::Wasm
    );
    // JSON containing Rust keywords/attributes inside strings must NOT be misclassified as Rust!
    let json_with_rust_doc =
        br##"{"kind":"region","doc":"#![no_std] #[unsafe(no_mangle)] pub extern \"C\" fn"}"##;
    assert!(!looks_like_rust_source(
        std::str::from_utf8(json_with_rust_doc).unwrap()
    ));
    assert_eq!(
        resolve_input_type(InputType::Auto, None, json_with_rust_doc),
        InputType::Ir
    );

    assert_eq!(sanitize_rust_ident("order_id_mix"), "order_id_mix");
    assert_eq!(sanitize_rust_ident("foo-bar.baz"), "foo_bar_baz");
    assert_eq!(sanitize_rust_ident("type"), "type_op");
    assert_eq!(sanitize_rust_ident("self"), "self_op");
    assert_eq!(sanitize_rust_ident("123mix"), "op_123mix");
    assert_eq!(sanitize_rust_ident(""), "op_");
}

#[test]
fn test_compile_rust_editions_diagnostics_and_oms_fixtures() {
    // 1. Rust 2021 style (#[no_mangle], extern "C")
    let rs_2021 = r#"#![no_std]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { core::arch::wasm32::unreachable() }
#[link(wasm_import_module = "gnomon")]
extern "C" { fn gnomon_assert(cond: i32); }
#[no_mangle]
pub extern "C" fn inc(x: i32) -> i32 {
    unsafe { gnomon_assert(1); }
    x.wrapping_add(1)
}
"#;
    let wasm21 = compile_rust_to_wasm(rs_2021, None, None).expect("Rust 2021 syntax should compile");
    let mod21 = lift_wasm(&wasm21).unwrap();
    assert_eq!(mod21.funcs.len(), 1);
    assert_eq!(mod21.host_contracts.len(), 1);

    // 2. Invalid Rust returns crisp rustc diagnostics in GnomonError::InvalidInput
    let bad_rs = r#"#![no_std]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { core::arch::wasm32::unreachable() }
#[unsafe(no_mangle)]
pub extern "C" fn broken(x: i32) -> i32 {
    x + "not_an_i32"
}
"#;
    let err = compile_rust_to_wasm(bad_rs, None, None).unwrap_err();
    match err {
        GnomonError::InvalidInput(msg) => {
            assert!(
                msg.contains("rustc compilation failed")
                    && (msg.contains("E0277") || msg.contains("cannot add")),
                "expected crisp rustc diagnostics, got: {msg}"
            );
        }
        other => panic!("expected InvalidInput, got: {other:?}"),
    }

    // 3. All existing examples/oms_strata/*.rs compile & lift directly!
    let oms_dir = repo_root().join("examples").join("oms_strata");
    for name in [
        "s1_1_notional_collar.rs",
        "s3_1_child_fsm.rs",
        "s3_1_child_fsm_buggy.rs",
    ] {
        let p = oms_dir.join(name);
        let src = std::fs::read_to_string(&p).unwrap();
        let wasm = compile_rust_to_wasm(&src, Some(&p), None)
            .unwrap_or_else(|e| panic!("failed compiling {}: {e}", p.display()));
        let lifted = lift_wasm(&wasm).unwrap();
        assert!(!lifted.funcs.is_empty(), "{name} should export functions");
        if name.starts_with("s3_1_") {
            assert_eq!(lifted.globals.len(), 0, "{name} must have 0 globals");
            assert_eq!(lifted.host_contracts.len(), 2);
        }
    }
}

#[test]
fn test_bind_stratum_imports_errors_and_nested_region_rewriting() {
    let mut reg = StratumRegistry::new();
    let double_body = Region::build(|b| {
        b.push_let(ValId(1), ValType::I32, Op::Bin(BinOp::I32Add, ValId(0), ValId(0)));
        b.push_yield(&[ValId(1)]);
    });
    reg.register_candidate_op(StratumOp {
        id: StratumId(7),
        name: "double_i32".into(),
        layer: 1,
        params: vec![(ValId(0), ValType::I32)],
        results: vec![ValType::I32],
        body: double_body,
        docstring: "doubles i32".into(),
    })
    .unwrap();

    let true_pred = || {
        Region::build(|b| {
            b.push_let(ValId(0), ValType::I32, Op::ConstI32(1));
            b.push_yield(&[ValId(0)]);
        })
    };
    let make_hc = |id: u32, module_name: &str, field_name: &str, p: Vec<ValType>, r: Vec<ValType>| {
        HostContract {
            id: HostCallId(id),
            module_name: module_name.into(),
            field_name: field_name.into(),
            params: p.into_iter().enumerate().map(|(i, t)| (ValId(i as u32), t)).collect(),
            results: r.into_iter().enumerate().map(|(i, t)| (ValId(10 + i as u32), t)).collect(),
            precondition: true_pred(),
            read_footprints: Vec::new(),
            write_footprints: Vec::new(),
            postcondition: true_pred(),
            sim_body: None,
        }
    };

    // 1. Unknown stratum import errors cleanly
    let unknown_mod = Module {
        host_contracts: vec![make_hc(0, "stratum", "no_such_op", vec![ValType::I32], vec![ValType::I32])],
        ..Module::default()
    };
    let err = bind_stratum_imports(unknown_mod, &reg).unwrap_err();
    assert!(matches!(err, GnomonError::Registry(_)), "got {err:?}");

    // 2. Signature mismatch errors cleanly
    let mismatch_mod = Module {
        host_contracts: vec![make_hc(0, "stratum", "double_i32", vec![ValType::I64], vec![ValType::I64])],
        ..Module::default()
    };
    let err = bind_stratum_imports(mismatch_mod, &reg).unwrap_err();
    assert!(
        matches!(err, GnomonError::Registry(ref m) if m.contains("signature mismatch")),
        "got {err:?}"
    );

    // 3. Rewrites CallTarget::Host across Block, IfElse, BoundedLoop, AND InvariantLoop
    //    while compacting HostCallId(0) (stratum) out and re-indexing HostCallId(1) (gnomon_assert) -> HostCallId(0).
    let then_reg = Region::build(|b| {
        b.push_call(&[(ValId(2), ValType::I32)], CallTarget::Host(HostCallId(0)), &[ValId(0)]);
        b.push_call(&[], CallTarget::Host(HostCallId(1)), &[ValId(2)]);
        b.push_yield(&[ValId(2)]);
    });
    let else_reg = Region::build(|b| {
        b.push_yield(&[ValId(0)]);
    });
    let if_reg = Region::if_else(ValId(0), &then_reg, &else_reg, &[ValType::I32]);

    let bloop_body = Region::build(|b| {
        b.push_call(&[(ValId(4), ValType::I32)], CallTarget::Host(HostCallId(0)), &[ValId(3)]);
        b.push_yield(&[ValId(4)]);
    });
    let bloop_reg = Region::bounded_loop(2, &[ValId(0)], &[(ValId(3), ValType::I32)], &bloop_body);

    let iloop_cond = Region::build(|b| {
        b.push_call(&[(ValId(6), ValType::I32)], CallTarget::Host(HostCallId(0)), &[ValId(5)]);
        b.push_yield(&[ValId(6)]);
    });
    let iloop_inv = Region::build(|b| {
        b.push_call(&[], CallTarget::Host(HostCallId(1)), &[ValId(5)]);
        b.push_yield(&[ValId(5)]);
    });
    let iloop_fuel = Region::build(|b| {
        b.push_yield(&[ValId(5)]);
    });
    let iloop_body = Region::build(|b| {
        b.push_call(&[(ValId(7), ValType::I32)], CallTarget::Host(HostCallId(0)), &[ValId(5)]);
        b.push_yield(&[ValId(7)]);
    });
    let iloop_reg = Region::invariant_loop(
        &[ValId(0)],
        &[(ValId(5), ValType::I32)],
        &iloop_cond,
        &iloop_inv,
        &iloop_fuel,
        &iloop_body,
    );

    let root_body = Region::build(|b| {
        b.push_subregion(&[(ValId(10), ValType::I32)], &if_reg);
        b.push_subregion(&[(ValId(11), ValType::I32)], &bloop_reg);
        b.push_subregion(&[(ValId(12), ValType::I32)], &iloop_reg);
        b.push_yield(&[ValId(12)]);
    });

    let nested_mod = Module {
        host_contracts: vec![
            make_hc(0, "stratum", "double_i32", vec![ValType::I32], vec![ValType::I32]),
            make_hc(1, "gnomon", "gnomon_assert", vec![ValType::I32], vec![]),
        ],
        funcs: vec![FuncDef {
            id: FuncId(0),
            name: "nested".into(),
            export_name: Some("nested".into()),
            params: vec![(ValId(0), ValType::I32)],
            results: vec![ValType::I32],
            body: root_body,
        }],
        ..Module::default()
    };

    let bound = bind_stratum_imports(nested_mod, &reg).unwrap();
    assert!(!module_has_stratum_imports(&bound));
    assert!(module_has_stratum_calls(&bound));
    assert_eq!(bound.host_contracts.len(), 1);
    assert_eq!(bound.host_contracts[0].id, HostCallId(0));
    assert_eq!(bound.host_contracts[0].field_name, "gnomon_assert");

    // Count all rewritten CallTargets across every nested region node.
    fn count_targets(r: gnomon_kernel::RegionRef<'_>, strata: &mut usize, hosts: &mut Vec<u32>) {
        match r.node {
            RegionNode::Block(span) => {
                for i in 0..span.len {
                    if let Some(stmt) = r.region.try_stmt(span, i) {
                        match stmt {
                            gnomon_kernel::Stmt::Call { target: CallTarget::Stratum(StratumId(7)), .. } => {
                                *strata += 1;
                            }
                            gnomon_kernel::Stmt::Call { target: CallTarget::Host(HostCallId(h)), .. } => {
                                hosts.push(h);
                            }
                            gnomon_kernel::Stmt::Region { region, .. } => {
                                count_targets(r.child(region).unwrap(), strata, hosts);
                            }
                            _ => {}
                        }
                    }
                }
            }
            RegionNode::IfElse { then_region, else_region, .. } => {
                count_targets(r.child(then_region).unwrap(), strata, hosts);
                count_targets(r.child(else_region).unwrap(), strata, hosts);
            }
            RegionNode::BoundedLoop { body, .. } => {
                count_targets(r.child(body).unwrap(), strata, hosts);
            }
            RegionNode::InvariantLoop { cond, invariant_pred, fuel_measure, body, .. } => {
                for id in [cond, invariant_pred, fuel_measure, body] {
                    count_targets(r.child(id).unwrap(), strata, hosts);
                }
            }
        }
    }

    let mut strata_calls = 0usize;
    let mut host_ids = Vec::new();
    count_targets(bound.funcs[0].body.as_ref(), &mut strata_calls, &mut host_ids);
    assert_eq!(strata_calls, 4, "all 4 stratum calls (IfElse, BoundedLoop, InvariantLoop cond+body) must bind");
    assert_eq!(host_ids, vec![0, 0], "both gnomon_assert calls must re-index Host(1) -> Host(0)");
}

#[test]
fn test_generate_strata_rs_and_transitive_multilayer_lowering_on_wasmtime() {
    let mut eng = GnomonEngine::new();

    // Layer 1: `order_id_mix(x: i64) -> i64` compiled from strict no_std Rust.
    let (_, art1) = eng
        .load_artifact_bytes(FMIX64_RS.as_bytes(), InputType::Rust, None)
        .unwrap();
    let (_, p1, r1, b1) = art1.into_region(Some("order_id_mix")).unwrap();
    let p1_dto = p1
        .into_iter()
        .map(|(id, ty)| gnomon_mcp::IrTypedVar { id: id.0, ty: ty.into() })
        .collect();
    let r1_dto = r1.into_iter().map(Into::into).collect();
    eng.define_op(
        "order_id_mix".into(),
        1,
        p1_dto,
        r1_dto,
        b1,
        "SplitMix64 bijective 64-bit mixer".into(),
        None,
    )
    .unwrap();

    // Also register a 0-result and keyword-named op to verify generate_strata_rs handles them cleanly.
    let void_body = Region::build(|b| {
        b.push_yield(&[]);
    });
    eng.define_op(
        "type".into(),
        1,
        vec![gnomon_mcp::IrTypedVar { id: 0, ty: gnomon_mcp::IrValType::I32 }],
        vec![],
        void_body,
        "keyword-named void op".into(),
        None,
    )
    .unwrap();

    // `include_candidates = false` omits candidates, `true` includes them.
    let promoted_only_rs = generate_strata_rs(&eng.registry, false);
    assert!(!promoted_only_rs.contains("pub fn order_id_mix"));
    assert!(promoted_only_rs.contains("pub fn gnomon_assume"));
    assert!(promoted_only_rs.contains("pub fn gnomon_assert"));

    let full_strata_rs = generate_strata_rs(&eng.registry, true);
    assert!(full_strata_rs.contains("pub fn order_id_mix(arg0: i64) -> i64"));
    assert!(full_strata_rs.contains("#[link_name = \"type\"]"));
    assert!(full_strata_rs.contains("pub fn type_op(arg0: i32)"));

    // Layer 2: `double_mix(x: i64) -> i64` calling Layer-1 `strata::order_id_mix` twice!
    let layer2_rs = r#"#![no_std]
mod strata;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

#[unsafe(no_mangle)]
pub extern "C" fn double_mix(x: i64) -> i64 {
    strata::order_id_mix(strata::order_id_mix(x)) ^ x
}
"#;
    let (_, art2) = eng
        .load_artifact_bytes(layer2_rs.as_bytes(), InputType::Auto, None)
        .unwrap();
    let (_, p2, r2, b2) = art2.into_region(Some("double_mix")).unwrap();
    let p2_dto = p2
        .into_iter()
        .map(|(id, ty)| gnomon_mcp::IrTypedVar { id: id.0, ty: ty.into() })
        .collect();
    let r2_dto = r2.into_iter().map(Into::into).collect();
    eng.define_op(
        "double_mix".into(),
        2,
        p2_dto,
        r2_dto,
        b2,
        "Layer-2 double fmix64".into(),
        None,
    )
    .unwrap();

    // Layer 3 caller module calling `strata::double_mix` (with early return branch) ->
    // transitively depends on Layer-2 `double_mix` -> Layer-1 `order_id_mix`!
    let caller_rs = r#"#![no_std]
mod strata;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

#[unsafe(no_mangle)]
pub extern "C" fn route_bucket(a: i64, b: i64) -> i64 {
    if a == 0 {
        return strata::double_mix(b);
    }
    strata::double_mix(a) ^ strata::double_mix(b)
}
"#;
    let (_, caller_art) = eng
        .load_artifact_bytes(caller_rs.as_bytes(), InputType::Rust, None)
        .unwrap();
    let caller_mod = match caller_art {
        gnomon_mcp::LoadedArtifact::Module(m) => m,
        _ => panic!("expected module"),
    };
    assert!(!module_has_stratum_imports(&caller_mod));
    assert!(
        module_has_stratum_calls(&caller_mod),
        "LLVM must NOT inline stratum extern import!"
    );

    // Transitively lower Layer-3 -> Layer-2 -> Layer-1 -> Layer-0 standalone Wasm!
    let lowered = lower_module_strata(&caller_mod, &eng.registry).unwrap();
    assert!(!module_has_stratum_imports(&lowered));
    assert!(!module_has_stratum_calls(&lowered));
    assert!(lowered.host_contracts.is_empty());
    // Original 1 func + 2 materialized internal strata (`order_id_mix`, `double_mix`)
    assert_eq!(lowered.funcs.len(), 3);

    let standalone_wasm = emit_wasm(&lowered).expect("lowered module must emit valid wasm");
    for (a, b) in [(0i64, 42i64), (123_456_789i64, -987_654_321i64), (7i64, 7i64)] {
        let dm = |v: i64| ref_fmix64(ref_fmix64(v)) ^ v;
        let expected = if a == 0 { dm(b) } else { dm(a) ^ dm(b) };
        let (outcome, _) = run_wasmtime_func(
            &standalone_wasm,
            "route_bucket",
            &[Val::I64(a), Val::I64(b)],
            100_000,
        )
        .unwrap();
        assert_eq!(outcome, ExecOutcome::Values(vec![Val::I64(expected)]));
    }
}

#[test]
fn test_cli_e2e_pure_rust_strata_uf_cegar_and_standalone_wasm() {
    let dir = temp_dir("cli_rust_e2e");
    let state = dir.join("state.json");

    // 0. Direct CLI lift & check-contract on examples/oms_strata/s1_1_notional_collar.rs (NO prebuilt wasm!)
    let oms_s1 = repo_root()
        .join("examples")
        .join("oms_strata")
        .join("s1_1_notional_collar.rs");
    let lift_oms = Command::new(gnomon_bin())
        .args(["lift", oms_s1.to_str().unwrap()])
        .output()
        .unwrap();
    assert!(
        lift_oms.status.success(),
        "lift s1_1 .rs failed: {}",
        String::from_utf8_lossy(&lift_oms.stderr)
    );
    let lift_v: Value = serde_json::from_slice(&lift_oms.stdout).unwrap();
    assert_eq!(lift_v["input_type"], "rust");
    assert_eq!(lift_v["roundtrip_wasm_valid"], true);

    let cc_oms = Command::new(gnomon_bin())
        .args([
            "check-contract",
            oms_s1.to_str().unwrap(),
            "--entry",
            "checked_notional",
            "--requires",
            "req_notional",
            "--ensures",
            "ens_notional",
            "--timeout-ms",
            "15000",
        ])
        .output()
        .unwrap();
    assert!(
        cc_oms.status.success(),
        "check-contract .rs failed: {}",
        String::from_utf8_lossy(&cc_oms.stderr)
    );
    let cc_v: Value = serde_json::from_slice(&cc_oms.stdout).unwrap();
    assert_eq!(cc_v["status"], "PROVED");

    // 1. Define Layer-1 `order_id_mix` (`fmix64`) directly from pure Rust (ZERO hand-written `.ir` JSON!)
    let mix_rs = dir.join("order_id_mix.rs");
    std::fs::write(&mix_rs, FMIX64_RS).unwrap();

    let def_out = Command::new(gnomon_bin())
        .args([
            "--state",
            state.to_str().unwrap(),
            "-t",
            "rust",
            "define-op",
            mix_rs.to_str().unwrap(),
            "--name",
            "order_id_mix",
            "--layer",
            "1",
            "--doc",
            "SplitMix64 fmix64 order ID mixer",
        ])
        .output()
        .unwrap();
    assert!(
        def_out.status.success(),
        "define-op -t rust failed: {}",
        String::from_utf8_lossy(&def_out.stderr)
    );
    let def_v: Value = serde_json::from_slice(&def_out.stdout).unwrap();
    assert_eq!(def_v["stratum_id"], 1);
    assert_eq!(def_v["status"], "CANDIDATE_REGISTERED");

    // 2. Emit `strata.rs` via CLI (both file and stdout!)
    let strata_rs_path = dir.join("strata.rs");
    let emit_file = Command::new(gnomon_bin())
        .args([
            "--state",
            state.to_str().unwrap(),
            "emit-rust",
            strata_rs_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        emit_file.status.success(),
        "emit-rust file failed: {}",
        String::from_utf8_lossy(&emit_file.stderr)
    );
    let emitted_code = std::fs::read_to_string(&strata_rs_path).unwrap();
    assert!(emitted_code.contains("pub fn order_id_mix(arg0: i64) -> i64"));
    assert!(emitted_code.contains("pub fn gnomon_assume(cond: bool)"));
    assert!(emitted_code.contains("pub fn gnomon_assert(cond: bool)"));

    let emit_stdout = Command::new(gnomon_bin())
        .args(["--state", state.to_str().unwrap(), "emit-rust"])
        .output()
        .unwrap();
    assert!(emit_stdout.status.success());
    assert_eq!(String::from_utf8_lossy(&emit_stdout.stdout), emitted_code);

    // 3. Prove a genuine non-redundant law on `order_id_mix` in 100% pure Rust using `mod strata;`!
    //    `order_id_mix(0) == 0` (fixed point of SplitMix64 `fmix64`, NOT derivable by generic Layer-0 identities).
    let law_lhs_rs = dir.join("law_lhs.rs");
    let law_rhs_rs = dir.join("law_rhs.rs");
    std::fs::write(
        &law_lhs_rs,
        r#"#![no_std]
mod strata;
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { core::arch::wasm32::unreachable() }
#[unsafe(no_mangle)]
pub extern "C" fn lhs() -> i64 {
    strata::order_id_mix(0)
}
"#,
    )
    .unwrap();
    std::fs::write(
        &law_rhs_rs,
        r#"#![no_std]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { core::arch::wasm32::unreachable() }
#[unsafe(no_mangle)]
pub extern "C" fn rhs() -> i64 {
    0
}
"#,
    )
    .unwrap();

    let prove_out = Command::new(gnomon_bin())
        .args([
            "--state",
            state.to_str().unwrap(),
            "prove-law",
            "--op",
            "order_id_mix",
            "--name",
            "mix_zero_fixed_point",
            "--lhs",
            law_lhs_rs.to_str().unwrap(),
            "--rhs",
            law_rhs_rs.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        prove_out.status.success(),
        "prove-law .rs failed: stdout={} stderr={}",
        String::from_utf8_lossy(&prove_out.stdout),
        String::from_utf8_lossy(&prove_out.stderr)
    );
    let prove_v: Value = serde_json::from_slice(&prove_out.stdout).unwrap();
    assert_eq!(prove_v["status"], "PROVED");
    assert_eq!(prove_v["stage"], "stage3_kernel_admitted");

    // 4. Write Layer-2 pure Rust caller importing `strata::order_id_mix` + `gnomon_assume`/`gnomon_assert`!
    //    Verify:
    //    (a) `lift --emit-ir` preserves `CallTarget::Stratum(1)` (NOT inlined by LLVM!)
    //    (b) `check-goal` proves deep 2x-`fmix64` equivalence past Bitwuzla's flat nonlinear cliff in < 100 ms!
    //    (c) `check-contract` proves relational congruence over 2x-`fmix64` via UF CEGAR in < 100 ms!
    //    (d) `trace` executes the Rust caller with `CallTarget::Stratum(1)` accurately!
    //    (e) `lift --lower --emit-wasm standalone.wasm` produces a zero-import `.wasm` that runs on `wasmtime`!
    let caller_cand_rs = dir.join("caller_cand.rs");
    let caller_spec_rs = dir.join("caller_spec.rs");
    std::fs::write(
        &caller_cand_rs,
        r#"#![no_std]
mod strata;
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { core::arch::wasm32::unreachable() }

#[unsafe(no_mangle)]
pub extern "C" fn mix_pair(a: i64, b: i64) -> i64 {
    let ha = strata::order_id_mix(strata::order_id_mix(a));
    let hb = strata::order_id_mix(strata::order_id_mix(b));
    ha.wrapping_add(hb)
}
"#,
    )
    .unwrap();
    std::fs::write(
        &caller_spec_rs,
        r#"#![no_std]
mod strata;
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { core::arch::wasm32::unreachable() }

#[unsafe(no_mangle)]
pub extern "C" fn mix_pair_spec(a: i64, b: i64) -> i64 {
    let hb = strata::order_id_mix(strata::order_id_mix(b));
    let ha = strata::order_id_mix(strata::order_id_mix(a));
    hb.wrapping_add(ha)
}
"#,
    )
    .unwrap();

    // (a) Verify CallTarget::Stratum(1) is preserved in lifted IR!
    let lift_caller = Command::new(gnomon_bin())
        .args([
            "--state",
            state.to_str().unwrap(),
            "lift",
            caller_cand_rs.to_str().unwrap(),
            "--emit-ir",
        ])
        .output()
        .unwrap();
    assert!(
        lift_caller.status.success(),
        "lift caller.rs failed: {}",
        String::from_utf8_lossy(&lift_caller.stderr)
    );
    let lift_caller_str = String::from_utf8_lossy(&lift_caller.stdout);
    let lift_caller_v: Value = serde_json::from_str(&lift_caller_str).unwrap();
    assert_eq!(lift_caller_v["input_type"], "rust");
    assert_eq!(lift_caller_v["host_contracts"], 0);
    assert_eq!(lift_caller_v["roundtrip_wasm_valid"], true);
    assert!(
        lift_caller_str.contains("\"kind\": \"stratum\""),
        "expected CallTarget::Stratum preserved in IR, got:\n{lift_caller_str}"
    );

    // (b) `check-goal` past Bitwuzla's flat cliff via UF CEGAR in < 100 ms!
    let goal_out = Command::new(gnomon_bin())
        .args([
            "--state",
            state.to_str().unwrap(),
            "check-goal",
            "--candidate",
            caller_cand_rs.to_str().unwrap(),
            "--spec",
            caller_spec_rs.to_str().unwrap(),
            "--timeout-ms",
            "5000",
        ])
        .output()
        .unwrap();
    assert!(
        goal_out.status.success(),
        "check-goal .rs UF CEGAR failed: stdout={} stderr={}",
        String::from_utf8_lossy(&goal_out.stdout),
        String::from_utf8_lossy(&goal_out.stderr)
    );
    let goal_v: Value = serde_json::from_slice(&goal_out.stdout).unwrap();
    assert_eq!(goal_v["status"], "PROVED");
    let goal_ms = goal_v["elapsed_ms"].as_f64().unwrap();
    assert!(
        goal_ms < 100.0,
        "UF CEGAR proof should complete in <100 ms past flat fmix64 cliff, took {goal_ms:.2} ms"
    );

    // (c) `check-contract` with inline `strata::gnomon_assume` + `strata::gnomon_assert` + `strata::order_id_mix`!
    let contract_rs = dir.join("caller_contract.rs");
    std::fs::write(
        &contract_rs,
        r#"#![no_std]
mod strata;
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { core::arch::wasm32::unreachable() }

#[unsafe(no_mangle)]
pub extern "C" fn verify_mix_congruence(a: i64, b: i64) -> i64 {
    strata::gnomon_assume(a == b);
    let ha = strata::order_id_mix(strata::order_id_mix(a));
    let hb = strata::order_id_mix(strata::order_id_mix(b));
    strata::gnomon_assert(ha == hb);
    ha
}
"#,
    )
    .unwrap();
    let cc_out = Command::new(gnomon_bin())
        .args([
            "--state",
            state.to_str().unwrap(),
            "check-contract",
            contract_rs.to_str().unwrap(),
            "--entry",
            "verify_mix_congruence",
            "--timeout-ms",
            "5000",
        ])
        .output()
        .unwrap();
    assert!(
        cc_out.status.success(),
        "check-contract UF CEGAR failed: stdout={} stderr={}",
        String::from_utf8_lossy(&cc_out.stdout),
        String::from_utf8_lossy(&cc_out.stderr)
    );
    let cc_v: Value = serde_json::from_slice(&cc_out.stdout).unwrap();
    assert_eq!(cc_v["status"], "PROVED");
    let cc_ms = cc_v["elapsed_ms"].as_f64().unwrap();
    assert!(
        cc_ms < 100.0,
        "UF CEGAR contract proof should complete in <100 ms, took {cc_ms:.2} ms"
    );

    // (d) `trace` directly on `-t rust` file calling Stratum!
    let trace_out = Command::new(gnomon_bin())
        .args([
            "--state",
            state.to_str().unwrap(),
            "trace",
            caller_cand_rs.to_str().unwrap(),
            "--entry",
            "mix_pair",
            "--inputs",
            r#"[{"ty":"i64","val":11},{"ty":"i64","val":29}]"#,
        ])
        .output()
        .unwrap();
    assert!(
        trace_out.status.success(),
        "trace .rs failed: {}",
        String::from_utf8_lossy(&trace_out.stderr)
    );
    let trace_v: Value = serde_json::from_slice(&trace_out.stdout).unwrap();
    let expected_sum = ref_fmix64(ref_fmix64(11)).wrapping_add(ref_fmix64(ref_fmix64(29)));
    assert_eq!(trace_v["status"], "OK");
    assert_eq!(trace_v["outputs"][0]["val"], expected_sum);

    // (e) `lift --lower --emit-wasm standalone.wasm` produces zero-import Wasm runnable on `wasmtime`!
    let standalone_wasm_path = dir.join("standalone.wasm");
    let lower_out = Command::new(gnomon_bin())
        .args([
            "--state",
            state.to_str().unwrap(),
            "lift",
            caller_cand_rs.to_str().unwrap(),
            "--lower",
            "--emit-wasm",
            standalone_wasm_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        lower_out.status.success(),
        "lift --lower --emit-wasm failed: {}",
        String::from_utf8_lossy(&lower_out.stderr)
    );
    let standalone_bytes = std::fs::read(&standalone_wasm_path).unwrap();
    let relifted = lift_wasm(&standalone_bytes).unwrap();
    assert!(
        relifted.host_contracts.is_empty(),
        "standalone lowered wasm must have ZERO imports"
    );
    let (wt_outcome, _) = run_wasmtime_func(
        &standalone_bytes,
        "mix_pair",
        &[Val::I64(11), Val::I64(29)],
        100_000,
    )
    .unwrap();
    assert_eq!(wt_outcome, ExecOutcome::Values(vec![Val::I64(expected_sum)]));

    // (f) `consolidate --emit-rust` writes updated strata.rs with proved law comment!
    let consolidated_rs_path = dir.join("strata_consolidated.rs");
    let cons_out = Command::new(gnomon_bin())
        .args([
            "--state",
            state.to_str().unwrap(),
            "consolidate",
            "--min-solutions",
            "1",
            "--emit-rust",
            consolidated_rs_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        cons_out.status.success(),
        "consolidate --emit-rust failed: {}",
        String::from_utf8_lossy(&cons_out.stderr)
    );
    let cons_rs = std::fs::read_to_string(&consolidated_rs_path).unwrap();
    assert!(
        cons_rs.contains("pub fn order_id_mix(arg0: i64) -> i64"),
        "expected order_id_mix in consolidated strata.rs, got:\n{cons_rs}"
    );
    assert!(cons_rs.contains("mix_zero_fixed_point"));

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn test_mcp_inline_rust_and_consolidate_emit_rust() {
    let dir = temp_dir("mcp_rust");
    let state = dir.join("mcp_state.json");

    let mut child = Command::new(gnomon_bin())
        .args(["--state", state.to_str().unwrap(), "mcp"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();

    let mut stdin = child.stdin.take().unwrap();
    let stdout = child.stdout.take().unwrap();
    let mut reader = BufReader::new(stdout);

    fn send_rpc(
        stdin: &mut std::process::ChildStdin,
        reader: &mut BufReader<std::process::ChildStdout>,
        msg: Value,
    ) -> Value {
        let line = serde_json::to_string(&msg).unwrap();
        writeln!(stdin, "{line}").unwrap();
        stdin.flush().unwrap();
        let mut resp_line = String::new();
        reader.read_line(&mut resp_line).unwrap();
        serde_json::from_str(&resp_line).unwrap()
    }

    // MCP initialize handshake
    let init = send_rpc(
        &mut stdin,
        &mut reader,
        json!({
            "jsonrpc": "2.0",
            "id": 1,
            "method": "initialize",
            "params": {
                "protocolVersion": "2025-03-26",
                "capabilities": {},
                "clientInfo": {"name": "rust-bridge-test", "version": "0.1"}
            }
        }),
    );
    assert!(init.get("result").is_some(), "init failed: {init}");
    writeln!(
        stdin,
        "{}",
        json!({"jsonrpc": "2.0", "method": "notifications/initialized"})
    )
    .unwrap();
    stdin.flush().unwrap();

    let call_tool = |stdin: &mut std::process::ChildStdin,
                     reader: &mut BufReader<std::process::ChildStdout>,
                     id: u64,
                     name: &str,
                     args: Value|
     -> Value {
        let resp = send_rpc(
            stdin,
            reader,
            json!({
                "jsonrpc": "2.0",
                "id": id,
                "method": "tools/call",
                "params": { "name": name, "arguments": args }
            }),
        );
        assert!(
            resp.get("error").is_none(),
            "MCP tool {name} returned error: {resp}"
        );
        let text = resp["result"]["content"][0]["text"].as_str().unwrap();
        serde_json::from_str(text).unwrap()
    };

    // 1. gnomon_define_op from inline Rust content (auto-detected!)
    let def_v = call_tool(
        &mut stdin,
        &mut reader,
        2,
        "gnomon_define_op",
        json!({
            "name": "order_id_mix",
            "layer": 1,
            "body_content": FMIX64_RS,
            "docstring": "SplitMix64 fmix64"
        }),
    );
    assert_eq!(def_v["stratum_id"], 1);
    assert_eq!(def_v["status"], "CANDIDATE_REGISTERED");

    // 2. gnomon_prove_law from inline Rust using auto-synthesized `mod strata;`!
    let prove_v = call_tool(
        &mut stdin,
        &mut reader,
        3,
        "gnomon_prove_law",
        json!({
            "op": "order_id_mix",
            "name": "mix_zero_fixed_point",
            "input_type": "rust",
            "lhs_content": "#![no_std]\nmod strata;\n#[panic_handler] fn p(_: &core::panic::PanicInfo) -> ! { core::arch::wasm32::unreachable() }\n#[unsafe(no_mangle)] pub extern \"C\" fn f() -> i64 { strata::order_id_mix(0) }",
            "rhs_content": "#![no_std]\n#[panic_handler] fn p(_: &core::panic::PanicInfo) -> ! { core::arch::wasm32::unreachable() }\n#[unsafe(no_mangle)] pub extern \"C\" fn g() -> i64 { 0 }"
        }),
    );
    assert_eq!(prove_v["status"], "PROVED");

    // 3. gnomon_check_goal from inline Rust calling `strata::order_id_mix` twice -> UF CEGAR < 100 ms!
    let t0 = Instant::now();
    let goal_v = call_tool(
        &mut stdin,
        &mut reader,
        4,
        "gnomon_check_goal",
        json!({
            "candidate_content": "#![no_std]\nmod strata;\n#[panic_handler] fn p(_: &core::panic::PanicInfo) -> ! { core::arch::wasm32::unreachable() }\n#[unsafe(no_mangle)] pub extern \"C\" fn c(x: i64, y: i64) -> i64 { strata::order_id_mix(strata::order_id_mix(x)) ^ strata::order_id_mix(strata::order_id_mix(y)) }",
            "spec_content": "#![no_std]\nmod strata;\n#[panic_handler] fn p(_: &core::panic::PanicInfo) -> ! { core::arch::wasm32::unreachable() }\n#[unsafe(no_mangle)] pub extern \"C\" fn s(x: i64, y: i64) -> i64 { strata::order_id_mix(strata::order_id_mix(y)) ^ strata::order_id_mix(strata::order_id_mix(x)) }",
            "timeout_ms": 5000
        }),
    );
    assert_eq!(goal_v["status"], "PROVED");
    assert!(
        goal_v["elapsed_ms"].as_f64().unwrap() < 100.0,
        "MCP UF CEGAR goal took {} ms (wall {:?})",
        goal_v["elapsed_ms"],
        t0.elapsed()
    );

    // 4. gnomon_consolidate with `emit_rust: true` returns `strata_rs`!
    let cons_v = call_tool(
        &mut stdin,
        &mut reader,
        5,
        "gnomon_consolidate",
        json!({
            "min_solutions": 1,
            "emit_rust": true
        }),
    );
    let strata_rs = cons_v["strata_rs"]
        .as_str()
        .expect("emit_rust: true must include strata_rs string");
    assert!(
        strata_rs.contains("pub fn order_id_mix(arg0: i64) -> i64"),
        "expected order_id_mix in MCP strata_rs, got:\n{strata_rs}"
    );
    assert!(strata_rs.contains("mix_zero_fixed_point"));
    assert!(strata_rs.contains("pub fn gnomon_assume(cond: bool)"));

    drop(stdin);
    let _ = child.wait();
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn test_compile_rust_with_explicit_strata_dir() {
    let dir = temp_dir("strata_dir");
    let mut reg = StratumRegistry::new();
    let body = Region::build(|b| {
        b.push_let(ValId(1), ValType::I64, Op::ConstI64(1));
        b.push_let(ValId(2), ValType::I64, Op::Bin(BinOp::I64Add, ValId(0), ValId(1)));
        b.push_yield(&[ValId(2)]);
    });
    reg.register_candidate_op(StratumOp {
        id: StratumId(1),
        name: "add_one_i64".into(),
        layer: 1,
        params: vec![(ValId(0), ValType::I64)],
        results: vec![ValType::I64],
        body,
        docstring: "x + 1".into(),
    })
    .unwrap();
    let strata_code = generate_strata_rs(&reg, true);
    std::fs::write(dir.join("strata.rs"), &strata_code).unwrap();

    let caller_src = r#"#![no_std]
mod strata;
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { core::arch::wasm32::unreachable() }
#[unsafe(no_mangle)]
pub extern "C" fn add_two(x: i64) -> i64 {
    strata::add_one_i64(strata::add_one_i64(x))
}
"#;
    let wasm = compile_rust_to_wasm(caller_src, None, Some(Path::new(&dir))).unwrap();
    let lifted = lift_wasm(&wasm).unwrap();
    assert!(module_has_stratum_imports(&lifted));
    let bound = bind_stratum_imports(lifted, &reg).unwrap();
    assert!(module_has_stratum_calls(&bound));
    let lowered = lower_module_strata(&bound, &reg).unwrap();
    let standalone = emit_wasm(&lowered).unwrap();
    let (res, _) = run_wasmtime_func(&standalone, "add_two", &[Val::I64(40)], 10_000).unwrap();
    assert_eq!(res, ExecOutcome::Values(vec![Val::I64(42)]));

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn test_define_op_oms_s1_1_with_early_return_and_lower_to_wasmtime() {
    let dir = temp_dir("oms_s1_1_strata");
    let state = dir.join("state.json");
    let oms_s1 = repo_root()
        .join("examples")
        .join("oms_strata")
        .join("s1_1_notional_collar.rs");

    for op_name in ["checked_notional", "price_collar_ok"] {
        let out = Command::new(gnomon_bin())
            .args([
                "--state",
                state.to_str().unwrap(),
                "define-op",
                oms_s1.to_str().unwrap(),
                "--name",
                op_name,
                "--layer",
                "1",
            ])
            .output()
            .unwrap();
        assert!(
            out.status.success(),
            "define-op {op_name} failed: stdout={} stderr={}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
    }

    let strata_path = dir.join("strata.rs");
    let emit_out = Command::new(gnomon_bin())
        .args([
            "--state",
            state.to_str().unwrap(),
            "emit-rust",
            strata_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(emit_out.status.success());

    let gate_rs = dir.join("gate.rs");
    std::fs::write(
        &gate_rs,
        r#"#![no_std]
mod strata;
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { core::arch::wasm32::unreachable() }

#[unsafe(no_mangle)]
pub extern "C" fn gate_check(price: i64, qty: i64, max_notional: i64, ref_price: i64, bps: i64) -> i32 {
    let ok1 = strata::checked_notional(price, qty, max_notional);
    let ok2 = strata::price_collar_ok(price, ref_price, bps);
    if ok1 != 0 && ok2 != 0 { 1 } else { 0 }
}
"#,
    )
    .unwrap();

    let standalone_path = dir.join("gate_standalone.wasm");
    let lower_out = Command::new(gnomon_bin())
        .args([
            "--state",
            state.to_str().unwrap(),
            "lift",
            gate_rs.to_str().unwrap(),
            "--lower",
            "--emit-wasm",
            standalone_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        lower_out.status.success(),
        "lift --lower gate.rs failed: {}",
        String::from_utf8_lossy(&lower_out.stderr)
    );
    let wasm = std::fs::read(&standalone_path).unwrap();

    // Case 1: price == ref_price triggers early return in price_collar_ok AND passes notional!
    let (r1, _) = run_wasmtime_func(
        &wasm,
        "gate_check",
        &[Val::I64(100), Val::I64(5), Val::I64(1000), Val::I64(100), Val::I64(50)],
        100_000,
    )
    .unwrap();
    assert_eq!(r1, ExecOutcome::Values(vec![Val::I32(1)]));

    // Case 2: price outside collar -> rejected (0)
    let (r2, _) = run_wasmtime_func(
        &wasm,
        "gate_check",
        &[Val::I64(200), Val::I64(5), Val::I64(1000), Val::I64(100), Val::I64(50)],
        100_000,
    )
    .unwrap();
    assert_eq!(r2, ExecOutcome::Values(vec![Val::I32(0)]));

    // Case 3: notional overflow -> rejected (0)
    let (r3, _) = run_wasmtime_func(
        &wasm,
        "gate_check",
        &[Val::I64(100), Val::I64(11), Val::I64(1000), Val::I64(100), Val::I64(50)],
        100_000,
    )
    .unwrap();
    assert_eq!(r3, ExecOutcome::Values(vec![Val::I32(0)]));

    let _ = std::fs::remove_dir_all(&dir);
}
