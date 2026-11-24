use std::io::{BufRead, BufReader, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::Instant;

use gnomon_kernel::{
    BinOp, EffectOp, LaneKind, MemId, MemWidth, Op, Region, RegionBuilder, UnOp, Val, ValId,
    ValType,
};
use gnomon_mcp::{
    GnomonEngine, InputType, IrDocument, IrTypedVar, IrVal, IrValType, LoadedArtifact,
    generate_strata_rs, load_artifact_bytes_with_registry,
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

fn oms_rs(name: &str) -> PathBuf {
    let p = repo_root()
        .join("examples")
        .join("oms_strata")
        .join(format!("{name}.rs"));
    assert!(p.is_file(), "missing OMS Rust fixture: {}", p.display());
    p
}

fn run_cli_json(args: &[&str], expected_code: i32) -> (Value, std::time::Duration) {
    let t0 = Instant::now();
    let out = Command::new(gnomon_bin()).args(args).output().unwrap();
    let elapsed = t0.elapsed();
    assert_eq!(
        out.status.code(),
        Some(expected_code),
        "CLI {:?} exited {:?} (expected {expected_code})\nstdout={}\nstderr={}",
        args,
        out.status.code(),
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    let v: Value = serde_json::from_slice(&out.stdout).unwrap_or_else(|e| {
        panic!(
            "invalid JSON stdout from {:?}: {e}\nstdout={}",
            args,
            String::from_utf8_lossy(&out.stdout)
        )
    });
    (v, elapsed)
}

#[test]
fn test_ir_codec_tcb_v2_lossless_roundtrip_and_strata_rs_fp_simd() {
    // 1. Exhaustive round-trip of all ValType (5), Val (5), MemWidth (5), LaneKind (8),
    //    UnOp (100), BinOp (141), and Op (17) variants through JSON.
    let val_cases = [
        Val::I32(-42),
        Val::I64(0x1234_5678_9ABC_DEF0u64 as i64),
        Val::F32(0x8000_0000), // -0.0
        Val::F32(0x7FC0_1234), // non-canonical qNaN payload
        Val::F64(0xBFF0_0000_0000_0000),
        Val::V128(0xFEED_FACE_CAFE_BABE_0123_4567_89AB_CDEFu128),
    ];
    for &v in &val_cases {
        let ir_v: IrVal = v.into();
        let json_str = serde_json::to_string(&ir_v).unwrap();
        let decoded: IrVal = serde_json::from_str(&json_str).unwrap();
        assert_eq!(Val::from(decoded), v, "IrVal roundtrip failed for {v:?}");
    }

    let mut b = RegionBuilder::new();
    // Seed typed registers: v0=I32, v1=I64, v2=F32, v3=F64, v4=V128
    b.push_let(ValId(0), ValType::I32, Op::ConstI32(7));
    b.push_let(ValId(1), ValType::I64, Op::ConstI64(11));
    b.push_let(ValId(2), ValType::F32, Op::ConstF32(0x3F80_0000));
    b.push_let(ValId(3), ValType::F64, Op::ConstF64(0x3FF0_0000_0000_0000));
    b.push_let(
        ValId(4),
        ValType::V128,
        Op::ConstV128(0x0102_0304_0506_0708_090A_0B0C_0D0E_0F10),
    );
    let reg_for = |ty: ValType| -> ValId {
        match ty {
            ValType::I32 => ValId(0),
            ValType::I64 => ValId(1),
            ValType::F32 => ValId(2),
            ValType::F64 => ValId(3),
            ValType::V128 => ValId(4),
        }
    };

    let mut next_id = 5u32;
    let mut alloc = || {
        let id = ValId(next_id);
        next_id += 1;
        id
    };

    // Every UnOp (all 100)
    for raw in 0..UnOp::COUNT {
        let uop = UnOp::from_u8(raw).unwrap();
        let dst = alloc();
        b.push_let(dst, uop.output_ty(), Op::Un(uop, reg_for(uop.input_ty())));
    }
    // Every BinOp (all 141)
    for raw in 0..BinOp::COUNT {
        let bop = BinOp::from_u8(raw).unwrap();
        let dst = alloc();
        b.push_let(
            dst,
            bop.output_ty(),
            Op::Bin(bop, reg_for(bop.lhs_ty()), reg_for(bop.rhs_ty())),
        );
    }
    // Every LaneKind (all 8) for extract + replace
    for raw in 0..8u8 {
        let lk = LaneKind::from_u8(raw).unwrap();
        let ex = alloc();
        b.push_let(
            ex,
            lk.scalar_ty(),
            Op::SimdExtractLane { kind: lk, lane: 0, vec: ValId(4) },
        );
        let rp = alloc();
        b.push_let(
            rp,
            ValType::V128,
            Op::SimdReplaceLane {
                kind: lk,
                lane: lk.num_lanes() - 1,
                vec: ValId(4),
                val: ex,
            },
        );
    }
    // SimdBitselect, SimdShuffle, and MemWidth::B16 Load + Store
    let bs = alloc();
    b.push_let(
        bs,
        ValType::V128,
        Op::SimdBitselect { a: ValId(4), b: ValId(4), mask: ValId(4) },
    );
    let sh = alloc();
    b.push_let(
        sh,
        ValType::V128,
        Op::SimdShuffle {
            lhs: ValId(4),
            rhs: bs,
            lanes: [0, 1, 2, 3, 16, 17, 18, 19, 4, 5, 6, 7, 20, 21, 22, 23],
        },
    );
    let ld16 = alloc();
    b.push_let(
        ld16,
        ValType::V128,
        Op::Load {
            mem: MemId(0),
            addr: ValId(0),
            offset: 0,
            width: MemWidth::B16,
            signed: false,
            result_ty: ValType::V128,
        },
    );
    b.push_effect(EffectOp::Store {
        mem: MemId(0),
        addr: ValId(0),
        offset: 16,
        width: MemWidth::B16,
        val: sh,
    });
    b.push_yield(&[ld16]);

    let region: Region = b.finish();
    let doc = IrDocument::from_region(&[], &[ValType::V128], &region);
    let json_text = serde_json::to_string(&doc).unwrap();
    let parsed: IrDocument = serde_json::from_str(&json_text).unwrap();
    assert_eq!(doc, parsed);
    let loaded = parsed.into_loaded().unwrap();
    match loaded {
        LoadedArtifact::Region { results, region: roundtripped, .. } => {
            assert_eq!(results, vec![ValType::V128]);
            assert_eq!(IrDocument::from_region(&[], &results, &roundtripped), doc);
        }
        LoadedArtifact::Module(_) => panic!("expected Region"),
    }

    // 2. Verify `generate_strata_rs` + `rust_bridge` compiles, binds, lowers, and runs
    //    `f32`, `f64`, and `v128` Stratum ops!
    let mut eng = GnomonEngine::new();
    let mut b_f32 = RegionBuilder::new();
    b_f32.push_let(ValId(2), ValType::F32, Op::Bin(BinOp::F32Add, ValId(0), ValId(1)));
    b_f32.push_yield(&[ValId(2)]);
    eng.define_op(
        "add_f32".into(),
        1,
        vec![
            IrTypedVar { id: 0, ty: IrValType::F32 },
            IrTypedVar { id: 1, ty: IrValType::F32 },
        ],
        vec![IrValType::F32],
        b_f32.finish(),
        "Add two f32 values".into(),
        Some(1),
    )
    .unwrap();

    let mut b_f64 = RegionBuilder::new();
    b_f64.push_let(ValId(1), ValType::F64, Op::Un(UnOp::F64Neg, ValId(0)));
    b_f64.push_yield(&[ValId(1)]);
    eng.define_op(
        "neg_f64".into(),
        1,
        vec![IrTypedVar { id: 0, ty: IrValType::F64 }],
        vec![IrValType::F64],
        b_f64.finish(),
        "Negate f64".into(),
        Some(2),
    )
    .unwrap();

    let mut b_v128 = RegionBuilder::new();
    b_v128.push_let(ValId(2), ValType::V128, Op::Bin(BinOp::I32x4Add, ValId(0), ValId(1)));
    b_v128.push_yield(&[ValId(2)]);
    eng.define_op(
        "add_i32x4".into(),
        1,
        vec![
            IrTypedVar { id: 0, ty: IrValType::V128 },
            IrTypedVar { id: 1, ty: IrValType::V128 },
        ],
        vec![IrValType::V128],
        b_v128.finish(),
        "Lane-wise i32x4 add".into(),
        Some(3),
    )
    .unwrap();

    let strata_rs = generate_strata_rs(&eng.registry, true);
    assert!(strata_rs.contains("pub fn add_f32(arg0: f32, arg1: f32) -> f32"));
    assert!(strata_rs.contains("pub fn neg_f64(arg0: f64) -> f64"));
    assert!(
        strata_rs.contains(
            "pub fn add_i32x4(arg0: core::arch::wasm32::v128, arg1: core::arch::wasm32::v128) -> core::arch::wasm32::v128"
        ),
        "strata.rs missing v128 signature:\n{strata_rs}"
    );

    let caller_rs = r#"
#![no_std]
mod strata;
use core::arch::wasm32::*;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

#[unsafe(no_mangle)]
pub extern "C" fn use_strata_fp_simd(a: f32, b: f32, c: f64, x: i32) -> i32 {
    let s = strata::add_f32(a, b);
    let n = strata::neg_f64(c);
    let v = i32x4_add(i32x4_splat(x), i32x4_splat(1));
    i32x4_extract_lane::<0>(v) + (s as i32) + (n as i32)
}
"#;
    let (_, art) = load_artifact_bytes_with_registry(
        caller_rs.as_bytes(),
        InputType::Rust,
        None,
        Some(&eng.registry),
    )
    .unwrap();

    let trace = eng
        .run_trace(
            Some(art),
            Some("use_strata_fp_simd"),
            &[
                IrVal::F32(1.5f32.to_bits()),
                IrVal::F32(2.5f32.to_bits()),
                IrVal::F64(3.0f64.to_bits()),
                IrVal::I32(10),
            ],
            50_000,
        )
        .unwrap();
    assert_eq!(trace.status, "OK", "trace: {trace:?}");
    // (10 + 1) + (1.5 + 2.5) as i32 + (-3.0) as i32 = 11 + 4 - 3 = 12
    assert_eq!(trace.outputs, vec![IrVal::I32(12)]);
}

#[test]
fn test_oms_s3_4_l2_book_sweep_v128_cli_and_mutants() {
    let clean_rs = oms_rs("s3_4_l2_book_sweep_v128");
    let buggy_rs = oms_rs("s3_4_l2_book_sweep_v128_buggy");
    let clean_s = clean_rs.to_str().unwrap();
    let buggy_s = buggy_rs.to_str().unwrap();

    // 1. `sweep_ask_4_v128` ≡ `sweep_ask_4_ref` (check-goal -t rust)
    let (v, dt) = run_cli_json(
        &[
            "-t",
            "rust",
            "check-goal",
            "--candidate",
            clean_s,
            "--candidate-entry",
            "sweep_ask_4_v128",
            "--spec",
            clean_s,
            "--spec-entry",
            "sweep_ask_4_ref",
            "--timeout-ms",
            "30000",
        ],
        0,
    );
    assert_eq!(v["status"], "PROVED", "S3.4 sweep_ask_4 goal: {v}");
    eprintln!("[S3.4] sweep_ask_4_v128 ≡ sweep_ask_4_ref: PROVED in {dt:?}");

    // 2. `contract_sweep_ask_4_equiv` (check-contract -t rust)
    let (v, dt) = run_cli_json(
        &[
            "-t",
            "rust",
            "check-contract",
            clean_s,
            "--entry",
            "contract_sweep_ask_4_equiv",
            "--timeout-ms",
            "30000",
        ],
        0,
    );
    assert_eq!(v["status"], "PROVED", "S3.4 contract_sweep_ask_4_equiv: {v}");
    eprintln!("[S3.4] contract_sweep_ask_4_equiv: PROVED in {dt:?}");

    // 3. `book_sweep_ask_8_v128` ≡ `book_sweep_ask_8_ref` (check-goal -t rust + contract)
    let (v, dt) = run_cli_json(
        &[
            "-t",
            "rust",
            "check-goal",
            "--candidate",
            clean_s,
            "--candidate-entry",
            "book_sweep_ask_8_v128",
            "--spec",
            clean_s,
            "--spec-entry",
            "book_sweep_ask_8_ref",
            "--timeout-ms",
            "30000",
        ],
        0,
    );
    assert_eq!(v["status"], "PROVED", "S3.4 book_sweep_ask_8 goal: {v}");
    eprintln!("[S3.4] book_sweep_ask_8_v128 ≡ book_sweep_ask_8_ref: PROVED in {dt:?}");

    // 4. Inductive L2 book suite (`--init init_l2_book --ops book_set_bid,book_set_ask --invariant inv_l2_book`)
    let (v, dt) = run_cli_json(
        &[
            "-t",
            "rust",
            "check-contract",
            clean_s,
            "--init",
            "init_l2_book",
            "--ops",
            "book_set_bid,book_set_ask",
            "--invariant",
            "inv_l2_book",
            "--timeout-ms",
            "30000",
        ],
        0,
    );
    assert_eq!(v["status"], "PROVED", "S3.4 inductive L2 book suite: {v}");
    assert_eq!(v["mode"], "inductive_suite");
    let op_results = v["op_results"].as_array().unwrap();
    assert_eq!(op_results.len(), 3);
    assert_eq!(op_results[0]["entry"], "init_l2_book");
    assert_eq!(op_results[0]["status"], "PROVED");
    assert_eq!(op_results[1]["entry"], "book_set_bid");
    assert_eq!(op_results[1]["status"], "PROVED");
    assert_eq!(op_results[2]["entry"], "book_set_ask");
    assert_eq!(op_results[2]["status"], "PROVED");
    eprintln!("[S3.4] inductive L2 book suite (init + 2 ops): PROVED in {dt:?}");

    // 5. Mutant 1: `contract_sweep_ask_4_equiv_buggy` (`i32x4.lt` misses `p_i == limit_px`) -> FALSIFIED
    let (v, dt) = run_cli_json(
        &[
            "-t",
            "rust",
            "check-contract",
            buggy_s,
            "--entry",
            "contract_sweep_ask_4_equiv_buggy",
            "--timeout-ms",
            "30000",
        ],
        1,
    );
    assert_eq!(v["status"], "FALSIFIED", "S3.4 Mutant 1: {v}");
    let scalars = v["counterexample"]["scalar_values"].as_array().unwrap();
    assert_eq!(scalars.len(), 9, "expected 9 i32 params: {scalars:?}");
    let vals: Vec<i32> = scalars
        .iter()
        .map(|pair| pair[1]["val"].as_i64().unwrap() as i32)
        .collect();
    let limit_px = vals[8];
    let witness_matches = (0..4).any(|i| vals[i] == limit_px && vals[i + 4] > 0);
    assert!(
        witness_matches,
        "Mutant 1 counterexample should have some p_i == limit_px && q_i > 0, got {vals:?}"
    );
    eprintln!("[S3.4] Mutant 1 (contract_sweep_ask_4_equiv_buggy): FALSIFIED in {dt:?}");

    // 6. Mutant 2: `contract_book_set_bid_preserves_inv_buggy` (crossed book) -> FALSIFIED
    let (v, dt) = run_cli_json(
        &[
            "-t",
            "rust",
            "check-contract",
            buggy_s,
            "--entry",
            "contract_book_set_bid_preserves_inv_buggy",
            "--timeout-ms",
            "30000",
        ],
        1,
    );
    assert_eq!(v["status"], "FALSIFIED", "S3.4 Mutant 2: {v}");
    assert_eq!(
        v["counterexample"]["scalar_values"].as_array().unwrap().len(),
        3
    );
    eprintln!("[S3.4] Mutant 2 (contract_book_set_bid_preserves_inv_buggy): FALSIFIED in {dt:?}");
}

#[test]
fn test_oms_s3_5_signal_vwap_var_v128_cli_and_mutants() {
    let clean_rs = oms_rs("s3_5_signal_vwap_var_v128");
    let buggy_rs = oms_rs("s3_5_signal_vwap_var_v128_buggy");
    let clean_s = clean_rs.to_str().unwrap();
    let buggy_s = buggy_rs.to_str().unwrap();

    // 1. `vwap_4_v128` ≡ `vwap_4_ref` (check-goal -t rust) & `contract_vwap_4_equiv`
    let (v, dt) = run_cli_json(
        &[
            "-t",
            "rust",
            "check-goal",
            "--candidate",
            clean_s,
            "--candidate-entry",
            "vwap_4_v128",
            "--spec",
            clean_s,
            "--spec-entry",
            "vwap_4_ref",
            "--timeout-ms",
            "30000",
        ],
        0,
    );
    assert_eq!(v["status"], "PROVED", "S3.5 vwap_4_v128 ≡ vwap_4_ref: {v}");
    eprintln!("[S3.5] vwap_4_v128 ≡ vwap_4_ref: PROVED in {dt:?}");

    let (v, dt) = run_cli_json(
        &[
            "-t",
            "rust",
            "check-contract",
            clean_s,
            "--entry",
            "contract_vwap_4_equiv",
            "--timeout-ms",
            "30000",
        ],
        0,
    );
    assert_eq!(v["status"], "PROVED", "S3.5 contract_vwap_4_equiv: {v}");
    eprintln!("[S3.5] contract_vwap_4_equiv: PROVED in {dt:?}");

    // 2. `vwap_4_v128` under `req_vwap_4_nonneg_finite` => `ens_vwap_4_safe`
    let (v, dt) = run_cli_json(
        &[
            "-t",
            "rust",
            "check-contract",
            clean_s,
            "--entry",
            "vwap_4_v128",
            "--requires",
            "req_vwap_4_nonneg_finite",
            "--ensures",
            "ens_vwap_4_safe",
            "--timeout-ms",
            "30000",
        ],
        0,
    );
    assert_eq!(v["status"], "PROVED", "S3.5 vwap_4_v128 safe: {v}");
    eprintln!("[S3.5] vwap_4_v128 (req => ens_vwap_4_safe): PROVED in {dt:?}");

    // 3. `quote_ticks_from_fair` under `req_fair_valid` => `ens_quotes_non_crossed`
    let (v, dt) = run_cli_json(
        &[
            "-t",
            "rust",
            "check-contract",
            clean_s,
            "--entry",
            "quote_ticks_from_fair",
            "--requires",
            "req_fair_valid",
            "--ensures",
            "ens_quotes_non_crossed",
            "--timeout-ms",
            "30000",
        ],
        0,
    );
    assert_eq!(v["status"], "PROVED", "S3.5 quote_ticks_from_fair: {v}");
    eprintln!("[S3.5] quote_ticks_from_fair (bid_tick < ask_tick): PROVED in {dt:?}");

    // 4. `signal_dir_safe` => `ens_signal_dir` (`-0.0` safe)
    let (v, dt) = run_cli_json(
        &[
            "-t",
            "rust",
            "check-contract",
            clean_s,
            "--entry",
            "signal_dir_safe",
            "--ensures",
            "ens_signal_dir",
            "--timeout-ms",
            "30000",
        ],
        0,
    );
    assert_eq!(v["status"], "PROVED", "S3.5 signal_dir_safe: {v}");
    eprintln!("[S3.5] signal_dir_safe => ens_signal_dir: PROVED in {dt:?}");

    // 5. `portfolio_notional_4_v128` ≡ `portfolio_notional_4_ref`
    let (v, dt) = run_cli_json(
        &[
            "-t",
            "rust",
            "check-goal",
            "--candidate",
            clean_s,
            "--candidate-entry",
            "portfolio_notional_4_v128",
            "--spec",
            clean_s,
            "--spec-entry",
            "portfolio_notional_4_ref",
            "--timeout-ms",
            "30000",
        ],
        0,
    );
    assert_eq!(
        v["status"], "PROVED",
        "S3.5 portfolio_notional_4_v128 ≡ portfolio_notional_4_ref: {v}"
    );
    eprintln!(
        "[S3.5] portfolio_notional_4_v128 ≡ portfolio_notional_4_ref: PROVED in {dt:?}"
    );

    // 6. Mutant 1: `contract_vwap_4_safe_buggy` (`0.0 / 0.0 = NaN` on empty book) -> FALSIFIED
    let (v, dt) = run_cli_json(
        &[
            "-t",
            "rust",
            "check-contract",
            buggy_s,
            "--entry",
            "contract_vwap_4_safe_buggy",
            "--timeout-ms",
            "30000",
        ],
        1,
    );
    assert_eq!(v["status"], "FALSIFIED", "S3.5 Mutant 1: {v}");
    let scalars = v["counterexample"]["scalar_values"].as_array().unwrap();
    assert_eq!(scalars.len(), 8);
    let q_sum: f32 = (4..8)
        .map(|i| {
            assert_eq!(scalars[i][1]["ty"], "f32");
            f32::from_bits(scalars[i][1]["val"].as_u64().unwrap() as u32)
        })
        .sum();
    assert_eq!(
        q_sum, 0.0,
        "Mutant 1 counterexample should have total_q == 0.0 (causing 0.0/0.0=NaN): {scalars:?}"
    );
    eprintln!("[S3.5] Mutant 1 (contract_vwap_4_safe_buggy): FALSIFIED in {dt:?}");

    // 7. Mutant 2: `contract_signal_dir_buggy` (exact `-0.0` sign-bit witness) -> FALSIFIED
    let (v, dt) = run_cli_json(
        &[
            "-t",
            "rust",
            "check-contract",
            buggy_s,
            "--entry",
            "contract_signal_dir_buggy",
            "--timeout-ms",
            "30000",
        ],
        1,
    );
    assert_eq!(v["status"], "FALSIFIED", "S3.5 Mutant 2: {v}");
    let scalars = v["counterexample"]["scalar_values"].as_array().unwrap();
    assert_eq!(scalars.len(), 1);
    assert_eq!(scalars[0][1]["ty"], "f32");
    assert_eq!(
        scalars[0][1]["val"].as_u64().unwrap() as u32,
        0x8000_0000,
        "Mutant 2 unique counterexample MUST be exact -0.0 (0x8000_0000), got {scalars:?}"
    );
    eprintln!(
        "[S3.5] Mutant 2 (contract_signal_dir_buggy): FALSIFIED on exact -0.0 (0x8000_0000) in {dt:?}"
    );

    // 8. Mutant 3: `contract_quote_ticks_buggy` (self-crossed `bid >= ask`) -> FALSIFIED
    let (v, dt) = run_cli_json(
        &[
            "-t",
            "rust",
            "check-contract",
            buggy_s,
            "--entry",
            "contract_quote_ticks_buggy",
            "--timeout-ms",
            "30000",
        ],
        1,
    );
    assert_eq!(v["status"], "FALSIFIED", "S3.5 Mutant 3: {v}");
    let scalars = v["counterexample"]["scalar_values"].as_array().unwrap();
    assert_eq!(scalars.len(), 2);
    assert_eq!(scalars[0][1]["ty"], "f32");
    assert_eq!(scalars[1][1]["ty"], "i32");
    let half_spread = scalars[1][1]["val"].as_i64().unwrap() as i32;
    assert!(
        (1..=100_000_000).contains(&half_spread),
        "Mutant 3 counterexample half_spread out of req_fair_valid range: {scalars:?}"
    );
    eprintln!("[S3.5] Mutant 3 (contract_quote_ticks_buggy): FALSIFIED in {dt:?}");
}

#[test]
fn test_oms_s3_4_and_s3_5_e2e_via_mcp_stdio() {
    let s3_4 = oms_rs("s3_4_l2_book_sweep_v128");
    let s3_4_buggy = oms_rs("s3_4_l2_book_sweep_v128_buggy");
    let s3_5 = oms_rs("s3_5_signal_vwap_var_v128");
    let s3_5_buggy = oms_rs("s3_5_signal_vwap_var_v128_buggy");

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
                "clientInfo": { "name": "oms-fp-simd-e2e", "version": "0.1.0" }
            }
        }),
    );
    assert!(init_resp["error"].is_null());
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

    // 1. `gnomon_lift_check` on S3.5 Rust source (`input_type: "rust"`)
    let lifted = call_tool(
        &mut stdin,
        &mut reader,
        2,
        "gnomon_lift_check",
        json!({
            "path": s3_5.to_str().unwrap(),
            "input_type": "rust"
        }),
    );
    assert_eq!(lifted["input_type"], "rust");
    assert!(lifted["functions"].as_array().unwrap().len() >= 19);

    // 2. `gnomon_run_trace` with `IrVal::F32(0x8000_0000)` (-0.0) on clean vs buggy `signal_dir`
    let trace_clean = call_tool(
        &mut stdin,
        &mut reader,
        3,
        "gnomon_run_trace",
        json!({
            "path": s3_5.to_str().unwrap(),
            "input_type": "rust",
            "entry": "signal_dir_safe",
            "inputs": [{"ty": "f32", "val": 0x8000_0000u32}]
        }),
    );
    assert_eq!(trace_clean["status"], "OK");
    assert_eq!(trace_clean["outputs"], json!([{"ty": "i32", "val": 0}]));

    let trace_buggy = call_tool(
        &mut stdin,
        &mut reader,
        4,
        "gnomon_run_trace",
        json!({
            "path": s3_5_buggy.to_str().unwrap(),
            "input_type": "rust",
            "entry": "signal_dir_buggy_neg_zero",
            "inputs": [{"ty": "f32", "val": 0x8000_0000u32}]
        }),
    );
    assert_eq!(trace_buggy["status"], "OK");
    assert_eq!(trace_buggy["outputs"], json!([{"ty": "i32", "val": -1}]));

    // 3. S3.4 `gnomon_check_goal` (`sweep_ask_4_v128` ≡ `sweep_ask_4_ref`) & inductive L2 suite via MCP
    let s3_4_goal = call_tool(
        &mut stdin,
        &mut reader,
        5,
        "gnomon_check_goal",
        json!({
            "candidate_path": s3_4.to_str().unwrap(),
            "candidate_entry": "sweep_ask_4_v128",
            "spec_path": s3_4.to_str().unwrap(),
            "spec_entry": "sweep_ask_4_ref",
            "input_type": "rust",
            "timeout_ms": 30000
        }),
    );
    assert_eq!(s3_4_goal["status"], "PROVED", "MCP S3.4 goal: {s3_4_goal}");

    let s3_4_suite = call_tool(
        &mut stdin,
        &mut reader,
        6,
        "gnomon_check_contract",
        json!({
            "path": s3_4.to_str().unwrap(),
            "input_type": "rust",
            "init": "init_l2_book",
            "ops": ["book_set_bid", "book_set_ask"],
            "invariant": "inv_l2_book",
            "timeout_ms": 30000
        }),
    );
    assert_eq!(s3_4_suite["status"], "PROVED", "MCP S3.4 suite: {s3_4_suite}");

    let s3_4_m1 = call_tool(
        &mut stdin,
        &mut reader,
        7,
        "gnomon_check_contract",
        json!({
            "path": s3_4_buggy.to_str().unwrap(),
            "input_type": "rust",
            "entry": "contract_sweep_ask_4_equiv_buggy",
            "timeout_ms": 30000
        }),
    );
    assert_eq!(s3_4_m1["status"], "FALSIFIED", "MCP S3.4 m1: {s3_4_m1}");

    // 4. S3.5 `gnomon_check_contract` clean (`quote_ticks_from_fair`, `vwap_4_v128`) + Mutant 2 `-0.0` via MCP
    let s3_5_quotes = call_tool(
        &mut stdin,
        &mut reader,
        8,
        "gnomon_check_contract",
        json!({
            "path": s3_5.to_str().unwrap(),
            "input_type": "rust",
            "entry": "quote_ticks_from_fair",
            "requires": "req_fair_valid",
            "ensures": "ens_quotes_non_crossed",
            "timeout_ms": 30000
        }),
    );
    assert_eq!(s3_5_quotes["status"], "PROVED", "MCP S3.5 quotes: {s3_5_quotes}");

    let s3_5_vwap_safe = call_tool(
        &mut stdin,
        &mut reader,
        9,
        "gnomon_check_contract",
        json!({
            "path": s3_5.to_str().unwrap(),
            "input_type": "rust",
            "entry": "vwap_4_v128",
            "requires": "req_vwap_4_nonneg_finite",
            "ensures": "ens_vwap_4_safe",
            "timeout_ms": 30000
        }),
    );
    assert_eq!(
        s3_5_vwap_safe["status"], "PROVED",
        "MCP S3.5 vwap safe: {s3_5_vwap_safe}"
    );

    let s3_5_m2 = call_tool(
        &mut stdin,
        &mut reader,
        10,
        "gnomon_check_contract",
        json!({
            "path": s3_5_buggy.to_str().unwrap(),
            "input_type": "rust",
            "entry": "contract_signal_dir_buggy",
            "timeout_ms": 30000
        }),
    );
    assert_eq!(s3_5_m2["status"], "FALSIFIED", "MCP S3.5 m2: {s3_5_m2}");
    assert_eq!(
        s3_5_m2["counterexample"]["scalar_values"][0][1],
        json!({"ty": "f32", "val": 0x8000_0000u32})
    );

    drop(stdin);
    let status = child.wait().unwrap();
    assert!(status.success());
    let _ = Path::new(&s3_4);
}
