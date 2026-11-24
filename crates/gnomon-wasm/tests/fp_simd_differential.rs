use std::path::PathBuf;

use gnomon_kernel::{FuncId, Val, ValType};
use gnomon_wasm::{
    ExecOutcome, FuzzConfig, FuzzOutcome, differential_check, emit_wasm, fuzz_equivalence,
    lift_wasm, run_wasmtime_func, verify_round_trip,
};
use wasm_encoder::{
    BlockType, CodeSection, ConstExpr, ExportKind, ExportSection, Function, FunctionSection,
    GlobalSection, GlobalType, Ieee32, Ieee64, InstructionSink, MemArg, MemArgTarget,
    MemorySection, MemoryType, Module as WasmModule, TypeSection, ValType as WVal,
};

type EmitFn = fn(&mut InstructionSink<'_>);

fn ma(mem: u32, offset: u64, align: u32) -> MemArg {
    MemArg {
        offset,
        align,
        target: MemArgTarget::Memory(mem),
        ordering: None,
    }
}

fn single_fn(
    params: &[WVal],
    results: &[WVal],
    locals: &[(u32, WVal)],
    build: impl FnOnce(&mut InstructionSink<'_>),
) -> Vec<u8> {
    let mut m = WasmModule::new();
    let mut ts = TypeSection::new();
    ts.ty().function(params.iter().copied(), results.iter().copied());
    m.section(&ts);

    let mut fs = FunctionSection::new();
    fs.function(0);
    m.section(&fs);

    let mut exps = ExportSection::new();
    exps.export("f", ExportKind::Func, 0);
    m.section(&exps);

    let mut cs = CodeSection::new();
    let mut f = Function::new(locals.iter().copied());
    {
        let mut sink = f.instructions();
        build(&mut sink);
        sink.end();
    }
    cs.function(&f);
    m.section(&cs);
    m.finish()
}

fn mem_fn(
    params: &[WVal],
    results: &[WVal],
    locals: &[(u32, WVal)],
    build: impl FnOnce(&mut InstructionSink<'_>),
) -> Vec<u8> {
    let mut m = WasmModule::new();
    let mut ts = TypeSection::new();
    ts.ty().function(params.iter().copied(), results.iter().copied());
    m.section(&ts);

    let mut fs = FunctionSection::new();
    fs.function(0);
    m.section(&fs);

    let mut ms = MemorySection::new();
    ms.memory(MemoryType {
        minimum: 1,
        maximum: Some(1),
        memory64: false,
        shared: false,
        page_size_log2: None,
    });
    m.section(&ms);

    let mut exps = ExportSection::new();
    exps.export("f", ExportKind::Func, 0);
    exps.export("mem", ExportKind::Memory, 0);
    m.section(&exps);

    let mut cs = CodeSection::new();
    let mut f = Function::new(locals.iter().copied());
    {
        let mut sink = f.instructions();
        build(&mut sink);
        sink.end();
    }
    cs.function(&f);
    m.section(&cs);
    m.finish()
}

const fn pack_u32x4(a: u32, b: u32, c: u32, d: u32) -> u128 {
    (a as u128) | ((b as u128) << 32) | ((c as u128) << 64) | ((d as u128) << 96)
}

const fn pack_u64x2(a: u64, b: u64) -> u128 {
    (a as u128) | ((b as u128) << 64)
}

const F32_CORNERS: &[u32] = &[
    0x0000_0000, // +0.0
    0x8000_0000, // -0.0
    0x0000_0001, // +subnormal_min
    0x8000_0001, // -subnormal_min
    0x007f_ffff, // +subnormal_max
    0x807f_ffff, // -subnormal_max
    0x0080_0000, // +normal_min
    0x8080_0000, // -normal_min
    0x3f00_0000, // +0.5
    0xbf00_0000, // -0.5
    0x3f7f_ffff, // next_down(1.0)
    0xbf7f_ffff, // next_up(-1.0)
    0x3f80_0000, // +1.0
    0xbf80_0000, // -1.0
    0x3fc0_0000, // +1.5
    0xbfc0_0000, // -1.5
    0x4000_0000, // +2.0
    0xc000_0000, // -2.0
    0x4020_0000, // +2.5
    0xc020_0000, // -2.5
    0x4eff_ffff, // largest f32 < 2^31
    0x4f00_0000, // +2^31
    0xcf00_0000, // -2^31 (i32::MIN)
    0xcf00_0001, // next_down(-2^31)
    0x4f7f_ffff, // largest f32 < 2^32
    0x4f80_0000, // +2^32
    0x5eff_ffff, // largest f32 < 2^63
    0x5f00_0000, // +2^63
    0xdf00_0000, // -2^63
    0xdf00_0001, // next_down(-2^63)
    0x5f7f_ffff, // largest f32 < 2^64
    0x5f80_0000, // +2^64
    0x7f7f_ffff, // +f32::MAX
    0xff7f_ffff, // -f32::MAX
    0x7f80_0000, // +Inf
    0xff80_0000, // -Inf
    0x7fc0_0000, // canonical qNaN
    0xffc0_0000, // negative qNaN
    0x7fc0_1234, // non-canonical qNaN
    0x7f80_0001, // sNaN
];

const F64_CORNERS: &[u64] = &[
    0x0000_0000_0000_0000, // +0.0
    0x8000_0000_0000_0000, // -0.0
    0x0000_0000_0000_0001, // +subnormal_min
    0x8000_0000_0000_0001, // -subnormal_min
    0x000f_ffff_ffff_ffff, // +subnormal_max
    0x0010_0000_0000_0000, // +normal_min
    0x3fe0_0000_0000_0000, // +0.5
    0xbfe0_0000_0000_0000, // -0.5
    0x3fef_ffff_ffff_ffff, // next_down(1.0)
    0xbfef_ffff_ffff_ffff, // next_up(-1.0)
    0x3ff0_0000_0000_0000, // +1.0
    0xbff0_0000_0000_0000, // -1.0
    0x3ff8_0000_0000_0000, // +1.5
    0xbff8_0000_0000_0000, // -1.5
    0x4004_0000_0000_0000, // +2.5
    0xc004_0000_0000_0000, // -2.5
    0x41df_ffff_ffff_ffff, // next_down(2^31)
    0x41e0_0000_0000_0000, // +2^31
    0xc1e0_0000_0000_0000, // -2^31
    0xc1e0_0000_001c_cccc, // -2147483648.9 (valid for i32.trunc_f64_s!)
    0xc1e0_0000_0020_0000, // -2147483649.0 (traps i32.trunc_f64_s!)
    0x41ef_ffff_ffff_ffff, // next_down(2^32)
    0x41f0_0000_0000_0000, // +2^32
    0x43df_ffff_ffff_ffff, // largest f64 < 2^63
    0x43e0_0000_0000_0000, // +2^63
    0xc3e0_0000_0000_0000, // -2^63
    0xc3e0_0000_0000_0001, // next_down(-2^63)
    0x43ef_ffff_ffff_ffff, // largest f64 < 2^64
    0x43f0_0000_0000_0000, // +2^64
    0x7fef_ffff_ffff_ffff, // +f64::MAX
    0xffef_ffff_ffff_ffff, // -f64::MAX
    0x7ff0_0000_0000_0000, // +Inf
    0xfff0_0000_0000_0000, // -Inf
    0x7ff8_0000_0000_0000, // canonical qNaN
    0xfff8_0000_0000_0000, // negative qNaN
    0x7ff8_0000_0000_0001, // non-canonical qNaN
    0x7ff0_0000_0000_0001, // sNaN
];

const V128_CORNERS: &[u128] = &[
    0u128,
    u128::MAX,
    0x5555_5555_5555_5555_5555_5555_5555_5555u128,
    0xAAAA_AAAA_AAAA_AAAA_AAAA_AAAA_AAAA_AAAAu128,
    u128::from_le_bytes([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]),
    u128::from_le_bytes([0, 15, 16, 17, 31, 32, 127, 128, 255, 1, 2, 3, 14, 15, 16, 200]),
    pack_u32x4(0, 1, u32::MAX, 0x8000_0000),
    pack_u32x4(0x7fff_ffff, 0x8000_0000, u32::MAX, 0),
    pack_u64x2(0x8000_0000_0000_0000, 0x7fff_ffff_ffff_ffff),
    pack_u32x4(0x0000_0000, 0x8000_0000, 0x3f80_0000, 0xbf80_0000),
    pack_u32x4(0x8000_0000, 0x0000_0000, 0xbf80_0000, 0x3f80_0000),
    pack_u32x4(0x7f80_0000, 0xff80_0000, 0x7fc0_0000, 0x7f80_0001),
    pack_u32x4(0x7fc0_0001, 0xffc0_1234, 0xbf00_0000, 0x4020_0000),
    pack_u32x4(0x0000_0001, 0x8000_0001, 0x7f7f_ffff, 0xff7f_ffff),
    pack_u32x4(0xcf00_0000, 0x4f00_0000, 0xbf80_0000, 0x4f80_0000),
    pack_u64x2(0x0000_0000_0000_0000, 0x8000_0000_0000_0000),
    pack_u64x2(0x8000_0000_0000_0000, 0x0000_0000_0000_0000),
    pack_u64x2(0x7ff0_0000_0000_0000, 0xfff0_0000_0000_0000),
    pack_u64x2(0x7ff8_0000_0000_0000, 0x7ff0_0000_0000_0001),
    pack_u64x2(0x0000_0000_0000_0001, 0xbfe0_0000_0000_0000),
];

fn next_rng(seed: &mut u64) -> u64 {
    *seed = seed.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = *seed;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

fn gen_args_for_params(params: &[ValType], count: usize, seed: &mut u64) -> Vec<Vec<Val>> {
    if params.is_empty() {
        return vec![vec![]];
    }
    let i32_c: &[i32] = &[0, 1, -1, 2, -2, 7, 16, 100, -100, i32::MAX, i32::MIN];
    let i64_c: &[i64] = &[0, 1, -1, 2, 100, -100, i32::MAX as i64, i64::MAX, i64::MIN];
    let mut out = Vec::with_capacity(count);
    for k in 0..count {
        let mut row = Vec::with_capacity(params.len());
        for (p_idx, &ty) in params.iter().enumerate() {
            let v = if k < 12 {
                let idx = k + p_idx;
                match ty {
                    ValType::I32 => Val::I32(i32_c[idx % i32_c.len()]),
                    ValType::I64 => Val::I64(i64_c[idx % i64_c.len()]),
                    ValType::F32 => Val::F32(F32_CORNERS[idx % F32_CORNERS.len()]),
                    ValType::F64 => Val::F64(F64_CORNERS[idx % F64_CORNERS.len()]),
                    ValType::V128 => Val::V128(V128_CORNERS[idx % V128_CORNERS.len()]),
                }
            } else {
                let r = next_rng(seed);
                match ty {
                    ValType::I32 => Val::I32((r as i32) & 0x7fff),
                    ValType::I64 => Val::I64(r as i64),
                    ValType::F32 => {
                        if (r & 1) == 0 {
                            Val::F32(F32_CORNERS[(r >> 4) as usize % F32_CORNERS.len()])
                        } else {
                            Val::F32(r as u32)
                        }
                    }
                    ValType::F64 => {
                        if (r & 1) == 0 {
                            Val::F64(F64_CORNERS[(r >> 4) as usize % F64_CORNERS.len()])
                        } else {
                            Val::F64(r)
                        }
                    }
                    ValType::V128 => {
                        let hi = next_rng(seed);
                        Val::V128((r as u128) | ((hi as u128) << 64))
                    }
                }
            };
            row.push(v);
        }
        out.push(row);
    }
    out
}

#[test]
fn test_oms_s3_4_and_s3_5_wasm_lift_roundtrip_and_differential() {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let oms_dir = manifest_dir.join("../../examples/oms_strata/out");
    let files = [
        "s3_4_l2_book_sweep_v128.wasm",
        "s3_4_l2_book_sweep_v128_buggy.wasm",
        "s3_5_signal_vwap_var_v128.wasm",
        "s3_5_signal_vwap_var_v128_buggy.wasm",
    ];

    let mut seed = 0x5334_5335_0001_u64;
    let mut total_oms_checks = 0usize;

    for fname in files {
        let path = oms_dir.join(fname);
        let bytes = std::fs::read(&path)
            .unwrap_or_else(|e| panic!("failed to read {}: {e}", path.display()));

        // 1. Lift -> Emit (self-validated via wasmparser::Validator) -> Re-lift
        let lifted = lift_wasm(&bytes)
            .unwrap_or_else(|e| panic!("lift_wasm failed on {fname}: {e}"));
        let reemitted = emit_wasm(&lifted)
            .unwrap_or_else(|e| panic!("emit_wasm failed on {fname}: {e}"));
        let relifted = lift_wasm(&reemitted)
            .unwrap_or_else(|e| panic!("re-lift failed on {fname}: {e}"));

        assert_eq!(lifted.funcs.len(), relifted.funcs.len(), "{fname}: func count mismatch");
        assert_eq!(lifted.memories.len(), relifted.memories.len(), "{fname}: mem count mismatch");
        assert_eq!(lifted.globals.len(), relifted.globals.len(), "{fname}: global count mismatch");

        // 2. Differential check EVERY exported function bit-for-bit across kernel, orig wasmtime, roundtrip wasmtime
        for func in &lifted.funcs {
            if func.export_name.is_none() {
                continue;
            }
            let param_tys: Vec<ValType> = func.params.iter().map(|&(_, t)| t).collect();
            let vecs = gen_args_for_params(&param_tys, 24, &mut seed);
            differential_check(&bytes, func.id, &vecs, 500_000).unwrap_or_else(|e| {
                panic!(
                    "OMS differential failure in {fname}::{}: {e}",
                    func.name
                )
            });
            total_oms_checks += vecs.len();
        }

        // 3. Stage-1 round-trip fuzz on first 2 exported functions of each file
        for func in lifted.funcs.iter().filter(|f| f.export_name.is_some()).take(2) {
            let rt = verify_round_trip(
                &bytes,
                func.id,
                &FuzzConfig {
                    total_vectors: 500,
                    fuel_per_run: 500_000,
                    seed: 0x3435,
                },
            )
            .unwrap_or_else(|e| panic!("verify_round_trip failed on {fname}::{}: {e}", func.name));
            assert!(
                matches!(rt, FuzzOutcome::NoCounterexample { .. }),
                "unexpected roundtrip falsification on {fname}::{}: {rt:?}",
                func.name
            );
        }
    }

    println!("All 4 S3.4/S3.5 OMS SIMD/FP .wasm files lifted, round-tripped, and verified ({total_oms_checks} differential checks)!");
    assert!(total_oms_checks >= 500);
}

#[test]
fn test_fp_and_v128_globals_locals_mem_select_and_dead_code() {
    // Tests:
    // - F32, F64, V128 mutable & immutable globals (`eval_const_expr` & `GlobalSection`)
    // - F32, F64, V128 zero-initialized locals
    // - F32, F64, V128 loads & stores (including OOB wrap traps)
    // - F32, F64, V128 `select` & `typed_select`
    // - Dead/unreachable code containing FP and `v128` ops (`check_supported_op`)
    let mut m = WasmModule::new();
    let mut ts = TypeSection::new();
    ts.ty().function(
        [WVal::I32, WVal::F32, WVal::F64, WVal::V128],
        [WVal::F32, WVal::F64, WVal::V128],
    );
    m.section(&ts);

    let mut fs = FunctionSection::new();
    fs.function(0);
    m.section(&fs);

    let mut ms = MemorySection::new();
    ms.memory(MemoryType {
        minimum: 1,
        maximum: Some(1),
        memory64: false,
        shared: false,
        page_size_log2: None,
    });
    m.section(&ms);

    let mut gs = GlobalSection::new();
    gs.global(
        GlobalType { val_type: WVal::F32, mutable: true, shared: false },
        &ConstExpr::f32_const(Ieee32::new(0xbf80_0000)), // -1.0f32
    );
    gs.global(
        GlobalType { val_type: WVal::F64, mutable: true, shared: false },
        &ConstExpr::f64_const(Ieee64::new(0x4004_0000_0000_0000)), // 2.5f64
    );
    gs.global(
        GlobalType { val_type: WVal::V128, mutable: true, shared: false },
        &ConstExpr::v128_const(pack_u32x4(1, 2, 3, 4) as i128),
    );
    m.section(&gs);

    let mut exps = ExportSection::new();
    exps.export("f", ExportKind::Func, 0);
    exps.export("mem", ExportKind::Memory, 0);
    exps.export("gf32", ExportKind::Global, 0);
    exps.export("gf64", ExportKind::Global, 1);
    exps.export("gv128", ExportKind::Global, 2);
    m.section(&exps);

    let mut cs = CodeSection::new();
    // Locals: 0=addr(i32), 1=x(f32), 2=y(f64), 3=v(v128), 4=lf32, 5=lf64, 6=lv128
    let mut f = Function::new([(1, WVal::F32), (1, WVal::F64), (1, WVal::V128)]);
    {
        let mut s = f.instructions();
        // Store at addr + 0 (f32), addr + 8 (f64), addr + 16 (v128)
        s.local_get(0).local_get(1).global_get(0).f32_add().f32_store(ma(0, 0, 2));
        s.local_get(0).local_get(2).global_get(1).f64_sub().f64_store(ma(0, 8, 3));
        s.local_get(0).local_get(3).global_get(2).v128_xor().v128_store(ma(0, 16, 4));

        // Load back and combine with zero-initialized locals via select / typed_select
        s.local_get(0).f32_load(ma(0, 0, 2)).local_get(4).local_get(0).i32_const(1).i32_and().select().local_set(4);
        s.local_get(0).f64_load(ma(0, 8, 3)).local_get(5).local_get(0).i32_const(2).i32_and().typed_select(WVal::F64).local_set(5);
        s.local_get(0).v128_load(ma(0, 16, 4)).local_get(6).local_get(0).i32_const(4).i32_and().typed_select(WVal::V128).local_set(6);

        // Update mutable globals
        s.local_get(4).global_set(0);
        s.local_get(5).global_set(1);
        s.local_get(6).global_set(2);

        // Exercise dead-code FP/SIMD validation path inside a block with unconditional br
        s.block(BlockType::Empty);
        s.br(0);
        s.f32_const(Ieee32::new(0x3f80_0000))
            .f32_abs()
            .drop()
            .f64_const(Ieee64::new(0x3ff0_0000_0000_0000))
            .f64_sqrt()
            .drop()
            .v128_const(0)
            .i32x4_extract_lane(0)
            .drop()
            .v128_const(0)
            .i32_const(1)
            .i32x4_replace_lane(1)
            .v128_const(0)
            .v128_const(0)
            .v128_bitselect()
            .v128_const(0)
            .i8x16_shuffle([0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23])
            .i32_const(0)
            .drop()
            .drop()
            .i32_const(0)
            .f32_load(ma(0, 0, 2))
            .drop()
            .i32_const(0)
            .f64_load(ma(0, 0, 3))
            .drop()
            .i32_const(0)
            .v128_load(ma(0, 0, 4))
            .drop();
        s.end();

        s.local_get(4).local_get(5).local_get(6);
        s.end();
    }
    cs.function(&f);
    m.section(&cs);
    let wasm = m.finish();

    let vecs = vec![
        vec![Val::I32(0), Val::F32(0x8000_0000), Val::F64(0x0000_0000_0000_0000), Val::V128(V128_CORNERS[4])],
        vec![Val::I32(7), Val::F32(0x7fc0_1234), Val::F64(0x7ff0_0000_0000_0001), Val::V128(V128_CORNERS[11])],
        vec![Val::I32(65504), Val::F32(0x3f80_0000), Val::F64(0xbff0_0000_0000_0000), Val::V128(u128::MAX)], // exact page fit: 65504+16+16=65536
        vec![Val::I32(65505), Val::F32(0x3f80_0000), Val::F64(0xbff0_0000_0000_0000), Val::V128(0)], // OOB v128.store!
        vec![Val::I32(-16), Val::F32(0x3f80_0000), Val::F64(0x3ff0_0000_0000_0000), Val::V128(0)], // u32 wrap OOB!
    ];
    differential_check(&wasm, FuncId(0), &vecs, 200_000).unwrap();

    // Check Stage-1 fuzzing catches subtle -0.0 sign-bit divergence AND f32x4.min vs f32x4.pmin!
    let sign_safe = single_fn(&[WVal::F32], &[WVal::I32], &[], |s| {
        // Returns -1 if x < 0.0, 0 otherwise (-0.0 -> 0)
        s.local_get(0).f32_const(Ieee32::new(0)).f32_lt();
    });
    let sign_buggy = single_fn(&[WVal::F32], &[WVal::I32], &[], |s| {
        // Bug: checks MSB sign bit, returning 1 for -0.0!
        s.local_get(0).i32_reinterpret_f32().i32_const(31).i32_shr_u();
    });
    let neg_zero_cx = fuzz_equivalence(
        &sign_safe,
        &sign_buggy,
        FuncId(0),
        &FuzzConfig { total_vectors: 1_000, fuel_per_run: 50_000, seed: 1 },
    )
    .unwrap();
    assert!(matches!(neg_zero_cx, FuzzOutcome::Falsified(_)));

    let v_min = single_fn(&[WVal::V128, WVal::V128], &[WVal::V128], &[], |s| {
        s.local_get(0).local_get(1).f32x4_min();
    });
    let v_pmin = single_fn(&[WVal::V128, WVal::V128], &[WVal::V128], &[], |s| {
        s.local_get(0).local_get(1).f32x4_pmin();
    });
    let pmin_cx = fuzz_equivalence(
        &v_min,
        &v_pmin,
        FuncId(0),
        &FuzzConfig { total_vectors: 1_000, fuel_per_run: 50_000, seed: 2 },
    )
    .unwrap();
    assert!(matches!(pmin_cx, FuzzOutcome::Falsified(_)));
}

#[test]
fn test_fp_simd_over_10000_differential_checks_gate() {
    let mut total_checks = 0usize;

    // =========================================================================
    // 1. Scalar F32 unary ops (7 ops * 40 corners = 280 checks)
    // =========================================================================
    let f32_un_vecs: Vec<Vec<Val>> = F32_CORNERS.iter().map(|&b| vec![Val::F32(b)]).collect();
    let f32_unary_ops: &[(&str, EmitFn)] = &[
        ("f32.abs", |s| { s.local_get(0).f32_abs(); }),
        ("f32.neg", |s| { s.local_get(0).f32_neg(); }),
        ("f32.ceil", |s| { s.local_get(0).f32_ceil(); }),
        ("f32.floor", |s| { s.local_get(0).f32_floor(); }),
        ("f32.trunc", |s| { s.local_get(0).f32_trunc(); }),
        ("f32.nearest", |s| { s.local_get(0).f32_nearest(); }),
        ("f32.sqrt", |s| { s.local_get(0).f32_sqrt(); }),
    ];
    for &(name, emit) in f32_unary_ops {
        let wasm = single_fn(&[WVal::F32], &[WVal::F32], &[], emit);
        differential_check(&wasm, FuncId(0), &f32_un_vecs, 100_000)
            .unwrap_or_else(|e| panic!("scalar {name} failed: {e}"));
        total_checks += f32_un_vecs.len();
    }

    // Explicit IEEE-754 semantic corner-case assertions (payload preservation, -0.0, RNE, exact trunc traps)
    let f32_neg_wasm = single_fn(&[WVal::F32], &[WVal::F32], &[], |s| { s.local_get(0).f32_neg(); });
    assert_eq!(
        run_wasmtime_func(&f32_neg_wasm, "f", &[Val::F32(0x7fc0_1234)], 10_000).unwrap().0,
        ExecOutcome::Values(vec![Val::F32(0xffc0_1234)])
    );
    let f32_abs_wasm = single_fn(&[WVal::F32], &[WVal::F32], &[], |s| { s.local_get(0).f32_abs(); });
    assert_eq!(
        run_wasmtime_func(&f32_abs_wasm, "f", &[Val::F32(0xff80_0001)], 10_000).unwrap().0,
        ExecOutcome::Values(vec![Val::F32(0x7f80_0001)])
    );
    let f32_copysign_wasm = single_fn(&[WVal::F32, WVal::F32], &[WVal::F32], &[], |s| {
        s.local_get(0).local_get(1).f32_copysign();
    });
    assert_eq!(
        run_wasmtime_func(&f32_copysign_wasm, "f", &[Val::F32(0x7fc0_1234), Val::F32(0x8000_0000)], 10_000).unwrap().0,
        ExecOutcome::Values(vec![Val::F32(0xffc0_1234)])
    );
    let f32_nearest_wasm = single_fn(&[WVal::F32], &[WVal::F32], &[], |s| { s.local_get(0).f32_nearest(); });
    for (inp, exp) in [
        (0x3f00_0000u32, 0x0000_0000u32), // nearest(+0.5) = +0.0 (RNE)
        (0xbf00_0000, 0x8000_0000),       // nearest(-0.5) = -0.0 (RNE + sign)
        (0x3fc0_0000, 0x4000_0000),       // nearest(1.5) = 2.0 (RNE)
        (0x4020_0000, 0x4000_0000),       // nearest(2.5) = 2.0 (RNE, not 3.0!)
    ] {
        assert_eq!(
            run_wasmtime_func(&f32_nearest_wasm, "f", &[Val::F32(inp)], 10_000).unwrap().0,
            ExecOutcome::Values(vec![Val::F32(exp)])
        );
    }
    let f32_trunc_u_wasm = single_fn(&[WVal::F32], &[WVal::I32], &[], |s| { s.local_get(0).i32_trunc_f32_u(); });
    assert_eq!(
        run_wasmtime_func(&f32_trunc_u_wasm, "f", &[Val::F32(0xbf7f_ffff)], 10_000).unwrap().0, // next_up(-1.0) -> 0
        ExecOutcome::Values(vec![Val::I32(0)])
    );
    assert_eq!(
        run_wasmtime_func(&f32_trunc_u_wasm, "f", &[Val::F32(0xbf80_0000)], 10_000).unwrap().0, // -1.0 -> traps
        ExecOutcome::Trap(gnomon_kernel::TrapCode::IntOverflow)
    );
    assert_eq!(
        run_wasmtime_func(&f32_trunc_u_wasm, "f", &[Val::F32(0x7fc0_0000)], 10_000).unwrap().0, // NaN -> traps
        ExecOutcome::Trap(gnomon_kernel::TrapCode::IntOverflow)
    );
    let f64_trunc_s_wasm = single_fn(&[WVal::F64], &[WVal::I32], &[], |s| { s.local_get(0).i32_trunc_f64_s(); });
    assert_eq!(
        run_wasmtime_func(&f64_trunc_s_wasm, "f", &[Val::F64(0xc1e0_0000_001c_cccc)], 10_000).unwrap().0, // -2147483648.9 -> i32::MIN
        ExecOutcome::Values(vec![Val::I32(i32::MIN)])
    );
    assert_eq!(
        run_wasmtime_func(&f64_trunc_s_wasm, "f", &[Val::F64(0xc1e0_0000_0020_0000)], 10_000).unwrap().0, // -2147483649.0 -> traps
        ExecOutcome::Trap(gnomon_kernel::TrapCode::IntOverflow)
    );
    let f32x4_pmin_wasm = single_fn(&[WVal::V128, WVal::V128], &[WVal::V128], &[], |s| {
        s.local_get(0).local_get(1).f32x4_pmin();
    });
    let pmin_a = pack_u32x4(0x7fc0_1234, 0x8000_0000, 0x0000_0000, 0x3f80_0000);
    let pmin_b = pack_u32x4(0x3f80_0000, 0x0000_0000, 0x8000_0000, 0x7fc0_5678);
    assert_eq!(
        run_wasmtime_func(&f32x4_pmin_wasm, "f", &[Val::V128(pmin_a), Val::V128(pmin_b)], 10_000).unwrap().0,
        ExecOutcome::Values(vec![Val::V128(pmin_a)])
    );

    // =========================================================================
    // 2. Scalar F64 unary ops (7 ops * 37 corners = 259 checks)
    // =========================================================================
    let f64_un_vecs: Vec<Vec<Val>> = F64_CORNERS.iter().map(|&b| vec![Val::F64(b)]).collect();
    let f64_unary_ops: &[(&str, EmitFn)] = &[
        ("f64.abs", |s| { s.local_get(0).f64_abs(); }),
        ("f64.neg", |s| { s.local_get(0).f64_neg(); }),
        ("f64.ceil", |s| { s.local_get(0).f64_ceil(); }),
        ("f64.floor", |s| { s.local_get(0).f64_floor(); }),
        ("f64.trunc", |s| { s.local_get(0).f64_trunc(); }),
        ("f64.nearest", |s| { s.local_get(0).f64_nearest(); }),
        ("f64.sqrt", |s| { s.local_get(0).f64_sqrt(); }),
    ];
    for &(name, emit) in f64_unary_ops {
        let wasm = single_fn(&[WVal::F64], &[WVal::F64], &[], emit);
        differential_check(&wasm, FuncId(0), &f64_un_vecs, 100_000)
            .unwrap_or_else(|e| panic!("scalar {name} failed: {e}"));
        total_checks += f64_un_vecs.len();
    }

    // =========================================================================
    // 3. Scalar F32 binary & cmp ops (13 ops * 16x16 = 3,328 checks!)
    // =========================================================================
    let f32_grid_elems: &[u32] = &[
        0x0000_0000, 0x8000_0000, 0x0000_0001, 0x8000_0001,
        0x0080_0000, 0x3f00_0000, 0xbf00_0000, 0x3f80_0000,
        0xbf80_0000, 0x4020_0000, 0x7f7f_ffff, 0xff7f_ffff,
        0x7f80_0000, 0xff80_0000, 0x7fc0_1234, 0x7f80_0001,
    ];
    let mut f32_pairs = Vec::with_capacity(f32_grid_elems.len() * f32_grid_elems.len());
    for &a in f32_grid_elems {
        for &b in f32_grid_elems {
            f32_pairs.push(vec![Val::F32(a), Val::F32(b)]);
        }
    }
    let f32_bin_ops: &[(&str, WVal, EmitFn)] = &[
        ("f32.add", WVal::F32, |s| { s.local_get(0).local_get(1).f32_add(); }),
        ("f32.sub", WVal::F32, |s| { s.local_get(0).local_get(1).f32_sub(); }),
        ("f32.mul", WVal::F32, |s| { s.local_get(0).local_get(1).f32_mul(); }),
        ("f32.div", WVal::F32, |s| { s.local_get(0).local_get(1).f32_div(); }),
        ("f32.min", WVal::F32, |s| { s.local_get(0).local_get(1).f32_min(); }),
        ("f32.max", WVal::F32, |s| { s.local_get(0).local_get(1).f32_max(); }),
        ("f32.copysign", WVal::F32, |s| { s.local_get(0).local_get(1).f32_copysign(); }),
        ("f32.eq", WVal::I32, |s| { s.local_get(0).local_get(1).f32_eq(); }),
        ("f32.ne", WVal::I32, |s| { s.local_get(0).local_get(1).f32_ne(); }),
        ("f32.lt", WVal::I32, |s| { s.local_get(0).local_get(1).f32_lt(); }),
        ("f32.gt", WVal::I32, |s| { s.local_get(0).local_get(1).f32_gt(); }),
        ("f32.le", WVal::I32, |s| { s.local_get(0).local_get(1).f32_le(); }),
        ("f32.ge", WVal::I32, |s| { s.local_get(0).local_get(1).f32_ge(); }),
    ];
    for &(name, res_ty, emit) in f32_bin_ops {
        let wasm = single_fn(&[WVal::F32, WVal::F32], &[res_ty], &[], emit);
        differential_check(&wasm, FuncId(0), &f32_pairs, 100_000)
            .unwrap_or_else(|e| panic!("scalar {name} failed: {e}"));
        total_checks += f32_pairs.len();
    }

    // =========================================================================
    // 4. Scalar F64 binary & cmp ops (13 ops * 14x14 = 2,548 checks!)
    // =========================================================================
    let f64_grid_elems: &[u64] = &[
        0x0000_0000_0000_0000, 0x8000_0000_0000_0000,
        0x0000_0000_0000_0001, 0x8000_0000_0000_0001,
        0x3fe0_0000_0000_0000, 0xbfe0_0000_0000_0000,
        0x3ff0_0000_0000_0000, 0xbff0_0000_0000_0000,
        0x7fef_ffff_ffff_ffff, 0xffef_ffff_ffff_ffff,
        0x7ff0_0000_0000_0000, 0xfff0_0000_0000_0000,
        0x7ff8_0000_0000_0001, 0x7ff0_0000_0000_0001,
    ];
    let mut f64_pairs = Vec::with_capacity(f64_grid_elems.len() * f64_grid_elems.len());
    for &a in f64_grid_elems {
        for &b in f64_grid_elems {
            f64_pairs.push(vec![Val::F64(a), Val::F64(b)]);
        }
    }
    let f64_bin_ops: &[(&str, WVal, EmitFn)] = &[
        ("f64.add", WVal::F64, |s| { s.local_get(0).local_get(1).f64_add(); }),
        ("f64.sub", WVal::F64, |s| { s.local_get(0).local_get(1).f64_sub(); }),
        ("f64.mul", WVal::F64, |s| { s.local_get(0).local_get(1).f64_mul(); }),
        ("f64.div", WVal::F64, |s| { s.local_get(0).local_get(1).f64_div(); }),
        ("f64.min", WVal::F64, |s| { s.local_get(0).local_get(1).f64_min(); }),
        ("f64.max", WVal::F64, |s| { s.local_get(0).local_get(1).f64_max(); }),
        ("f64.copysign", WVal::F64, |s| { s.local_get(0).local_get(1).f64_copysign(); }),
        ("f64.eq", WVal::I32, |s| { s.local_get(0).local_get(1).f64_eq(); }),
        ("f64.ne", WVal::I32, |s| { s.local_get(0).local_get(1).f64_ne(); }),
        ("f64.lt", WVal::I32, |s| { s.local_get(0).local_get(1).f64_lt(); }),
        ("f64.gt", WVal::I32, |s| { s.local_get(0).local_get(1).f64_gt(); }),
        ("f64.le", WVal::I32, |s| { s.local_get(0).local_get(1).f64_le(); }),
        ("f64.ge", WVal::I32, |s| { s.local_get(0).local_get(1).f64_ge(); }),
    ];
    for &(name, res_ty, emit) in f64_bin_ops {
        let wasm = single_fn(&[WVal::F64, WVal::F64], &[res_ty], &[], emit);
        differential_check(&wasm, FuncId(0), &f64_pairs, 100_000)
            .unwrap_or_else(|e| panic!("scalar {name} failed: {e}"));
        total_checks += f64_pairs.len();
    }

    // =========================================================================
    // 5. All 30 Conversion / Trunc / TruncSat / Demote / Promote / Reinterpret ops (~980 checks)
    // =========================================================================
    let f32_convs: &[(&str, WVal, EmitFn)] = &[
        ("i32.trunc_f32_s", WVal::I32, |s| { s.local_get(0).i32_trunc_f32_s(); }),
        ("i32.trunc_f32_u", WVal::I32, |s| { s.local_get(0).i32_trunc_f32_u(); }),
        ("i64.trunc_f32_s", WVal::I64, |s| { s.local_get(0).i64_trunc_f32_s(); }),
        ("i64.trunc_f32_u", WVal::I64, |s| { s.local_get(0).i64_trunc_f32_u(); }),
        ("i32.trunc_sat_f32_s", WVal::I32, |s| { s.local_get(0).i32_trunc_sat_f32_s(); }),
        ("i32.trunc_sat_f32_u", WVal::I32, |s| { s.local_get(0).i32_trunc_sat_f32_u(); }),
        ("i64.trunc_sat_f32_s", WVal::I64, |s| { s.local_get(0).i64_trunc_sat_f32_s(); }),
        ("i64.trunc_sat_f32_u", WVal::I64, |s| { s.local_get(0).i64_trunc_sat_f32_u(); }),
        ("f64.promote_f32", WVal::F64, |s| { s.local_get(0).f64_promote_f32(); }),
        ("i32.reinterpret_f32", WVal::I32, |s| { s.local_get(0).i32_reinterpret_f32(); }),
    ];
    for &(name, res_ty, emit) in f32_convs {
        let wasm = single_fn(&[WVal::F32], &[res_ty], &[], emit);
        differential_check(&wasm, FuncId(0), &f32_un_vecs, 100_000)
            .unwrap_or_else(|e| panic!("conv {name} failed: {e}"));
        total_checks += f32_un_vecs.len();
    }

    let f64_convs: &[(&str, WVal, EmitFn)] = &[
        ("i32.trunc_f64_s", WVal::I32, |s| { s.local_get(0).i32_trunc_f64_s(); }),
        ("i32.trunc_f64_u", WVal::I32, |s| { s.local_get(0).i32_trunc_f64_u(); }),
        ("i64.trunc_f64_s", WVal::I64, |s| { s.local_get(0).i64_trunc_f64_s(); }),
        ("i64.trunc_f64_u", WVal::I64, |s| { s.local_get(0).i64_trunc_f64_u(); }),
        ("i32.trunc_sat_f64_s", WVal::I32, |s| { s.local_get(0).i32_trunc_sat_f64_s(); }),
        ("i32.trunc_sat_f64_u", WVal::I32, |s| { s.local_get(0).i32_trunc_sat_f64_u(); }),
        ("i64.trunc_sat_f64_s", WVal::I64, |s| { s.local_get(0).i64_trunc_sat_f64_s(); }),
        ("i64.trunc_sat_f64_u", WVal::I64, |s| { s.local_get(0).i64_trunc_sat_f64_u(); }),
        ("f32.demote_f64", WVal::F32, |s| { s.local_get(0).f32_demote_f64(); }),
        ("i64.reinterpret_f64", WVal::I64, |s| { s.local_get(0).i64_reinterpret_f64(); }),
    ];
    for &(name, res_ty, emit) in f64_convs {
        let wasm = single_fn(&[WVal::F64], &[res_ty], &[], emit);
        differential_check(&wasm, FuncId(0), &f64_un_vecs, 100_000)
            .unwrap_or_else(|e| panic!("conv {name} failed: {e}"));
        total_checks += f64_un_vecs.len();
    }

    let i32_edge_vecs: Vec<Vec<Val>> = [
        0, 1, -1, 2, -2, 127, -128, 0x00ff_ffff, 0x0100_0001, 0x7fff_ffff, i32::MIN,
        i32::MIN + 1, 0x7fc0_1234, 0x7f80_0001, 0x8000_0000u32 as i32,
    ]
    .into_iter()
    .map(|x| vec![Val::I32(x)])
    .collect();
    let i32_convs: &[(&str, WVal, EmitFn)] = &[
        ("f32.convert_i32_s", WVal::F32, |s| { s.local_get(0).f32_convert_i32_s(); }),
        ("f32.convert_i32_u", WVal::F32, |s| { s.local_get(0).f32_convert_i32_u(); }),
        ("f64.convert_i32_s", WVal::F64, |s| { s.local_get(0).f64_convert_i32_s(); }),
        ("f64.convert_i32_u", WVal::F64, |s| { s.local_get(0).f64_convert_i32_u(); }),
        ("f32.reinterpret_i32", WVal::F32, |s| { s.local_get(0).f32_reinterpret_i32(); }),
    ];
    for &(name, res_ty, emit) in i32_convs {
        let wasm = single_fn(&[WVal::I32], &[res_ty], &[], emit);
        differential_check(&wasm, FuncId(0), &i32_edge_vecs, 100_000)
            .unwrap_or_else(|e| panic!("conv {name} failed: {e}"));
        total_checks += i32_edge_vecs.len();
    }

    let i64_edge_vecs: Vec<Vec<Val>> = [
        0, 1, -1, 2, -2, (1i64 << 53) - 1, 1i64 << 53, (1i64 << 53) + 1,
        i64::MAX, i64::MAX - 1, i64::MIN, i64::MIN + 1, 0x7ff8_0000_0000_0001,
        0x7ff0_0000_0000_0001, 0x8000_0000_0000_0000u64 as i64,
    ]
    .into_iter()
    .map(|x| vec![Val::I64(x)])
    .collect();
    let i64_convs: &[(&str, WVal, EmitFn)] = &[
        ("f32.convert_i64_s", WVal::F32, |s| { s.local_get(0).f32_convert_i64_s(); }),
        ("f32.convert_i64_u", WVal::F32, |s| { s.local_get(0).f32_convert_i64_u(); }),
        ("f64.convert_i64_s", WVal::F64, |s| { s.local_get(0).f64_convert_i64_s(); }),
        ("f64.convert_i64_u", WVal::F64, |s| { s.local_get(0).f64_convert_i64_u(); }),
        ("f64.reinterpret_i64", WVal::F64, |s| { s.local_get(0).f64_reinterpret_i64(); }),
    ];
    for &(name, res_ty, emit) in i64_convs {
        let wasm = single_fn(&[WVal::I64], &[res_ty], &[], emit);
        differential_check(&wasm, FuncId(0), &i64_edge_vecs, 100_000)
            .unwrap_or_else(|e| panic!("conv {name} failed: {e}"));
        total_checks += i64_edge_vecs.len();
    }

    // =========================================================================
    // 6. All 40 v128 UnOps (unary / splat / bitmask / all_true / abs / neg / FP / convert / extend)
    // =========================================================================
    let v128_un_vecs: Vec<Vec<Val>> = V128_CORNERS.iter().map(|&b| vec![Val::V128(b)]).collect();
    let v128_unary_ops: &[(&str, WVal, EmitFn)] = &[
        ("v128.not", WVal::V128, |s| { s.local_get(0).v128_not(); }),
        ("v128.any_true", WVal::I32, |s| { s.local_get(0).v128_any_true(); }),
        ("i8x16.bitmask", WVal::I32, |s| { s.local_get(0).i8x16_bitmask(); }),
        ("i16x8.bitmask", WVal::I32, |s| { s.local_get(0).i16x8_bitmask(); }),
        ("i32x4.bitmask", WVal::I32, |s| { s.local_get(0).i32x4_bitmask(); }),
        ("i64x2.bitmask", WVal::I32, |s| { s.local_get(0).i64x2_bitmask(); }),
        ("i32x4.all_true", WVal::I32, |s| { s.local_get(0).i32x4_all_true(); }),
        ("i64x2.all_true", WVal::I32, |s| { s.local_get(0).i64x2_all_true(); }),
        ("i32x4.abs", WVal::V128, |s| { s.local_get(0).i32x4_abs(); }),
        ("i32x4.neg", WVal::V128, |s| { s.local_get(0).i32x4_neg(); }),
        ("i64x2.abs", WVal::V128, |s| { s.local_get(0).i64x2_abs(); }),
        ("i64x2.neg", WVal::V128, |s| { s.local_get(0).i64x2_neg(); }),
        ("f32x4.abs", WVal::V128, |s| { s.local_get(0).f32x4_abs(); }),
        ("f32x4.neg", WVal::V128, |s| { s.local_get(0).f32x4_neg(); }),
        ("f32x4.sqrt", WVal::V128, |s| { s.local_get(0).f32x4_sqrt(); }),
        ("f32x4.ceil", WVal::V128, |s| { s.local_get(0).f32x4_ceil(); }),
        ("f32x4.floor", WVal::V128, |s| { s.local_get(0).f32x4_floor(); }),
        ("f32x4.trunc", WVal::V128, |s| { s.local_get(0).f32x4_trunc(); }),
        ("f32x4.nearest", WVal::V128, |s| { s.local_get(0).f32x4_nearest(); }),
        ("f64x2.abs", WVal::V128, |s| { s.local_get(0).f64x2_abs(); }),
        ("f64x2.neg", WVal::V128, |s| { s.local_get(0).f64x2_neg(); }),
        ("f64x2.sqrt", WVal::V128, |s| { s.local_get(0).f64x2_sqrt(); }),
        ("f64x2.ceil", WVal::V128, |s| { s.local_get(0).f64x2_ceil(); }),
        ("f64x2.floor", WVal::V128, |s| { s.local_get(0).f64x2_floor(); }),
        ("f64x2.trunc", WVal::V128, |s| { s.local_get(0).f64x2_trunc(); }),
        ("f64x2.nearest", WVal::V128, |s| { s.local_get(0).f64x2_nearest(); }),
        ("i32x4.trunc_sat_f32x4_s", WVal::V128, |s| { s.local_get(0).i32x4_trunc_sat_f32x4_s(); }),
        ("i32x4.trunc_sat_f32x4_u", WVal::V128, |s| { s.local_get(0).i32x4_trunc_sat_f32x4_u(); }),
        ("f32x4.convert_i32x4_s", WVal::V128, |s| { s.local_get(0).f32x4_convert_i32x4_s(); }),
        ("f32x4.convert_i32x4_u", WVal::V128, |s| { s.local_get(0).f32x4_convert_i32x4_u(); }),
        ("i64x2.extend_low_i32x4_s", WVal::V128, |s| { s.local_get(0).i64x2_extend_low_i32x4_s(); }),
        ("i64x2.extend_low_i32x4_u", WVal::V128, |s| { s.local_get(0).i64x2_extend_low_i32x4_u(); }),
        ("i64x2.extend_high_i32x4_s", WVal::V128, |s| { s.local_get(0).i64x2_extend_high_i32x4_s(); }),
        ("i64x2.extend_high_i32x4_u", WVal::V128, |s| { s.local_get(0).i64x2_extend_high_i32x4_u(); }),
    ];
    for &(name, res_ty, emit) in v128_unary_ops {
        let wasm = single_fn(&[WVal::V128], &[res_ty], &[], emit);
        differential_check(&wasm, FuncId(0), &v128_un_vecs, 100_000)
            .unwrap_or_else(|e| panic!("v128 unary {name} failed: {e}"));
        total_checks += v128_un_vecs.len();
    }

    // All 6 splats
    let splat_ops: &[(&str, WVal, &[Vec<Val>], EmitFn)] = &[
        ("i8x16.splat", WVal::I32, &i32_edge_vecs, |s| { s.local_get(0).i8x16_splat(); }),
        ("i16x8.splat", WVal::I32, &i32_edge_vecs, |s| { s.local_get(0).i16x8_splat(); }),
        ("i32x4.splat", WVal::I32, &i32_edge_vecs, |s| { s.local_get(0).i32x4_splat(); }),
        ("i64x2.splat", WVal::I64, &i64_edge_vecs, |s| { s.local_get(0).i64x2_splat(); }),
        ("f32x4.splat", WVal::F32, &f32_un_vecs, |s| { s.local_get(0).f32x4_splat(); }),
        ("f64x2.splat", WVal::F64, &f64_un_vecs, |s| { s.local_get(0).f64x2_splat(); }),
    ];
    for &(name, in_ty, vecs, emit) in splat_ops {
        let wasm = single_fn(&[in_ty], &[WVal::V128], &[], emit);
        differential_check(&wasm, FuncId(0), vecs, 100_000)
            .unwrap_or_else(|e| panic!("splat {name} failed: {e}"));
        total_checks += vecs.len();
    }

    // =========================================================================
    // 7. All 65 v128 BinOps (59 (v128, v128) + 6 (v128, i32) shifts)
    // =========================================================================
    let v128_grid = &V128_CORNERS[..8];
    let mut v128_pairs = Vec::with_capacity(v128_grid.len() * v128_grid.len() + 36);
    for &a in v128_grid {
        for &b in v128_grid {
            v128_pairs.push(vec![Val::V128(a), Val::V128(b)]);
        }
    }
    // Also add all pairwise combinations of FP v128 corners (indices 9..20)
    for &a in &V128_CORNERS[9..15] {
        for &b in &V128_CORNERS[9..15] {
            v128_pairs.push(vec![Val::V128(a), Val::V128(b)]);
        }
    }
    let v128_f64_pairs: Vec<Vec<Val>> = V128_CORNERS[15..]
        .iter()
        .flat_map(|&a| V128_CORNERS[15..].iter().map(move |&b| vec![Val::V128(a), Val::V128(b)]))
        .collect();

    let v128_bin_ops: &[(&str, bool, EmitFn)] = &[
        ("v128.and", false, |s| { s.local_get(0).local_get(1).v128_and(); }),
        ("v128.andnot", false, |s| { s.local_get(0).local_get(1).v128_andnot(); }),
        ("v128.or", false, |s| { s.local_get(0).local_get(1).v128_or(); }),
        ("v128.xor", false, |s| { s.local_get(0).local_get(1).v128_xor(); }),
        ("i8x16.swizzle", false, |s| { s.local_get(0).local_get(1).i8x16_swizzle(); }),
        ("i32x4.add", false, |s| { s.local_get(0).local_get(1).i32x4_add(); }),
        ("i32x4.sub", false, |s| { s.local_get(0).local_get(1).i32x4_sub(); }),
        ("i32x4.mul", false, |s| { s.local_get(0).local_get(1).i32x4_mul(); }),
        ("i32x4.min_s", false, |s| { s.local_get(0).local_get(1).i32x4_min_s(); }),
        ("i32x4.min_u", false, |s| { s.local_get(0).local_get(1).i32x4_min_u(); }),
        ("i32x4.max_s", false, |s| { s.local_get(0).local_get(1).i32x4_max_s(); }),
        ("i32x4.max_u", false, |s| { s.local_get(0).local_get(1).i32x4_max_u(); }),
        ("i32x4.eq", false, |s| { s.local_get(0).local_get(1).i32x4_eq(); }),
        ("i32x4.ne", false, |s| { s.local_get(0).local_get(1).i32x4_ne(); }),
        ("i32x4.lt_s", false, |s| { s.local_get(0).local_get(1).i32x4_lt_s(); }),
        ("i32x4.lt_u", false, |s| { s.local_get(0).local_get(1).i32x4_lt_u(); }),
        ("i32x4.gt_s", false, |s| { s.local_get(0).local_get(1).i32x4_gt_s(); }),
        ("i32x4.gt_u", false, |s| { s.local_get(0).local_get(1).i32x4_gt_u(); }),
        ("i32x4.le_s", false, |s| { s.local_get(0).local_get(1).i32x4_le_s(); }),
        ("i32x4.le_u", false, |s| { s.local_get(0).local_get(1).i32x4_le_u(); }),
        ("i32x4.ge_s", false, |s| { s.local_get(0).local_get(1).i32x4_ge_s(); }),
        ("i32x4.ge_u", false, |s| { s.local_get(0).local_get(1).i32x4_ge_u(); }),
        ("i64x2.add", false, |s| { s.local_get(0).local_get(1).i64x2_add(); }),
        ("i64x2.sub", false, |s| { s.local_get(0).local_get(1).i64x2_sub(); }),
        ("i64x2.mul", false, |s| { s.local_get(0).local_get(1).i64x2_mul(); }),
        ("i64x2.eq", false, |s| { s.local_get(0).local_get(1).i64x2_eq(); }),
        ("i64x2.ne", false, |s| { s.local_get(0).local_get(1).i64x2_ne(); }),
        ("i64x2.lt_s", false, |s| { s.local_get(0).local_get(1).i64x2_lt_s(); }),
        ("i64x2.gt_s", false, |s| { s.local_get(0).local_get(1).i64x2_gt_s(); }),
        ("i64x2.le_s", false, |s| { s.local_get(0).local_get(1).i64x2_le_s(); }),
        ("i64x2.ge_s", false, |s| { s.local_get(0).local_get(1).i64x2_ge_s(); }),
        ("f32x4.add", false, |s| { s.local_get(0).local_get(1).f32x4_add(); }),
        ("f32x4.sub", false, |s| { s.local_get(0).local_get(1).f32x4_sub(); }),
        ("f32x4.mul", false, |s| { s.local_get(0).local_get(1).f32x4_mul(); }),
        ("f32x4.div", false, |s| { s.local_get(0).local_get(1).f32x4_div(); }),
        ("f32x4.min", false, |s| { s.local_get(0).local_get(1).f32x4_min(); }),
        ("f32x4.max", false, |s| { s.local_get(0).local_get(1).f32x4_max(); }),
        ("f32x4.pmin", false, |s| { s.local_get(0).local_get(1).f32x4_pmin(); }),
        ("f32x4.pmax", false, |s| { s.local_get(0).local_get(1).f32x4_pmax(); }),
        ("f32x4.eq", false, |s| { s.local_get(0).local_get(1).f32x4_eq(); }),
        ("f32x4.ne", false, |s| { s.local_get(0).local_get(1).f32x4_ne(); }),
        ("f32x4.lt", false, |s| { s.local_get(0).local_get(1).f32x4_lt(); }),
        ("f32x4.gt", false, |s| { s.local_get(0).local_get(1).f32x4_gt(); }),
        ("f32x4.le", false, |s| { s.local_get(0).local_get(1).f32x4_le(); }),
        ("f32x4.ge", false, |s| { s.local_get(0).local_get(1).f32x4_ge(); }),
        ("f64x2.add", true, |s| { s.local_get(0).local_get(1).f64x2_add(); }),
        ("f64x2.sub", true, |s| { s.local_get(0).local_get(1).f64x2_sub(); }),
        ("f64x2.mul", true, |s| { s.local_get(0).local_get(1).f64x2_mul(); }),
        ("f64x2.div", true, |s| { s.local_get(0).local_get(1).f64x2_div(); }),
        ("f64x2.min", true, |s| { s.local_get(0).local_get(1).f64x2_min(); }),
        ("f64x2.max", true, |s| { s.local_get(0).local_get(1).f64x2_max(); }),
        ("f64x2.pmin", true, |s| { s.local_get(0).local_get(1).f64x2_pmin(); }),
        ("f64x2.pmax", true, |s| { s.local_get(0).local_get(1).f64x2_pmax(); }),
        ("f64x2.eq", true, |s| { s.local_get(0).local_get(1).f64x2_eq(); }),
        ("f64x2.ne", true, |s| { s.local_get(0).local_get(1).f64x2_ne(); }),
        ("f64x2.lt", true, |s| { s.local_get(0).local_get(1).f64x2_lt(); }),
        ("f64x2.gt", true, |s| { s.local_get(0).local_get(1).f64x2_gt(); }),
        ("f64x2.le", true, |s| { s.local_get(0).local_get(1).f64x2_le(); }),
        ("f64x2.ge", true, |s| { s.local_get(0).local_get(1).f64x2_ge(); }),
    ];
    for &(name, is_f64, emit) in v128_bin_ops {
        let wasm = single_fn(&[WVal::V128, WVal::V128], &[WVal::V128], &[], emit);
        let vecs = if is_f64 { &v128_f64_pairs } else { &v128_pairs };
        differential_check(&wasm, FuncId(0), vecs, 100_000)
            .unwrap_or_else(|e| panic!("v128 bin {name} failed: {e}"));
        total_checks += vecs.len();
    }

    // All 6 asymmetric shifts: (v128, i32) -> v128
    let shift_counts = [0, 1, 7, 31, 32, 33, 63, 64, 65, -1, i32::MIN];
    let mut shift_vecs = Vec::new();
    for &v in &V128_CORNERS[..9] {
        for &sh in &shift_counts {
            shift_vecs.push(vec![Val::V128(v), Val::I32(sh)]);
        }
    }
    let shift_ops: &[(&str, EmitFn)] = &[
        ("i32x4.shl", |s| { s.local_get(0).local_get(1).i32x4_shl(); }),
        ("i32x4.shr_s", |s| { s.local_get(0).local_get(1).i32x4_shr_s(); }),
        ("i32x4.shr_u", |s| { s.local_get(0).local_get(1).i32x4_shr_u(); }),
        ("i64x2.shl", |s| { s.local_get(0).local_get(1).i64x2_shl(); }),
        ("i64x2.shr_s", |s| { s.local_get(0).local_get(1).i64x2_shr_s(); }),
        ("i64x2.shr_u", |s| { s.local_get(0).local_get(1).i64x2_shr_u(); }),
    ];
    for &(name, emit) in shift_ops {
        let wasm = single_fn(&[WVal::V128, WVal::I32], &[WVal::V128], &[], emit);
        differential_check(&wasm, FuncId(0), &shift_vecs, 100_000)
            .unwrap_or_else(|e| panic!("v128 shift {name} failed: {e}"));
        total_checks += shift_vecs.len();
    }

    // =========================================================================
    // 8. SIMD ExtractLane (8 kinds), ReplaceLane (6 kinds), Bitselect, Shuffle, v128.load/store
    // =========================================================================
    let lane_extract_replace = single_fn(
        &[WVal::V128, WVal::I32, WVal::I64, WVal::F32, WVal::F64],
        &[WVal::V128, WVal::I32, WVal::I64, WVal::F32, WVal::F64],
        &[],
        |s| {
            // Chain all 6 replace_lane ops on local 0
            s.local_get(0)
                .local_get(1).i8x16_replace_lane(0)
                .local_get(1).i8x16_replace_lane(15)
                .local_get(1).i16x8_replace_lane(3)
                .local_get(1).i32x4_replace_lane(2)
                .local_get(2).i64x2_replace_lane(1)
                .local_get(3).f32x4_replace_lane(1)
                .local_get(4).f64x2_replace_lane(0);
            // Extract all 8 lane kinds from local 0
            s.local_get(0).i8x16_extract_lane_s(15)
                .local_get(0).i8x16_extract_lane_u(15).i32_xor()
                .local_get(0).i16x8_extract_lane_s(7).i32_add()
                .local_get(0).i16x8_extract_lane_u(7).i32_xor()
                .local_get(0).i32x4_extract_lane(3).i32_add();
            s.local_get(0).i64x2_extract_lane(1);
            s.local_get(0).f32x4_extract_lane(2);
            s.local_get(0).f64x2_extract_lane(1);
        },
    );
    let mut seed = 0xBEEF_F320_F640_1280u64;
    let lane_vecs = gen_args_for_params(
        &[ValType::V128, ValType::I32, ValType::I64, ValType::F32, ValType::F64],
        100,
        &mut seed,
    );
    differential_check(&lane_extract_replace, FuncId(0), &lane_vecs, 100_000).unwrap();
    total_checks += lane_vecs.len();

    // v128.bitselect + multiple i8x16.shuffle masks + v128.load/store
    let bitselect_shuffle_mem = mem_fn(
        &[WVal::V128, WVal::V128, WVal::V128, WVal::I32],
        &[WVal::V128],
        &[],
        |s| {
            // addr = local_get(3) & 1023
            s.local_get(3).i32_const(1023).i32_and();
            // v128.bitselect(a, b, mask)
            s.local_get(0).local_get(1).local_get(2).v128_bitselect();
            // Shuffle 1: interleave bytes from bitselect result and b
            s.local_get(1)
                .i8x16_shuffle([0, 16, 1, 17, 2, 18, 3, 19, 12, 28, 13, 29, 14, 30, 15, 31]);
            // Store to memory at addr + 16
            s.v128_store(ma(0, 16, 4));
            // Load back and shuffle 2: reverse 32-bit lanes with a
            s.local_get(3).i32_const(1023).i32_and().v128_load(ma(0, 16, 4));
            s.local_get(0)
                .i8x16_shuffle([12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19]);
        },
    );
    let bsm_vecs = gen_args_for_params(
        &[ValType::V128, ValType::V128, ValType::V128, ValType::I32],
        200,
        &mut seed,
    );
    differential_check(&bitselect_shuffle_mem, FuncId(0), &bsm_vecs, 100_000).unwrap();
    total_checks += bsm_vecs.len();

    println!("Total FP & v128 SIMD differential checks passed (0 mismatches): {total_checks}");
    assert!(
        total_checks >= 10_000,
        "expected >= 10,000 FP/SIMD differential checks, got {total_checks}"
    );
}
