use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

use gnomon_kernel::{
    BinOp, EffectOp, FuncDef, FuncId, GlobalDef, GlobalId, HeapState, MemId, MemoryDef, Module,
    Op, Region, StratumRegistry, TrapCode, UnOp, Val, ValId, ValType, eval_func,
};
use gnomon_wasm::{
    ExecOutcome, FuzzConfig, FuzzOutcome, WasmError, differential_check, emit_wasm,
    fuzz_equivalence, fuzz_equivalence_by_name, lift_wasm, run_wasmtime_func, verify_round_trip,
};
use proptest::prelude::*;
use wasm_encoder::{
    BlockType, CodeSection, ConstExpr, DataSection, EntityType, ExportKind, ExportSection,
    Function, FunctionSection, GlobalSection, GlobalType, ImportSection, InstructionSink, MemArg,
    MemArgTarget, MemorySection, MemoryType, Module as WasmModule, TypeSection, ValType as WVal,
};

fn ma(mem: u32, offset: u64, align: u32) -> MemArg {
    MemArg {
        offset,
        align,
        target: MemArgTarget::Memory(mem),
        ordering: None,
    }
}

fn single_fn_wasm(
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

fn mem_fn_wasm(
    mem_pages: u32,
    max_pages: Option<u32>,
    init_data: &[(u32, &[u8])],
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
        minimum: u64::from(mem_pages),
        maximum: max_pages.map(u64::from),
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

    if !init_data.is_empty() {
        let mut ds = DataSection::new();
        for &(off, data) in init_data {
            ds.active(0, &ConstExpr::i32_const(off as i32), data.iter().copied());
        }
        m.section(&ds);
    }
    m.finish()
}

#[test]
fn test_all_i32_i64_ops_and_exact_traps() {
    // 1. i32.div_s / rem_s / div_u / rem_u boundary traps & MIN % -1 == 0
    let div_i32 = single_fn_wasm(&[WVal::I32, WVal::I32], &[WVal::I32], &[], |s| {
        s.local_get(0).local_get(1).i32_div_s();
    });
    let rem_i32 = single_fn_wasm(&[WVal::I32, WVal::I32], &[WVal::I32], &[], |s| {
        s.local_get(0).local_get(1).i32_rem_s();
    });
    let div_i64 = single_fn_wasm(&[WVal::I64, WVal::I64], &[WVal::I64], &[], |s| {
        s.local_get(0).local_get(1).i64_div_s();
    });
    let rem_i64 = single_fn_wasm(&[WVal::I64, WVal::I64], &[WVal::I64], &[], |s| {
        s.local_get(0).local_get(1).i64_rem_s();
    });

    let i32_vecs = vec![
        vec![Val::I32(i32::MIN), Val::I32(-1)],
        vec![Val::I32(10), Val::I32(0)],
        vec![Val::I32(i32::MIN), Val::I32(0)],
        vec![Val::I32(i32::MAX), Val::I32(-3)],
        vec![Val::I32(-100), Val::I32(7)],
    ];
    differential_check(&div_i32, FuncId(0), &i32_vecs, 100_000).unwrap();
    differential_check(&rem_i32, FuncId(0), &i32_vecs, 100_000).unwrap();

    // Verify exact TrapCodes via run_wasmtime_func
    assert_eq!(
        run_wasmtime_func(&div_i32, "f", &[Val::I32(i32::MIN), Val::I32(-1)], 10_000).unwrap().0,
        ExecOutcome::Trap(TrapCode::IntOverflow)
    );
    assert_eq!(
        run_wasmtime_func(&div_i32, "f", &[Val::I32(7), Val::I32(0)], 10_000).unwrap().0,
        ExecOutcome::Trap(TrapCode::DivByZero)
    );
    assert_eq!(
        run_wasmtime_func(&rem_i32, "f", &[Val::I32(i32::MIN), Val::I32(-1)], 10_000).unwrap().0,
        ExecOutcome::Values(vec![Val::I32(0)])
    );

    let i64_vecs = vec![
        vec![Val::I64(i64::MIN), Val::I64(-1)],
        vec![Val::I64(42), Val::I64(0)],
        vec![Val::I64(i64::MAX), Val::I64(-5)],
    ];
    differential_check(&div_i64, FuncId(0), &i64_vecs, 100_000).unwrap();
    differential_check(&rem_i64, FuncId(0), &i64_vecs, 100_000).unwrap();

    // 2. All unary & shift/rotate/comparison/extension ops in one multi-branch expression
    let unary_and_bits = single_fn_wasm(&[WVal::I32, WVal::I64], &[WVal::I64], &[], |s| {
        // Compute a checksum exercising clz, ctz, popcnt, extend8_s, extend16_s, extend32_s,
        // wrap_i64, extend_i32_s/u, eqz, rotl, rotr, shl, shr_s, shr_u
        s.local_get(0).i32_clz();
        s.local_get(0).i32_ctz().i32_add();
        s.local_get(0).i32_popcnt().i32_xor();
        s.local_get(0).i32_extend8_s().i32_add();
        s.local_get(0).i32_extend16_s().i32_sub();
        s.local_get(0).i32_eqz().i32_add();
        s.local_get(0).i32_const(13).i32_rotl().i32_xor();
        s.local_get(0).i32_const(7).i32_rotr().i32_add();
        s.local_get(1).i32_wrap_i64().i32_add();
        s.i64_extend_i32_s();
        s.local_get(0).i64_extend_i32_u().i64_xor();
        s.local_get(1).i64_clz().i64_add();
        s.local_get(1).i64_ctz().i64_add();
        s.local_get(1).i64_popcnt().i64_xor();
        s.local_get(1).i64_extend8_s().i64_add();
        s.local_get(1).i64_extend16_s().i64_sub();
        s.local_get(1).i64_extend32_s().i64_add();
        s.local_get(1).i64_eqz().i64_extend_i32_u().i64_add();
        s.local_get(1).i64_const(19).i64_rotl().i64_xor();
        s.local_get(1).i64_const(37).i64_rotr().i64_add();
    });

    let mixed_vecs = vec![
        vec![Val::I32(0), Val::I64(0)],
        vec![Val::I32(-1), Val::I64(-1)],
        vec![Val::I32(i32::MIN), Val::I64(i64::MIN)],
        vec![Val::I32(i32::MAX), Val::I64(i64::MAX)],
        vec![Val::I32(0x8080), Val::I64(0x1234_5678_9ABC_DEF0u64 as i64)],
    ];
    differential_check(&unary_and_bits, FuncId(0), &mixed_vecs, 100_000).unwrap();
    let rt = verify_round_trip(&unary_and_bits, FuncId(0), &FuzzConfig::default()).unwrap();
    assert!(matches!(rt, FuzzOutcome::NoCounterexample { vectors_tested: 50_000, .. }));
}

#[test]
fn test_multi_memory_loads_stores_copy_fill_grow_and_u64_ea_bounds() {
    // Module with 2 memories (exported in reverse order: mem1 then mem0!),
    // active data segments on both, 8/16/32/64-bit load/store, memory.copy across memories,
    // memory.fill, memory.size, memory.grow.
    let mut m = WasmModule::new();
    let mut ts = TypeSection::new();
    ts.ty().function([WVal::I32, WVal::I64], [WVal::I64]);
    m.section(&ts);

    let mut fs = FunctionSection::new();
    fs.function(0);
    m.section(&fs);

    let mut ms = MemorySection::new();
    ms.memory(MemoryType {
        minimum: 1,
        maximum: Some(2),
        memory64: false,
        shared: false,
        page_size_log2: None,
    });
    ms.memory(MemoryType {
        minimum: 1,
        maximum: Some(3),
        memory64: false,
        shared: false,
        page_size_log2: None,
    });
    m.section(&ms);

    let mut exps = ExportSection::new();
    exps.export("f", ExportKind::Func, 0);
    exps.export("mem1", ExportKind::Memory, 1);
    exps.export("mem0", ExportKind::Memory, 0);
    m.section(&exps);

    let mut cs = CodeSection::new();
    let mut f = Function::new([(1, WVal::I32)]);
    {
        let mut s = f.instructions();
        // Store val (i64) at mem0[addr + 4]
        s.local_get(0).local_get(1).i64_store(ma(0, 4, 3));
        // Store low byte at mem1[addr]
        s.local_get(0).local_get(1).i64_store8(ma(1, 0, 0));
        // Fill 4 bytes in mem1 at 100
        s.i32_const(100).i32_const(0xAB).i32_const(4).memory_fill(1);
        // Copy 8 bytes from mem0[addr + 4] to mem1[200]
        s.i32_const(200).local_get(0).i32_const(4).i32_add().i32_const(8).memory_copy(1, 0);
        // Grow mem0 by (addr & 1) pages, save old size
        s.local_get(0).i32_const(1).i32_and().memory_grow(0).local_set(2);
        // Combine mem1[200] (i64_load), mem0.size, mem1.size, and load32_s from mem1[0]
        s.i32_const(200).i64_load(ma(1, 0, 3));
        s.i32_const(0).i64_load32_s(ma(1, 0, 2)).i64_add();
        s.memory_size(0).i64_extend_i32_u().i64_add();
        s.local_get(2).i64_extend_i32_s().i64_add();
        s.end();
    }
    cs.function(&f);
    m.section(&cs);

    let mut ds = DataSection::new();
    ds.active(0, &ConstExpr::i32_const(16), b"hello-mem0".iter().copied());
    ds.active(1, &ConstExpr::i32_const(32), b"world-mem1".iter().copied());
    m.section(&ds);

    let wasm = m.finish();

    let vecs = vec![
        vec![Val::I32(0), Val::I64(0x1122_3344_5566_7788)],
        vec![Val::I32(1024), Val::I64(-42)],
        vec![Val::I32(65524), Val::I64(999)],     // near end of page 0 -> fits (65524 + 4 + 8 = 65536)
        vec![Val::I32(65528), Val::I64(999)],     // OOB: 65528 + 4 + 8 = 65540 > 65536
        vec![Val::I32(-16i32), Val::I64(1)],      // u32 wrap trap: 0xFFFF_FFF0 + 4 > 65536!
    ];
    differential_check(&wasm, FuncId(0), &vecs, 100_000).unwrap();

    // Check explicit wrap-around EA trap (0xFFFF_FFFC + 4 must trap OutOfBoundsMem, not wrap to 0!)
    let wrap_wasm = mem_fn_wasm(1, Some(1), &[], &[WVal::I32], &[WVal::I32], &[], |s| {
        s.local_get(0).i32_load(ma(0, 8, 2));
    });
    assert_eq!(
        run_wasmtime_func(&wrap_wasm, "f", &[Val::I32(-4)], 10_000).unwrap().0,
        ExecOutcome::Trap(TrapCode::OutOfBoundsMem)
    );
    differential_check(
        &wrap_wasm,
        FuncId(0),
        &[vec![Val::I32(-4)], vec![Val::I32(-8)], vec![Val::I32(65524)], vec![Val::I32(65525)]],
        10_000,
    )
    .unwrap();
}

#[test]
fn test_structured_control_flow_loops_mut_locals_br_table_and_unreachable_stacks() {
    // Exercises:
    // - block with FuncType params & multi-value results
    // - loop with params + mutated locals + conditional br_if (continue) & fallthrough exit
    // - if without else mutating locals
    // - br_table jumping across nested blocks + polymorphic dead stack after br_table
    // - local.tee, typed_select
    let mut m = WasmModule::new();
    let mut ts = TypeSection::new();
    ts.ty().function([WVal::I32, WVal::I32], [WVal::I32]); // type 0
    ts.ty().function([WVal::I32], [WVal::I32, WVal::I32]); // type 1
    m.section(&ts);

    let mut fs = FunctionSection::new();
    fs.function(0);
    m.section(&fs);

    let mut exps = ExportSection::new();
    exps.export("f", ExportKind::Func, 0);
    m.section(&exps);

    let mut cs = CodeSection::new();
    let mut f = Function::new([(2, WVal::I32)]); // 0=x, 1=y, 2=acc, 3=cnt
    {
        let mut s = f.instructions();
        s.i32_const(10).local_set(2);
        s.local_get(0).i32_const(15).i32_and().local_set(3);

        // 1. br_table over 3 nested blocks + unreachable dead code
        s.block(BlockType::Empty);
        s.block(BlockType::Empty);
        s.block(BlockType::Empty);
        s.local_get(3).br_table([0, 1], 2);
        // Polymorphic dead code after br_table
        s.i32_add().drop();
        s.end();
        s.local_get(2).i32_const(1).i32_add().local_set(2);
        s.end();
        s.local_get(2).i32_const(2).i32_add().local_set(2);
        s.end();

        // 2. if without else mutating local 2 + block with FuncType(1)
        s.local_get(1);
        s.block(BlockType::FunctionType(1));
        // stack: [y]
        s.local_get(3).i32_const(1).i32_and();
        s.if_(BlockType::Empty);
        s.local_get(2).i32_const(5).i32_add().local_set(2);
        s.end();
        s.local_get(2); // stack: [y, acc]
        // Early br_if out of FuncType(1) block carrying [y, acc]!
        s.local_get(0).i32_const(2).i32_and().br_if(0);
        s.i32_const(3).i32_add();
        s.end();
        s.i32_xor().local_set(2);

        // 3. Loop with param [i32] and mutated local 2, testing br_if continue AND fallthrough exit
        s.local_get(3); // initial iter arg
        s.loop_(BlockType::FunctionType(1)); // param [i32] -> result [i32, i32]
        s.local_tee(3); // stack: [iter], local 3 = iter
        s.local_get(2).i32_add().local_set(2); // acc += iter
        s.local_get(3).i32_const(1).i32_sub(); // stack: [iter - 1]
        s.local_get(3).i32_const(0).i32_gt_s().br_if(0); // continue loop with iter - 1 if iter > 0!
        // Fall off loop end with [iter - 1, acc]
        s.local_get(2);
        s.end();
        s.i32_add(); // combine both loop outputs

        // 4. typed_select: select(true_val=y, false_val=x, cond=(x & 1))
        s.local_get(1).local_get(0).local_get(0).i32_const(1).i32_and().typed_select(WVal::I32);
        s.i32_add();
        s.end();
    }
    cs.function(&f);
    m.section(&cs);
    let wasm = m.finish();

    let mut vecs = Vec::new();
    for x in -5..=20 {
        for y in [-1, 0, 1, 7, 42] {
            vecs.push(vec![Val::I32(x), Val::I32(y)]);
        }
    }
    differential_check(&wasm, FuncId(0), &vecs, 100_000).unwrap();
    let rt = verify_round_trip(&wasm, FuncId(0), &FuzzConfig::default()).unwrap();
    assert!(matches!(rt, FuzzOutcome::NoCounterexample { vectors_tested: 50_000, .. }));
}

#[test]
fn test_imports_internal_calls_globals_and_polymorphic_return_if() {
    // Module with 1 imported host func, 2 defined funcs (helper + entry),
    // 1 mutable global, 1 immutable global, and an if/else where both branches return.
    let mut m = WasmModule::new();
    let mut ts = TypeSection::new();
    ts.ty().function([WVal::I32], [WVal::I32]); // type 0
    ts.ty().function([WVal::I32, WVal::I32], [WVal::I32]); // type 1
    m.section(&ts);

    let mut imps = ImportSection::new();
    imps.import("env", "host_zero", EntityType::Function(0)); // func 0 (HostCallId(0))
    m.section(&imps);

    let mut fs = FunctionSection::new();
    fs.function(0); // func 1 -> FuncId(0) (helper)
    fs.function(1); // func 2 -> FuncId(1) (main)
    m.section(&fs);

    let mut gs = GlobalSection::new();
    gs.global(
        GlobalType { val_type: WVal::I32, mutable: true, shared: false },
        &ConstExpr::i32_const(100),
    );
    gs.global(
        GlobalType { val_type: WVal::I32, mutable: false, shared: false },
        &ConstExpr::i32_const(7),
    );
    m.section(&gs);

    let mut exps = ExportSection::new();
    exps.export("main", ExportKind::Func, 2);
    exps.export("g0", ExportKind::Global, 0);
    m.section(&exps);

    let mut cs = CodeSection::new();
    // helper(x): if x < 0 { return -x; } else { return x + 1; }
    let mut f_helper = Function::new([]);
    {
        let mut s = f_helper.instructions();
        s.local_get(0).i32_const(0).i32_lt_s();
        s.if_(BlockType::Result(WVal::I32));
        s.i32_const(0).local_get(0).i32_sub().return_();
        s.else_();
        s.local_get(0).i32_const(1).i32_add().return_();
        s.end();
        s.end();
    }
    cs.function(&f_helper);

    // main(a, b): calls host_zero(a), mutates g0, calls helper(b), returns g0 + g1 + helper(b)
    let mut f_main = Function::new([]);
    {
        let mut s = f_main.instructions();
        s.local_get(0).call(0); // HostCallId(0) -> returns 0
        s.global_get(0).i32_add().local_get(0).i32_add().global_set(0);
        s.global_get(0).global_get(1).i32_add();
        s.local_get(1).call(1).i32_add();
        s.end();
    }
    cs.function(&f_main);
    m.section(&cs);

    let wasm = m.finish();
    let vecs = vec![
        vec![Val::I32(5), Val::I32(-3)],
        vec![Val::I32(-10), Val::I32(4)],
        vec![Val::I32(0), Val::I32(i32::MIN)],
    ];
    differential_check(&wasm, FuncId(1), &vecs, 100_000).unwrap();

    // Test hand-constructed Module with InvariantLoop & BoundedLoop -> emit_wasm -> wasmtime!
    let mod_ir = Module {
        memories: vec![MemoryDef { id: MemId(0), min_pages: 1, max_pages: Some(1), init_data: vec![] }],
        globals: vec![GlobalDef { id: GlobalId(0), ty: ValType::I32, mutable: true, init: Val::I32(0) }],
        host_contracts: vec![],
        funcs: vec![FuncDef {
            id: FuncId(0),
            name: "sum_to".into(),
            export_name: Some("sum_to".into()),
            params: vec![(ValId(0), ValType::I32)],
            results: vec![ValType::I32],
            body: {
                let loop_body = Region::build(|b| {
                    b.push_let(ValId(5), ValType::I32, Op::Bin(BinOp::I32LeS, ValId(4), ValId(1)));
                    b.push_break(0, Some(ValId(5)), &[ValId(3), ValId(4)]);
                    b.push_let(ValId(6), ValType::I32, Op::Bin(BinOp::I32Add, ValId(3), ValId(4)));
                    b.push_let(ValId(7), ValType::I32, Op::Bin(BinOp::I32Sub, ValId(4), ValId(2)));
                    b.push_continue(0, None, &[ValId(6), ValId(7)]);
                });
                let lp = Region::bounded_loop(
                    u32::MAX,
                    &[ValId(1), ValId(0)],
                    &[(ValId(3), ValType::I32), (ValId(4), ValType::I32)],
                    &loop_body,
                );
                Region::build(|b| {
                    b.push_let(ValId(1), ValType::I32, Op::ConstI32(0));
                    b.push_let(ValId(2), ValType::I32, Op::ConstI32(1));
                    b.push_subregion(&[(ValId(10), ValType::I32), (ValId(11), ValType::I32)], &lp);
                    b.push_effect(EffectOp::GlobalSet { id: GlobalId(0), val: ValId(10) });
                    b.push_let(ValId(12), ValType::I32, Op::Un(UnOp::I32Clz, ValId(10)));
                    b.push_let(ValId(13), ValType::I32, Op::Bin(BinOp::I32Add, ValId(10), ValId(12)));
                    b.push_yield(&[ValId(13)]);
                })
            },
        }],
        memory_exports: vec![("mem".into(), MemId(0))],
        global_exports: vec![],
    };
    let emitted = emit_wasm(&mod_ir).unwrap();
    let reg = StratumRegistry::new();
    for n in 0..=20 {
        let h = HeapState::from_module(&mod_ir, 100_000).unwrap();
        let (kvals, _) = eval_func(&mod_ir, &reg, FuncId(0), &[Val::I32(n)], h).unwrap();
        let (wout, _) = run_wasmtime_func(&emitted, "sum_to", &[Val::I32(n)], 100_000).unwrap();
        assert_eq!(ExecOutcome::Values(kvals), wout);
    }
}

#[test]
fn test_rustc_cdylib_real_wasm_roundtrip_and_differential() {
    let src = r#"#![no_std]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }

static LUT: [i32; 8] = [3, 1, 4, 1, 5, 9, 2, 6];

#[unsafe(no_mangle)]
pub extern "C" fn rustc_kernel(n: i32, mode: i32) -> i32 {
    let mut buf = [0u8; 16];
    let fill_byte = (n as u8) ^ 0x5A;
    buf.fill(fill_byte);
    let mut acc: i32 = LUT[(n as usize) & 7];
    let mut i: i32 = 0;
    while i < (n & 7) {
        acc = match mode & 3 {
            0 => acc.wrapping_add((buf[(i as usize) & 15] as i8) as i32),
            1 => acc.wrapping_sub(LUT[(i as usize) & 7]),
            2 => acc.wrapping_mul(3).wrapping_add(i),
            _ => acc ^ ((i as i16) as i32).rotate_left((mode & 15) as u32),
        };
        i += 1;
    }
    acc
}
"#;
    let unique = std::process::id();
    let rs_path = std::env::temp_dir().join(format!("gnomon_rustc_test_{unique}.rs"));
    let wasm_path = std::env::temp_dir().join(format!("gnomon_rustc_test_{unique}.wasm"));
    std::fs::write(&rs_path, src).unwrap();

    let status = Command::new("rustc")
        .args([
            "--target",
            "wasm32-unknown-unknown",
            "--crate-type",
            "cdylib",
            "-C",
            "opt-level=2",
        ])
        .arg(&rs_path)
        .arg("-o")
        .arg(&wasm_path)
        .status()
        .expect("rustc must be available");
    assert!(status.success(), "rustc wasm32 cdylib build failed");

    let wasm_bytes = std::fs::read(&wasm_path).unwrap();
    let _ = std::fs::remove_file(&rs_path);
    let _ = std::fs::remove_file(&wasm_path);

    let lifted = lift_wasm(&wasm_bytes).unwrap();
    assert!(!lifted.funcs.is_empty());

    let mut vecs = Vec::new();
    for n in [-100, -1, 0, 1, 2, 3, 7, 8, 15, 255, i32::MIN, i32::MAX] {
        for mode in 0..8 {
            vecs.push(vec![Val::I32(n), Val::I32(mode)]);
        }
    }
    differential_check(&wasm_bytes, FuncId(0), &vecs, 200_000).unwrap();

    let rt = verify_round_trip(
        &wasm_bytes,
        FuncId(0),
        &FuzzConfig {
            total_vectors: 1_000,
            fuel_per_run: 200_000,
            seed: 42,
        },
    )
    .unwrap();
    assert!(matches!(rt, FuzzOutcome::NoCounterexample { vectors_tested: 1_000, .. }));
}

#[test]
fn test_stage1_falsification_speed_and_equivalence() {
    // Equivalent strength reduction: (x * 8) === (x << 3)
    let mul8 = single_fn_wasm(&[WVal::I32], &[WVal::I32], &[], |s| {
        s.local_get(0).i32_const(8).i32_mul();
    });
    let shl3 = single_fn_wasm(&[WVal::I32], &[WVal::I32], &[], |s| {
        s.local_get(0).i32_const(3).i32_shl();
    });
    let eq_res = fuzz_equivalence(&mul8, &shl3, FuncId(0), &FuzzConfig::default()).unwrap();
    match eq_res {
        FuzzOutcome::NoCounterexample { vectors_tested, elapsed_micros } => {
            assert_eq!(vectors_tested, 50_000);
            println!("Stage-1 50k equivalent pass elapsed_micros={elapsed_micros}");
        }
        FuzzOutcome::Falsified(cx) => panic!("unexpected falsification: {cx:?}"),
    }

    // Buggy optimization: (x / 2) != (x >> 1) for negative odd x!
    let div2 = single_fn_wasm(&[WVal::I32], &[WVal::I32], &[], |s| {
        s.local_get(0).i32_const(2).i32_div_s();
    });
    let shr1 = single_fn_wasm(&[WVal::I32], &[WVal::I32], &[], |s| {
        s.local_get(0).i32_const(1).i32_shr_s();
    });
    let t0 = Instant::now();
    let bad_res = fuzz_equivalence(&div2, &shr1, FuncId(0), &FuzzConfig::default()).unwrap();
    let wall_us = t0.elapsed().as_micros();
    match bad_res {
        FuzzOutcome::Falsified(cx) => {
            assert_ne!(cx.lhs_outcome, cx.rhs_outcome);
            println!(
                "Stage-1 falsified (x/2 vs x>>1) on input {:?} in {} us",
                cx.inputs, wall_us
            );
        }
        FuzzOutcome::NoCounterexample { .. } => panic!("expected falsification"),
    }

    // Memory divergence falsification + fuzz_equivalence_by_name across different FuncIds
    let mem_a = {
        let mut m = WasmModule::new();
        let mut ts = TypeSection::new();
        ts.ty().function([], [WVal::I32]);
        ts.ty().function([WVal::I32, WVal::I32], [WVal::I32]);
        m.section(&ts);
        let mut fs = FunctionSection::new();
        fs.function(0);
        fs.function(1);
        m.section(&fs);
        let mut ms = MemorySection::new();
        ms.memory(MemoryType { minimum: 1, maximum: Some(1), memory64: false, shared: false, page_size_log2: None });
        m.section(&ms);
        let mut exps = ExportSection::new();
        exps.export("helper", ExportKind::Func, 0);
        exps.export("target", ExportKind::Func, 1);
        exps.export("mem", ExportKind::Memory, 0);
        m.section(&exps);
        let mut cs = CodeSection::new();
        let mut f0 = Function::new([]);
        f0.instructions().i32_const(0).end();
        cs.function(&f0);
        let mut f1 = Function::new([]);
        f1.instructions()
            .local_get(0).i32_const(65535).i32_and()
            .local_get(1)
            .i32_store8(ma(0, 0, 0))
            .local_get(1)
            .end();
        cs.function(&f1);
        m.section(&cs);
        m.finish()
    };
    let mem_b_target = {
        let mut m = WasmModule::new();
        let mut ts = TypeSection::new();
        ts.ty().function([WVal::I32, WVal::I32], [WVal::I32]);
        m.section(&ts);
        let mut fs = FunctionSection::new();
        fs.function(0);
        m.section(&fs);
        let mut ms = MemorySection::new();
        ms.memory(MemoryType { minimum: 1, maximum: Some(1), memory64: false, shared: false, page_size_log2: None });
        m.section(&ms);
        let mut exps = ExportSection::new();
        exps.export("target", ExportKind::Func, 0);
        exps.export("mem", ExportKind::Memory, 0);
        m.section(&exps);
        let mut cs = CodeSection::new();
        let mut f = Function::new([]);
        f.instructions()
            .local_get(0).i32_const(65535).i32_and()
            .local_get(0).i32_const(4096).i32_eq()
            .if_(BlockType::Result(WVal::I32))
            .local_get(1).i32_const(1).i32_xor()
            .else_()
            .local_get(1)
            .end()
            .i32_store8(ma(0, 0, 0))
            .local_get(1)
            .end();
        cs.function(&f);
        m.section(&cs);
        m.finish()
    };
    let mem_bug = fuzz_equivalence_by_name(&mem_a, &mem_b_target, "target", &FuzzConfig::default()).unwrap();
    match mem_bug {
        FuzzOutcome::Falsified(cx) => {
            assert_eq!(cx.lhs_outcome, cx.rhs_outcome);
            assert_eq!(cx.memory_snapshots.len(), 1);
            assert_eq!(cx.inputs[0], Val::I32(4096));
        }
        FuzzOutcome::NoCounterexample { .. } => panic!("expected memory falsification at 4096"),
    }

    // Infinite loop OutOfFuel equivalence
    let inf = single_fn_wasm(&[], &[WVal::I32], &[], |s| {
        s.loop_(BlockType::Result(WVal::I32)).br(0).end();
    });
    assert_eq!(
        run_wasmtime_func(&inf, "f", &[], 1_000).unwrap().0,
        ExecOutcome::Trap(TrapCode::OutOfFuel)
    );
    differential_check(&inf, FuncId(0), &[vec![]], 1_000).unwrap();
}

static PROP_DIFF_CHECKS: AtomicUsize = AtomicUsize::new(0);

#[derive(Clone, Debug)]
enum RandExpr {
    Arg0,
    Arg1,
    Const(i32),
    Un(u8, Box<RandExpr>),
    Bin(u8, Box<RandExpr>, Box<RandExpr>),
    IfThenElse(Box<RandExpr>, Box<RandExpr>, Box<RandExpr>),
}

fn arb_expr() -> impl Strategy<Value = RandExpr> {
    let leaf = prop_oneof![
        Just(RandExpr::Arg0),
        Just(RandExpr::Arg1),
        any::<i32>().prop_map(RandExpr::Const),
    ];
    leaf.prop_recursive(4, 32, 3, |inner| {
        prop_oneof![
            (0u8..6, inner.clone()).prop_map(|(op, a)| RandExpr::Un(op, Box::new(a))),
            (0u8..21, inner.clone(), inner.clone())
                .prop_map(|(op, a, b)| RandExpr::Bin(op, Box::new(a), Box::new(b))),
            (inner.clone(), inner.clone(), inner)
                .prop_map(|(c, t, e)| RandExpr::IfThenElse(Box::new(c), Box::new(t), Box::new(e))),
        ]
    })
}

fn emit_rand_expr(e: &RandExpr, s: &mut InstructionSink<'_>) {
    match e {
        RandExpr::Arg0 => { s.local_get(0); }
        RandExpr::Arg1 => { s.local_get(1); }
        RandExpr::Const(v) => { s.i32_const(*v); }
        RandExpr::Un(op, a) => {
            emit_rand_expr(a, s);
            match op % 6 {
                0 => { s.i32_eqz(); }
                1 => { s.i32_clz(); }
                2 => { s.i32_ctz(); }
                3 => { s.i32_popcnt(); }
                4 => { s.i32_extend8_s(); }
                _ => { s.i32_extend16_s(); }
            }
        }
        RandExpr::Bin(op, a, b) => {
            emit_rand_expr(a, s);
            emit_rand_expr(b, s);
            match op % 21 {
                0 => { s.i32_add(); }
                1 => { s.i32_sub(); }
                2 => { s.i32_mul(); }
                3 => { s.i32_div_s(); }
                4 => { s.i32_div_u(); }
                5 => { s.i32_rem_s(); }
                6 => { s.i32_rem_u(); }
                7 => { s.i32_and(); }
                8 => { s.i32_or(); }
                9 => { s.i32_xor(); }
                10 => { s.i32_shl(); }
                11 => { s.i32_shr_s(); }
                12 => { s.i32_shr_u(); }
                13 => { s.i32_rotl(); }
                14 => { s.i32_rotr(); }
                15 => { s.i32_eq(); }
                16 => { s.i32_ne(); }
                17 => { s.i32_lt_s(); }
                18 => { s.i32_lt_u(); }
                19 => { s.i32_gt_s(); }
                _ => { s.i32_le_u(); }
            }
        }
        RandExpr::IfThenElse(c, t, e) => {
            emit_rand_expr(c, s);
            s.local_tee(2); // exercise local.tee inside expressions!
            s.if_(BlockType::Result(WVal::I32));
            emit_rand_expr(t, s);
            s.local_get(2).i32_add();
            s.else_();
            emit_rand_expr(e, s);
            s.local_get(2).i32_xor();
            s.end();
        }
    }
}

#[test]
fn test_proptest_and_corpus_over_10000_differential_checks() {
    // Part A: 10,000+ deterministic + PRNG differential checks over rich structured Wasm programs
    // covering arithmetic, 64-bit ops, multi-memory, loops, br_table, local.tee, select, traps.
    let loop_and_mem = mem_fn_wasm(
        1,
        Some(2),
        &[(0, &[1, 2, 3, 4, 5, 6, 7, 8])],
        &[WVal::I32, WVal::I32],
        &[WVal::I32],
        &[(2, WVal::I32)],
        |s| {
            // local 2 = sum, local 3 = i
            s.i32_const(0).local_set(2);
            s.i32_const(0).local_set(3);
            s.block(BlockType::Empty);
            s.loop_(BlockType::Empty);
            s.local_get(3).local_get(0).i32_const(7).i32_and().i32_ge_s().br_if(1);
            // Store (x ^ i) at mem[(i * 4) + 16]
            s.local_get(3).i32_const(2).i32_shl().i32_const(16).i32_add();
            s.local_get(0).local_get(3).i32_xor();
            s.i32_store(ma(0, 0, 2));
            // Update sum with branchy select & local.tee
            s.local_get(2)
                .local_get(3).i32_const(2).i32_shl().i32_load(ma(0, 16, 2))
                .i32_add()
                .local_get(1)
                .i32_xor()
                .local_tee(2)
                .drop();
            s.local_get(3).i32_const(1).i32_add().local_set(3);
            s.br(0);
            s.end();
            s.end();
            s.local_get(2);
        },
    );

    let mut batch_inputs = Vec::with_capacity(6_000);
    let mut seed = 0xCAFE_BABE_1234_5678u64;
    let mut next_u64 = || {
        seed = seed.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = seed;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    };
    for _ in 0..6_000 {
        let a = next_u64() as i32;
        let b = (next_u64() >> 32) as i32;
        batch_inputs.push(vec![Val::I32(a), Val::I32(b)]);
    }
    differential_check(&loop_and_mem, FuncId(0), &batch_inputs, 100_000).unwrap();
    PROP_DIFF_CHECKS.fetch_add(batch_inputs.len(), Ordering::Relaxed);

    // Part B: 64-bit arithmetic + trap differential batch (2,500 vectors)
    let i64_prog = single_fn_wasm(&[WVal::I64, WVal::I64], &[WVal::I64], &[], |s| {
        s.local_get(0).local_get(1).i64_const(1).i64_or().i64_div_s();
        s.local_get(0).local_get(1).i64_rotl().i64_xor();
        s.local_get(0).i64_extend32_s().i64_add();
    });
    let mut i64_inputs = vec![
        vec![Val::I64(i64::MIN), Val::I64(-1)],
        vec![Val::I64(i64::MIN), Val::I64(-2)],
        vec![Val::I64(0), Val::I64(0)],
    ];
    for _ in 0..2_497 {
        i64_inputs.push(vec![Val::I64(next_u64() as i64), Val::I64(next_u64() as i64)]);
    }
    differential_check(&i64_prog, FuncId(0), &i64_inputs, 100_000).unwrap();
    PROP_DIFF_CHECKS.fetch_add(i64_inputs.len(), Ordering::Relaxed);

    // Part C: Proptest randomly generated Wasm ASTs (256 modules * 16 input pairs = 4,096 checks)
    let mut runner = proptest::test_runner::TestRunner::new(ProptestConfig {
        cases: 256,
        ..ProptestConfig::default()
    });
    runner
        .run(
            &(
                arb_expr(),
                prop::collection::vec((any::<i32>(), any::<i32>()), 16),
            ),
            |(expr, pairs)| {
                let wasm = single_fn_wasm(
                    &[WVal::I32, WVal::I32],
                    &[WVal::I32],
                    &[(1, WVal::I32)],
                    |s| emit_rand_expr(&expr, s),
                );
                let mut vecs: Vec<Vec<Val>> = pairs
                    .into_iter()
                    .map(|(a, b)| vec![Val::I32(a), Val::I32(b)])
                    .collect();
                vecs[0] = vec![Val::I32(i32::MIN), Val::I32(-1)];
                vecs[1] = vec![Val::I32(0), Val::I32(0)];
                differential_check(&wasm, FuncId(0), &vecs, 100_000).map_err(|e| {
                    TestCaseError::fail(format!("proptest differential failure: {e}"))
                })?;
                PROP_DIFF_CHECKS.fetch_add(vecs.len(), Ordering::Relaxed);
                Ok(())
            },
        )
        .unwrap();

    let total = PROP_DIFF_CHECKS.load(Ordering::Relaxed);
    println!("Total differential checks passed: {total}");
    assert!(total >= 10_000, "expected >= 10,000 differential checks, got {total}");
}

#[test]
fn test_error_handling_for_invalid_and_unsupported_wasm() {
    assert!(matches!(lift_wasm(b"not-wasm"), Err(WasmError::ValidationError(_))));

    // Reference-typed function (`externref`) should return UnsupportedFeature cleanly
    let mut m = WasmModule::new();
    let mut ts = TypeSection::new();
    ts.ty().function([WVal::EXTERNREF], [WVal::EXTERNREF]);
    m.section(&ts);
    let mut fs = FunctionSection::new();
    fs.function(0);
    m.section(&fs);
    let mut cs = CodeSection::new();
    let mut f = Function::new([]);
    f.instructions().local_get(0).end();
    cs.function(&f);
    m.section(&cs);
    assert!(matches!(lift_wasm(&m.finish()), Err(WasmError::UnsupportedFeature(_))));
}

#[test]
fn test_all_19_load_store_widths_and_br_table_to_loop_and_func() {
    // 1. All 19 deterministic load/store instructions with non-zero offsets
    let mem_all = mem_fn_wasm(1, Some(1), &[], &[WVal::I32, WVal::I64], &[WVal::I64], &[], |s| {
        let x = 0;
        let v64 = 1;
        // Stores
        s.i32_const(0).local_get(x).i32_store8(ma(0, 1, 0));
        s.i32_const(0).local_get(x).i32_store16(ma(0, 4, 1));
        s.i32_const(0).local_get(x).i32_store(ma(0, 8, 2));
        s.i32_const(0).local_get(v64).i64_store8(ma(0, 16, 0));
        s.i32_const(0).local_get(v64).i64_store16(ma(0, 20, 1));
        s.i32_const(0).local_get(v64).i64_store32(ma(0, 24, 2));
        s.i32_const(0).local_get(v64).i64_store(ma(0, 32, 3));
        // Loads: sum all 12 load instructions
        s.i32_const(0).i32_load8_s(ma(0, 1, 0)).i64_extend_i32_s();
        s.i32_const(0).i32_load8_u(ma(0, 1, 0)).i64_extend_i32_u().i64_add();
        s.i32_const(0).i32_load16_s(ma(0, 4, 1)).i64_extend_i32_s().i64_add();
        s.i32_const(0).i32_load16_u(ma(0, 4, 1)).i64_extend_i32_u().i64_add();
        s.i32_const(0).i32_load(ma(0, 8, 2)).i64_extend_i32_s().i64_add();
        s.i32_const(0).i64_load8_s(ma(0, 16, 0)).i64_add();
        s.i32_const(0).i64_load8_u(ma(0, 16, 0)).i64_add();
        s.i32_const(0).i64_load16_s(ma(0, 20, 1)).i64_add();
        s.i32_const(0).i64_load16_u(ma(0, 20, 1)).i64_add();
        s.i32_const(0).i64_load32_s(ma(0, 24, 2)).i64_add();
        s.i32_const(0).i64_load32_u(ma(0, 24, 2)).i64_add();
        s.i32_const(0).i64_load(ma(0, 32, 3)).i64_add();
    });
    let mem_vecs = vec![
        vec![Val::I32(0), Val::I64(0)],
        vec![Val::I32(-1), Val::I64(-1)],
        vec![Val::I32(0x8080_8080u32 as i32), Val::I64(0x8000_0000_8000_8080u64 as i64)],
        vec![Val::I32(i32::MAX), Val::I64(i64::MIN)],
    ];
    differential_check(&mem_all, FuncId(0), &mem_vecs, 100_000).unwrap();

    // 2. br_table jumping simultaneously to loop (depth 0), block (depth 1), and func root (depth 2)
    let mut m = WasmModule::new();
    let mut ts = TypeSection::new();
    ts.ty().function([WVal::I32], [WVal::I32]); // type 0: [i32] -> [i32] (used for func AND loop!)
    m.section(&ts);
    let mut fs = FunctionSection::new();
    fs.function(0);
    m.section(&fs);
    let mut exps = ExportSection::new();
    exps.export("f", ExportKind::Func, 0);
    m.section(&exps);
    let mut cs = CodeSection::new();
    let mut f = Function::new([(1, WVal::I32)]); // local 0 = n, local 1 = acc
    {
        let mut s = f.instructions();
        s.i32_const(0).local_set(1);
        s.block(BlockType::Result(WVal::I32));
        s.local_get(0); // initial loop param
        s.loop_(BlockType::FunctionType(0)); // [i32] -> [i32]; label arity = 1!
        s.local_tee(0);
        s.local_get(1).i32_add().local_set(1); // acc += n
        // Next branch arg on stack: n + 10 (for block/func) or n - 1 (via local_get(0) - 1)
        s.local_get(0).i32_const(1).i32_sub(); // branch arg = n - 1
        // Selector: if n <= 0 -> 1 (exit block); if n > 5 -> 2 (return from func!); else -> 0 (continue loop!)
        s.local_get(0).i32_const(0).i32_le_s();
        s.if_(BlockType::Result(WVal::I32));
        s.i32_const(1);
        s.else_();
        s.local_get(0).i32_const(5).i32_gt_s();
        s.if_(BlockType::Result(WVal::I32));
        s.i32_const(2);
        s.else_();
        s.i32_const(0);
        s.end();
        s.end();
        // br_table: 0 -> loop (depth 0), 1 -> block (depth 1), default -> func root (depth 2)!
        s.br_table([0, 1], 2);
        s.end(); // end loop
        s.end(); // end block
        // Only reached when br_table jumped to depth 1 (block)! Add mutated local 1 (acc)!
        s.local_get(1).i32_add();
        s.end();
    }
    cs.function(&f);
    m.section(&cs);
    let br_table_wasm = m.finish();

    let br_vecs: Vec<Vec<Val>> = (-2..=10).map(|x| vec![Val::I32(x)]).collect();
    differential_check(&br_table_wasm, FuncId(0), &br_vecs, 100_000).unwrap();
    let rt = verify_round_trip(&br_table_wasm, FuncId(0), &FuzzConfig::default()).unwrap();
    assert!(matches!(rt, FuzzOutcome::NoCounterexample { vectors_tested: 50_000, .. }));
}

#[test]
fn test_invariant_loop_emit_and_swapped_state_vars() {
    // Tests emitting InvariantLoop AND BoundedLoop swapping state_vars (a, b) -> (b, a)
    let mod_ir = Module {
        memories: vec![],
        globals: vec![],
        host_contracts: vec![],
        funcs: vec![FuncDef {
            id: FuncId(0),
            name: "fib_swap".into(),
            export_name: Some("fib_swap".into()),
            params: vec![(ValId(0), ValType::I32)],
            results: vec![ValType::I32],
            body: {
                let cond = Region::build(|b| {
                    b.push_let(ValId(6), ValType::I32, Op::Bin(BinOp::I32GtS, ValId(3), ValId(1)));
                    b.push_yield(&[ValId(6)]);
                });
                let inv = Region::yield_vals(&[ValId(2)]);
                let fuel = Region::build(|b| {
                    b.push_let(ValId(7), ValType::I64, Op::Un(UnOp::I64ExtendI32U, ValId(3)));
                    b.push_yield(&[ValId(7)]);
                });
                let body_lp = Region::build(|b| {
                    b.push_let(ValId(8), ValType::I32, Op::Bin(BinOp::I32Sub, ValId(3), ValId(2)));
                    b.push_let(ValId(9), ValType::I32, Op::Bin(BinOp::I32Add, ValId(4), ValId(5)));
                    b.push_yield(&[ValId(8), ValId(5), ValId(9)]);
                });
                let lp = Region::invariant_loop(
                    &[ValId(0), ValId(1), ValId(2)],
                    &[(ValId(3), ValType::I32), (ValId(4), ValType::I32), (ValId(5), ValType::I32)],
                    &cond,
                    &inv,
                    &fuel,
                    &body_lp,
                );
                Region::build(|b| {
                    b.push_let(ValId(1), ValType::I32, Op::ConstI32(0));
                    b.push_let(ValId(2), ValType::I32, Op::ConstI32(1));
                    b.push_subregion(
                        &[(ValId(20), ValType::I32), (ValId(21), ValType::I32), (ValId(22), ValType::I32)],
                        &lp,
                    );
                    b.push_yield(&[ValId(21)]);
                })
            },
        }],
        memory_exports: vec![],
        global_exports: vec![],
    };

    let wasm = emit_wasm(&mod_ir).unwrap();
    let reg = StratumRegistry::new();
    for n in 0..=15 {
        let h = HeapState::from_module(&mod_ir, 100_000).unwrap();
        let (kvals, _) = eval_func(&mod_ir, &reg, FuncId(0), &[Val::I32(n)], h).unwrap();
        let (wout, _) = run_wasmtime_func(&wasm, "fib_swap", &[Val::I32(n)], 100_000).unwrap();
        assert_eq!(ExecOutcome::Values(kvals), wout);
    }
}

#[test]
fn test_exported_mutable_global_falsification_and_bounded_loop_fuel_trap() {
    // 1. Exported mutable global divergence must be falsified even when return values match,
    // and mutable globals must reset cleanly between fuzz vectors.
    let mk_global_mod = |mutate_global: bool| {
        let body = Region::build(|b| {
            b.push_let(ValId(1), ValType::I32, Op::GlobalGet(GlobalId(0)));
            b.push_let(ValId(2), ValType::I32, Op::Bin(BinOp::I32Add, ValId(1), ValId(0)));
            if mutate_global {
                b.push_effect(EffectOp::GlobalSet { id: GlobalId(0), val: ValId(2) });
            }
            b.push_yield(&[ValId(0)]);
        });
        let ir = Module {
            memories: vec![],
            globals: vec![GlobalDef {
                id: GlobalId(0),
                ty: ValType::I32,
                mutable: true,
                init: Val::I32(10),
            }],
            host_contracts: vec![],
            funcs: vec![FuncDef {
                id: FuncId(0),
                name: "step".into(),
                export_name: Some("step".into()),
                params: vec![(ValId(0), ValType::I32)],
                results: vec![ValType::I32],
                body,
            }],
            memory_exports: vec![],
            global_exports: vec![("g0".into(), GlobalId(0))],
        };
        emit_wasm(&ir).unwrap()
    };

    let ref_w = mk_global_mod(true);
    let mut_w = mk_global_mod(false);
    let out = fuzz_equivalence(&ref_w, &mut_w, FuncId(0), &FuzzConfig::default()).unwrap();
    assert!(matches!(out, FuzzOutcome::Falsified(_)), "expected exported global divergence to be caught");

    let vecs: Vec<Vec<Val>> = (0..32).map(|x| vec![Val::I32(x)]).collect();
    differential_check(&ref_w, FuncId(0), &vecs, 100_000).unwrap();

    // 2. Finite BoundedLoop exhaustion emits OutOfFuel trap matching gnomon-kernel,
    // and shadowed ValId in nested Region::Block preserves outer local value.
    let bounded_ir = Module {
        memories: vec![],
        globals: vec![],
        host_contracts: vec![],
        funcs: vec![FuncDef {
            id: FuncId(0),
            name: "spin".into(),
            export_name: Some("spin".into()),
            params: vec![(ValId(0), ValType::I32)],
            results: vec![ValType::I32],
            body: {
                let inner_shadow = Region::build(|b| {
                    // Shadow ValId(0) inside child block!
                    b.push_let(ValId(0), ValType::I32, Op::ConstI32(99));
                    b.push_yield(&[ValId(0)]);
                });
                let lp_body = Region::build(|b| {
                    b.push_let(ValId(2), ValType::I32, Op::ConstI32(0));
                    b.push_let(ValId(3), ValType::I32, Op::Bin(BinOp::I32LeS, ValId(1), ValId(2)));
                    b.push_break(0, Some(ValId(3)), &[ValId(5)]);
                    b.push_let(ValId(4), ValType::I32, Op::ConstI32(1));
                    b.push_let(ValId(7), ValType::I32, Op::Bin(BinOp::I32Sub, ValId(1), ValId(4)));
                    b.push_continue(0, None, &[ValId(7)]);
                });
                let lp = Region::bounded_loop(3, &[ValId(0)], &[(ValId(1), ValType::I32)], &lp_body);
                Region::build(|b| {
                    b.push_subregion(&[(ValId(5), ValType::I32)], &inner_shadow);
                    b.push_subregion(&[(ValId(6), ValType::I32)], &lp);
                    b.push_yield(&[ValId(6)]);
                })
            },
        }],
        memory_exports: vec![],
        global_exports: vec![],
    };
    let bounded_wasm = emit_wasm(&bounded_ir).unwrap();
    let reg = StratumRegistry::new();
    for n in [0, 2, 5] {
        let h = HeapState::from_module(&bounded_ir, 5_000).unwrap();
        let k_res = eval_func(&bounded_ir, &reg, FuncId(0), &[Val::I32(n)], h)
            .map(|(v, _)| ExecOutcome::Values(v))
            .unwrap_or_else(ExecOutcome::Trap);
        let (w_res, _) = run_wasmtime_func(&bounded_wasm, "spin", &[Val::I32(n)], 5_000).unwrap();
        assert_eq!(k_res, w_res, "mismatch for n={n}");
        if n == 5 {
            assert_eq!(w_res, ExecOutcome::Trap(TrapCode::OutOfFuel));
        } else {
            assert_eq!(w_res, ExecOutcome::Values(vec![Val::I32(99)]));
        }
    }
}
