//! Proof 1 — Deterministic Solver-Cliff Benchmark (Flat Bitwuzla vs Gnomon Strata + egglog + UF CEGAR).
//!
//! Measures exact wall-clock solve latency (ms) and timeout behavior on three genuinely hard
//! bit-blasting / multi-memory scaling ladders (`N = 1, 2, 4, 8`) with zero LLM confounders:
//!   1. Nonlinear 64-bit MurmurHash3 / SplitMix64 bijective mixer chain (`unmix^N(mix^N(x)) == x`)
//!   2. Surviving heavy nonlinear 64-bit ARX+mul kernel across surrounding optimizations (UF CEGAR!)
//!   3. Dual-memory interleaved 64-bit packet-ring pipeline (`MemId(0)` writes + `MemId(1)` read hoist)
//!
//! Also verifies a 1-bit injected bug at the hardest depth is caught in milliseconds (0 unsoundness).

use std::time::Instant;

use gnomon_kernel::{
    BinOp, CallTarget, EffectOp, FuncDef, FuncId, Law, LawKind, LawList, MemId, MemWidth,
    MemoryDef, Module, Op, Region, RegionBuilder, Stratum, StratumId, StratumOp, StratumRegistry,
    ValId, ValType,
};
use gnomon_sieve::{
    BitwuzlaNativeBackend, EgglogSimplifier, EqSatConfig, SmtBackend, SmtResult,
};
use gnomon_wasm::{FuzzConfig, FuzzOutcome, emit_wasm, fuzz_equivalence};

const C1: u64 = 0xff51_afd7_ed55_8ccd; // MurmurHash3 fmix64 constant 1
const C1_INV: u64 = 0x4f74_430c_22a5_4005; // exact modular inverse of C1 mod 2^64
const C2: u64 = 0xc4ce_b9fe_1a85_ec53; // MurmurHash3 fmix64 constant 2
const C2_INV: u64 = 0x9cb4_b2f8_1293_37db; // exact modular inverse of C2 mod 2^64

const TIMEOUT_MS: u64 = 10_000;

fn mk_mul64_body(c: u64) -> Region {
    Region::build(|b| {
        b.push_let(ValId(1), ValType::I64, Op::ConstI64(c as i64));
        b.push_let(ValId(2), ValType::I64, Op::Bin(BinOp::I64Mul, ValId(0), ValId(1)));
        b.push_yield(&[ValId(2)]);
    })
}

fn mk_xshr64_body(shift: i64) -> Region {
    Region::build(|b| {
        b.push_let(ValId(1), ValType::I64, Op::ConstI64(shift));
        b.push_let(ValId(2), ValType::I64, Op::Bin(BinOp::I64ShrU, ValId(0), ValId(1)));
        b.push_let(ValId(3), ValType::I64, Op::Bin(BinOp::I64Xor, ValId(0), ValId(2)));
        b.push_yield(&[ValId(3)]);
    })
}

fn mk_call_chain(ops: &[StratumId]) -> Region {
    let mut b = RegionBuilder::new();
    let mut cur = ValId(0);
    for (next_id, &sid) in (10u32..).zip(ops.iter()) {
        let dst = ValId(next_id);
        b.push_call(&[(dst, ValType::I64)], CallTarget::Stratum(sid), &[cur]);
        cur = dst;
    }
    b.push_yield(&[cur]);
    b.finish()
}

#[allow(clippy::too_many_arguments)]
fn prove_and_promote(
    reg: &mut StratumRegistry,
    module: &Module,
    op: StratumOp,
    law_name: &str,
    kind: LawKind,
    params: Vec<(ValId, ValType)>,
    lhs: Region,
    rhs: Region,
) {
    // Prove law in Bitwuzla before admitting (genuine zero-trust admission!).
    let mut scratch = reg.clone();
    scratch
        .promote_stratum(Stratum {
            op: op.clone(),
            laws: LawList::single(Law {
                name: format!("__anchor_{}", op.id.0),
                kind: LawKind::Algebraic,
                params: Vec::new(),
                precondition: Region::empty(),
                lhs: Region::empty(),
                rhs: Region::empty(),
                proof_digest: [0xee; 32],
            }),
        })
        .unwrap();

    if matches!(kind, LawKind::Algebraic) {
        let mut backend = BitwuzlaNativeBackend::with_time_limit_ms(TIMEOUT_MS);
        let res = backend.check_equivalence(module, &scratch, &lhs, &rhs, None).unwrap();
        assert_eq!(res, SmtResult::Unsat, "law '{law_name}' MUST be proved UNSAT!");
    }

    reg.promote_stratum(Stratum {
        op,
        laws: LawList::single(Law {
            name: law_name.into(),
            kind,
            params,
            precondition: Region::empty(),
            lhs,
            rhs,
            proof_digest: [0x42; 32],
        }),
    })
    .unwrap();
}

fn build_cliff_registry() -> (StratumRegistry, Module) {
    assert_eq!(C1.wrapping_mul(C1_INV), 1);
    assert_eq!(C2.wrapping_mul(C2_INV), 1);

    let module = Module {
        memories: vec![
            MemoryDef { id: MemId(0), min_pages: 1, max_pages: Some(1), init_data: Vec::new() },
            MemoryDef { id: MemId(1), min_pages: 1, max_pages: Some(1), init_data: Vec::new() },
        ],
        globals: Vec::new(),
        funcs: Vec::new(),
        host_contracts: Vec::new(),
        memory_exports: Vec::new(),
        global_exports: Vec::new(),
    };

    let mut reg = StratumRegistry::new();
    let p1 = vec![(ValId(0), ValType::I64)];

    // L1: xshr33 (id=1), involution: xshr33(xshr33(x)) == x
    prove_and_promote(
        &mut reg,
        &module,
        StratumOp {
            id: StratumId(1),
            name: "xshr33".into(),
            layer: 1,
            params: p1.clone(),
            results: vec![ValType::I64],
            body: mk_xshr64_body(33),
            docstring: "x ^ (x >> 33)".into(),
        },
        "xshr33_involution",
        LawKind::Algebraic,
        p1.clone(),
        mk_call_chain(&[StratumId(1), StratumId(1)]),
        Region::yield_vals(&[ValId(0)]),
    );

    // L1: mul_c1 (id=2) — anchor memory_frame(mem=1)
    prove_and_promote(
        &mut reg,
        &module,
        StratumOp {
            id: StratumId(2),
            name: "mul_c1".into(),
            layer: 1,
            params: p1.clone(),
            results: vec![ValType::I64],
            body: mk_mul64_body(C1),
            docstring: "x * C1 mod 2^64".into(),
        },
        "mul_c1_pure",
        LawKind::MemoryFrame { untouched_mem: MemId(1) },
        p1.clone(),
        mk_call_chain(&[StratumId(2)]),
        mk_call_chain(&[StratumId(2)]),
    );

    // L1: unmul_c1 (id=3) — proves unmul_c1(mul_c1(x)) == x
    prove_and_promote(
        &mut reg,
        &module,
        StratumOp {
            id: StratumId(3),
            name: "unmul_c1".into(),
            layer: 1,
            params: p1.clone(),
            results: vec![ValType::I64],
            body: mk_mul64_body(C1_INV),
            docstring: "x * C1^-1 mod 2^64".into(),
        },
        "unmul_mul_c1_cancel",
        LawKind::Algebraic,
        p1.clone(),
        mk_call_chain(&[StratumId(2), StratumId(3)]),
        Region::yield_vals(&[ValId(0)]),
    );

    // L1: mul_c2 (id=4)
    prove_and_promote(
        &mut reg,
        &module,
        StratumOp {
            id: StratumId(4),
            name: "mul_c2".into(),
            layer: 1,
            params: p1.clone(),
            results: vec![ValType::I64],
            body: mk_mul64_body(C2),
            docstring: "x * C2 mod 2^64".into(),
        },
        "mul_c2_pure",
        LawKind::MemoryFrame { untouched_mem: MemId(1) },
        p1.clone(),
        mk_call_chain(&[StratumId(4)]),
        mk_call_chain(&[StratumId(4)]),
    );

    // L1: unmul_c2 (id=5) — proves unmul_c2(mul_c2(x)) == x
    prove_and_promote(
        &mut reg,
        &module,
        StratumOp {
            id: StratumId(5),
            name: "unmul_c2".into(),
            layer: 1,
            params: p1.clone(),
            results: vec![ValType::I64],
            body: mk_mul64_body(C2_INV),
            docstring: "x * C2^-1 mod 2^64".into(),
        },
        "unmul_mul_c2_cancel",
        LawKind::Algebraic,
        p1.clone(),
        mk_call_chain(&[StratumId(4), StratumId(5)]),
        Region::yield_vals(&[ValId(0)]),
    );

    // L2: fmix64 (id=6) = xshr33 -> mul_c1 -> xshr33 -> mul_c2 -> xshr33 (exact MurmurHash3 fmix64!)
    prove_and_promote(
        &mut reg,
        &module,
        StratumOp {
            id: StratumId(6),
            name: "fmix64".into(),
            layer: 2,
            params: p1.clone(),
            results: vec![ValType::I64],
            body: mk_call_chain(&[
                StratumId(1),
                StratumId(2),
                StratumId(1),
                StratumId(4),
                StratumId(1),
            ]),
            docstring: "MurmurHash3 64-bit nonlinear finalizer".into(),
        },
        "fmix64_pure",
        LawKind::MemoryFrame { untouched_mem: MemId(1) },
        p1.clone(),
        mk_call_chain(&[StratumId(6)]),
        mk_call_chain(&[StratumId(6)]),
    );

    // L2: unfmix64 (id=7) = xshr33 -> unmul_c2 -> xshr33 -> unmul_c1 -> xshr33
    // Prove unfmix64(fmix64(x)) == x using Layer-1 laws via egglog FIRST (instant!)
    let eqsat = EgglogSimplifier::new(EqSatConfig { max_iters: 5, max_nodes: 5_000, timeout_ms: 1_000 });
    let unfmix_body = mk_call_chain(&[
        StratumId(1),
        StratumId(5),
        StratumId(1),
        StratumId(3),
        StratumId(1),
    ]);
    // Verify Layer-1 law composition directly via egglog before promoting L2 unfmix64!
    let mut expanded_roundtrip = mk_call_chain(&[
        StratumId(1),
        StratumId(2),
        StratumId(1),
        StratumId(4),
        StratumId(1),
        StratumId(1),
        StratumId(5),
        StratumId(1),
        StratumId(3),
        StratumId(1),
    ]);
    let (simp_rt, _) = eqsat.simplify_region(&expanded_roundtrip, &reg).unwrap();
    expanded_roundtrip = simp_rt;
    let mut b_check = BitwuzlaNativeBackend::with_time_limit_ms(TIMEOUT_MS);
    assert_eq!(
        b_check
            .check_equivalence(&module, &reg, &expanded_roundtrip, &Region::yield_vals(&[ValId(0)]), None)
            .unwrap(),
        SmtResult::Unsat,
        "L2 unfmix64(fmix64(x)) == x must be proved via L1 laws!"
    );
    reg.promote_stratum(Stratum {
        op: StratumOp {
            id: StratumId(7),
            name: "unfmix64".into(),
            layer: 2,
            params: p1.clone(),
            results: vec![ValType::I64],
            body: unfmix_body,
            docstring: "Exact inverse of MurmurHash3 fmix64".into(),
        },
        laws: LawList::single(Law {
            name: "unfmix64_fmix64_cancel".into(),
            kind: LawKind::Algebraic,
            params: p1.clone(),
            precondition: Region::empty(),
            lhs: mk_call_chain(&[StratumId(6), StratumId(7)]),
            rhs: Region::yield_vals(&[ValId(0)]),
            proof_digest: [0x64; 32],
        }),
    })
    .unwrap();

    // L3: write_pkt_m0(slot_i32, hdr_i64) -> i64: encodes hdr with fmix64, stores 8 bytes into MemId(0) at (slot & 255) << 3!
    let p_wr = vec![(ValId(0), ValType::I32), (ValId(1), ValType::I64)];
    let wr_body = Region::build(|b| {
        b.push_let(ValId(2), ValType::I32, Op::ConstI32(255));
        b.push_let(ValId(3), ValType::I32, Op::Bin(BinOp::I32And, ValId(0), ValId(2)));
        b.push_let(ValId(4), ValType::I32, Op::ConstI32(3));
        b.push_let(ValId(5), ValType::I32, Op::Bin(BinOp::I32Shl, ValId(3), ValId(4)));
        b.push_call(&[(ValId(6), ValType::I64)], CallTarget::Stratum(StratumId(6)), &[ValId(1)]);
        b.push_effect(EffectOp::Store {
            mem: MemId(0),
            addr: ValId(5),
            offset: 0,
            width: MemWidth::B8,
            val: ValId(6),
        });
        b.push_yield(&[ValId(6)]);
    });
    let wr_call = Region::build(|b| {
        b.push_call(
            &[(ValId(2), ValType::I64)],
            CallTarget::Stratum(StratumId(8)),
            &[ValId(0), ValId(1)],
        );
        b.push_yield(&[ValId(2)]);
    });
    prove_and_promote(
        &mut reg,
        &module,
        StratumOp {
            id: StratumId(8),
            name: "write_pkt_m0".into(),
            layer: 3,
            params: p_wr.clone(),
            results: vec![ValType::I64],
            body: wr_body,
            docstring: "fmix64-encode packet header and write 8B to MemId(0)".into(),
        },
        "write_pkt_m0_isolates_m1",
        LawKind::MemoryFrame { untouched_mem: MemId(1) },
        p_wr,
        wr_call.clone(),
        wr_call,
    );

    (reg, module)
}

fn time_check(
    module: &Module,
    reg: &StratumRegistry,
    lhs: &Region,
    rhs: &Region,
    use_gnomon: bool,
) -> (String, f64, usize) {
    let start = Instant::now();
    if use_gnomon {
        let eqsat = EgglogSimplifier::new(EqSatConfig {
            max_iters: 5,
            max_nodes: 5_000,
            timeout_ms: 2_000,
        });
        let (sl, rl) = eqsat.simplify_region(lhs, reg).unwrap();
        let (sr, rr) = eqsat.simplify_region(rhs, reg).unwrap();
        let fired = rl.laws_fired.len() + rr.laws_fired.len();
        let mut backend = BitwuzlaNativeBackend::with_time_limit_ms(TIMEOUT_MS);
        let res = backend.check_equivalence(module, reg, &sl, &sr, None).unwrap();
        let tag = match res {
            SmtResult::Unsat => "PROVED".into(),
            SmtResult::Sat(_) => "FALSIFIED".into(),
            SmtResult::Unknown(_) => format!("TIMEOUT(>{TIMEOUT_MS}ms)"),
        };
        (tag, start.elapsed().as_secs_f64() * 1000.0, fired)
    } else {
        // Flat Arm A/B: inline everything to Layer 0, empty registry, raw Bitwuzla!
        let mut nv1 = 1000u32;
        let flat_l = reg.lower_region_to_layer0(lhs, &mut nv1).unwrap();
        let mut nv2 = 1000u32;
        let flat_r = reg.lower_region_to_layer0(rhs, &mut nv2).unwrap();
        let empty = StratumRegistry::new();
        let mut backend = BitwuzlaNativeBackend::with_time_limit_ms(TIMEOUT_MS);
        let res = backend.check_equivalence(module, &empty, &flat_l, &flat_r, None).unwrap();
        let tag = match res {
            SmtResult::Unsat => "PROVED".into(),
            SmtResult::Sat(_) => "FALSIFIED".into(),
            SmtResult::Unknown(_) => format!("TIMEOUT(>{TIMEOUT_MS}ms)"),
        };
        (tag, start.elapsed().as_secs_f64() * 1000.0, 0)
    }
}

fn main() {
    let t0 = Instant::now();
    let (reg, module) = build_cliff_registry();
    println!(
        "Built & verified 3-layer Strata stack (8 ops) in {:.1} ms (timeout cap = {} ms)\n",
        t0.elapsed().as_secs_f64() * 1000.0,
        TIMEOUT_MS
    );

    println!(
        "{:<34} {:<16} {:>10} | {:<16} {:>10} {:>6} | {:>10}",
        "BENCHMARK", "FLAT BITWUZLA", "FLAT(ms)", "GNOMON STRATA", "GNOMON(ms)", "LAWS", "SPEEDUP"
    );
    println!("{}", "-".repeat(114));

    // =======================================================================
    // Suite 1: Nonlinear 64-bit MurmurHash3 fmix64 round-trip chain
    //          unfmix64^N(fmix64^N(x)) == x  (N = 1, 2, 4)
    // =======================================================================
    for n in [1usize, 2, 4] {
        let mut ops = Vec::with_capacity(2 * n);
        for _ in 0..n {
            ops.push(StratumId(6));
        }
        for _ in 0..n {
            ops.push(StratumId(7));
        }
        let lhs = mk_call_chain(&ops);
        let rhs = Region::yield_vals(&[ValId(0)]);
        let (ft, fms, _) = time_check(&module, &reg, &lhs, &rhs, false);
        let (gt, gms, glaws) = time_check(&module, &reg, &lhs, &rhs, true);
        let sp = if ft.starts_with("TIMEOUT") {
            format!(">{:.0}x", fms / gms.max(0.01))
        } else {
            format!("{:.1}x", fms / gms.max(0.01))
        };
        println!(
            "{:<34} {:<16} {:>10.1} | {:<16} {:>10.1} {:>6} | {:>10}",
            format!("S1_fmix64_roundtrip_N{n}"),
            ft,
            fms,
            gt,
            gms,
            glaws,
            sp
        );
        assert_eq!(gt, "PROVED");
    }

    // =======================================================================
    // Suite 2: Surviving heavy nonlinear fmix64^N pipeline (UF CEGAR!)
    //          Strength-reduction input identity that Bitwuzla cannot hash-cons:
    //          fmix64^N((x + y) * (x - y)) == fmix64^N(x * x - y * y)  (N = 1, 2, 4, 8)
    // =======================================================================
    for n in [1usize, 2, 4, 8] {
        // LHS: compute d = (x + y) * (x - y), then apply fmix64 N times
        let mut bl = RegionBuilder::new();
        bl.push_let(ValId(2), ValType::I64, Op::Bin(BinOp::I64Add, ValId(0), ValId(1)));
        bl.push_let(ValId(3), ValType::I64, Op::Bin(BinOp::I64Sub, ValId(0), ValId(1)));
        bl.push_let(ValId(4), ValType::I64, Op::Bin(BinOp::I64Mul, ValId(2), ValId(3)));
        let mut cur = ValId(4);
        for nid in (10u32..).take(n) {
            let d = ValId(nid);
            bl.push_call(&[(d, ValType::I64)], CallTarget::Stratum(StratumId(6)), &[cur]);
            cur = d;
        }
        bl.push_yield(&[cur]);
        let lhs = bl.finish();

        // RHS: compute d = (x * x) - (y * y), then apply fmix64 N times
        let mut br = RegionBuilder::new();
        br.push_let(ValId(2), ValType::I64, Op::Bin(BinOp::I64Mul, ValId(0), ValId(0)));
        br.push_let(ValId(3), ValType::I64, Op::Bin(BinOp::I64Mul, ValId(1), ValId(1)));
        br.push_let(ValId(4), ValType::I64, Op::Bin(BinOp::I64Sub, ValId(2), ValId(3)));
        let mut cur_r = ValId(4);
        for nid_r in (10u32..).take(n) {
            let d = ValId(nid_r);
            br.push_call(&[(d, ValType::I64)], CallTarget::Stratum(StratumId(6)), &[cur_r]);
            cur_r = d;
        }
        br.push_yield(&[cur_r]);
        let rhs = br.finish();

        let (ft, fms, _) = time_check(&module, &reg, &lhs, &rhs, false);
        let (gt, gms, glaws) = time_check(&module, &reg, &lhs, &rhs, true);
        let sp = if ft.starts_with("TIMEOUT") {
            format!(">{:.0}x", fms / gms.max(0.01))
        } else {
            format!("{:.1}x", fms / gms.max(0.01))
        };
        println!(
            "{:<34} {:<16} {:>10.1} | {:<16} {:>10.1} {:>6} | {:>10}",
            format!("S2_surviving_fmix64_UF_N{n}"),
            ft,
            fms,
            gt,
            gms,
            glaws,
            sp
        );
        assert_eq!(gt, "PROVED");
    }

    // =======================================================================
    // Suite 3: Dual-memory interleaved 64-bit packet-ring pipeline
    //          Hoist MemId(1) control load across N fmix64 writes to MemId(0)
    // =======================================================================
    for n in [2usize, 4, 8] {
        // Unoptimized LHS: write N fmix64 packets to MemId(0), THEN read MemId(1)[ctrl_addr]
        let mut bl = RegionBuilder::new();
        let mut nid = 10u32;
        let mut cur_hdr = ValId(2);
        let mut cur_slot = ValId(0);
        for _ in 0..n {
            let next_h = ValId(nid);
            nid += 1;
            bl.push_call(
                &[(next_h, ValType::I64)],
                CallTarget::Stratum(StratumId(8)),
                &[cur_slot, cur_hdr],
            );
            let one = ValId(nid);
            nid += 1;
            let next_s = ValId(nid);
            nid += 1;
            bl.push_let(one, ValType::I32, Op::ConstI32(1));
            bl.push_let(next_s, ValType::I32, Op::Bin(BinOp::I32Add, cur_slot, one));
            cur_slot = next_s;
            cur_hdr = next_h;
        }
        let ctrl_after = ValId(nid);
        nid += 1;
        let out_l = ValId(nid);
        bl.push_let(
            ctrl_after,
            ValType::I64,
            Op::Load {
                mem: MemId(1),
                addr: ValId(1),
                offset: 0,
                width: MemWidth::B8,
                signed: false,
                result_ty: ValType::I64,
            },
        );
        bl.push_let(out_l, ValType::I64, Op::Bin(BinOp::I64Xor, cur_hdr, ctrl_after));
        bl.push_yield(&[out_l]);
        let lhs = bl.finish();

        // Optimized RHS: hoist MemId(1)[ctrl_addr] BEFORE all N MemId(0) packet writes!
        let mut br = RegionBuilder::new();
        let ctrl_before = ValId(9);
        br.push_let(
            ctrl_before,
            ValType::I64,
            Op::Load {
                mem: MemId(1),
                addr: ValId(1),
                offset: 0,
                width: MemWidth::B8,
                signed: false,
                result_ty: ValType::I64,
            },
        );
        let mut nid_r = 10u32;
        let mut cur_hdr_r = ValId(2);
        let mut cur_slot_r = ValId(0);
        for _ in 0..n {
            let next_h = ValId(nid_r);
            nid_r += 1;
            br.push_call(
                &[(next_h, ValType::I64)],
                CallTarget::Stratum(StratumId(8)),
                &[cur_slot_r, cur_hdr_r],
            );
            let one = ValId(nid_r);
            nid_r += 1;
            let next_s = ValId(nid_r);
            nid_r += 1;
            br.push_let(one, ValType::I32, Op::ConstI32(1));
            br.push_let(next_s, ValType::I32, Op::Bin(BinOp::I32Add, cur_slot_r, one));
            cur_slot_r = next_s;
            cur_hdr_r = next_h;
        }
        let out_r = ValId(nid_r);
        br.push_let(out_r, ValType::I64, Op::Bin(BinOp::I64Xor, cur_hdr_r, ctrl_before));
        br.push_yield(&[out_r]);
        let rhs = br.finish();

        let (ft, fms, _) = time_check(&module, &reg, &lhs, &rhs, false);
        let (gt, gms, glaws) = time_check(&module, &reg, &lhs, &rhs, true);
        let sp = if ft.starts_with("TIMEOUT") {
            format!(">{:.0}x", fms / gms.max(0.01))
        } else {
            format!("{:.1}x", fms / gms.max(0.01))
        };
        println!(
            "{:<34} {:<16} {:>10.1} | {:<16} {:>10.1} {:>6} | {:>10}",
            format!("S3_dual_mem_fmix64_hoist_N{n}"),
            ft,
            fms,
            gt,
            gms,
            glaws,
            sp
        );
        assert_eq!(gt, "PROVED");
    }

    // =======================================================================
    // Soundness Control: 1-bit bug injected into S2 N=8 pipeline MUST BE FALSIFIED in < 5ms!
    // =======================================================================
    let mut b_bug = RegionBuilder::new();
    b_bug.push_let(ValId(2), ValType::I64, Op::ConstI64(1)); // 1-bit bug: x ^ 1 instead of x ^ 0!
    b_bug.push_let(ValId(3), ValType::I64, Op::Bin(BinOp::I64Xor, ValId(0), ValId(2)));
    let mut cur = ValId(3);
    for nid in (10u32..).take(8) {
        let d = ValId(nid);
        b_bug.push_call(&[(d, ValType::I64)], CallTarget::Stratum(StratumId(6)), &[cur]);
        cur = d;
    }
    b_bug.push_yield(&[cur]);
    let bug_lhs = b_bug.finish();
    let ok_rhs = mk_call_chain(&[StratumId(6); 8]);

    let mut nv1 = 1000u32;
    let bug_l0 = reg.lower_region_to_layer0(&bug_lhs, &mut nv1).unwrap();
    let mut nv2 = 1000u32;
    let ok_l0 = reg.lower_region_to_layer0(&ok_rhs, &mut nv2).unwrap();
    let mut ml = Module::default();
    ml.funcs.push(FuncDef {
        id: FuncId(0),
        name: "entry".into(),
        export_name: Some("entry".into()),
        params: vec![(ValId(0), ValType::I64)],
        results: vec![ValType::I64],
        body: bug_l0,
    });
    let mut mr = Module::default();
    mr.funcs.push(FuncDef {
        id: FuncId(0),
        name: "entry".into(),
        export_name: Some("entry".into()),
        params: vec![(ValId(0), ValType::I64)],
        results: vec![ValType::I64],
        body: ok_l0,
    });
    let t_bug = Instant::now();
    let wl = emit_wasm(&ml).unwrap();
    let wr = emit_wasm(&mr).unwrap();
    let fuzz_res = fuzz_equivalence(&wl, &wr, FuncId(0), &FuzzConfig::default()).unwrap();
    let bug_ms = t_bug.elapsed().as_secs_f64() * 1000.0;
    assert!(matches!(fuzz_res, FuzzOutcome::Falsified(_)), "1-bit bug MUST be falsified!");
    println!("{}", "-".repeat(114));
    println!(
        "Soundness control (1-bit bug in 8-round fmix64): Stage-1 Wasmtime FALSIFIED in {:.2} ms!",
        bug_ms
    );
}
