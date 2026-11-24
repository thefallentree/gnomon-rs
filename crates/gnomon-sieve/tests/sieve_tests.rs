use gnomon_kernel::{
    BinOp, CallTarget, EffectOp, FuncDef, FuncId, GlobalDef, GlobalId, HeapState, HostCallId,
    HostContract, Law, LawKind, LawList, MemId, MemWidth, MemoryDef, Module, OffsetRange, Op,
    Region, RegionBuilder, RegionList, RegionNode, SliceBound, Stratum, StratumId, StratumOp,
    StratumRegistry, TrapCode, UnOp, Val, ValId, ValType, VcKind, VcObligation, WASM_PAGE_SIZE,
    eval_region, split_invariant_loop,
};
use gnomon_sieve::{
    BitwuzlaNativeBackend, BitwuzlaPipeBackend, ContractSpec, EgglogSimplifier, EqSatConfig,
    SieveError, SmtBackend, SmtResult,
};

fn mod_with_mems(mems: &[(u16, u32, Option<u32>)]) -> Module {
    Module {
        memories: mems
            .iter()
            .map(|&(id, min_pages, max_pages)| MemoryDef {
                id: MemId(id),
                min_pages,
                max_pages,
                init_data: vec![],
            })
            .collect(),
        ..Module::default()
    }
}

fn with_both_backends(mut f: impl FnMut(&mut dyn SmtBackend, &str)) {
    let mut native = BitwuzlaNativeBackend::new();
    f(&mut native, "native");

    let mut pipe = BitwuzlaPipeBackend::new().expect("spawn bitwuzla pipe backend");
    f(&mut pipe, "pipe");
    assert!(pipe.query_count() >= 1);
}

#[test]
fn test_algebraic_equivalences_both_backends() {
    let module = Module::default();
    let reg = StratumRegistry::new();

    // 1. (a + b) * 2 == (a << 1) + (b << 1)
    let lhs = Region::build(|b| {
        b.push_let(ValId(2), ValType::I32, Op::Bin(BinOp::I32Add, ValId(0), ValId(1)));
        b.push_let(ValId(3), ValType::I32, Op::ConstI32(2));
        b.push_let(ValId(4), ValType::I32, Op::Bin(BinOp::I32Mul, ValId(2), ValId(3)));
        b.push_yield(&[ValId(4)]);
    });
    let rhs = Region::build(|b| {
        b.push_let(ValId(10), ValType::I32, Op::ConstI32(1));
        b.push_let(ValId(11), ValType::I32, Op::Bin(BinOp::I32Shl, ValId(0), ValId(10)));
        b.push_let(ValId(12), ValType::I32, Op::Bin(BinOp::I32Shl, ValId(1), ValId(10)));
        b.push_let(ValId(13), ValType::I32, Op::Bin(BinOp::I32Add, ValId(11), ValId(12)));
        b.push_yield(&[ValId(13)]);
    });

    // 2. Masked shift & rotate identities: rotl(x, 35) == rotl(x, 3) and (x << 33) == (x << 1)
    let rot_lhs = Region::build(|b| {
        b.push_let(ValId(1), ValType::I64, Op::ConstI64(67));
        b.push_let(ValId(2), ValType::I64, Op::Bin(BinOp::I64Rotl, ValId(0), ValId(1)));
        b.push_let(ValId(3), ValType::I64, Op::ConstI64(65));
        b.push_let(ValId(4), ValType::I64, Op::Bin(BinOp::I64Shl, ValId(2), ValId(3)));
        b.push_yield(&[ValId(4)]);
    });
    let rot_rhs = Region::build(|b| {
        b.push_let(ValId(1), ValType::I64, Op::ConstI64(3));
        b.push_let(ValId(2), ValType::I64, Op::Bin(BinOp::I64Rotl, ValId(0), ValId(1)));
        b.push_let(ValId(3), ValType::I64, Op::ConstI64(1));
        b.push_let(ValId(4), ValType::I64, Op::Bin(BinOp::I64Shl, ValId(2), ValId(3)));
        b.push_yield(&[ValId(4)]);
    });

    // 3. rem_s(x, -1) == 0 with NO trap (even when x == i32::MIN!)
    let rem_lhs = Region::build(|b| {
        b.push_let(ValId(1), ValType::I32, Op::ConstI32(-1));
        b.push_let(ValId(2), ValType::I32, Op::Bin(BinOp::I32RemS, ValId(0), ValId(1)));
        b.push_yield(&[ValId(2)]);
    });
    let rem_rhs = Region::build(|b| {
        b.push_let(ValId(1), ValType::I32, Op::ConstI32(0));
        b.push_yield(&[ValId(1)]);
    });

    with_both_backends(|backend, name| {
        assert_eq!(
            backend.check_equivalence(&module, &reg, &lhs, &rhs, None).unwrap(),
            SmtResult::Unsat,
            "{name}: algebraic equivalence failed"
        );
        assert_eq!(
            backend.check_equivalence(&module, &reg, &rot_lhs, &rot_rhs, None).unwrap(),
            SmtResult::Unsat,
            "{name}: 64-bit rotate/shift equivalence failed"
        );
        assert_eq!(
            backend.check_equivalence(&module, &reg, &rem_lhs, &rem_rhs, None).unwrap(),
            SmtResult::Unsat,
            "{name}: rem_s(x, -1) == 0 equivalence failed"
        );
    });
}

#[test]
fn test_div_s_min_neg1_counterexample_both_backends() {
    let module = Module::default();
    let reg = StratumRegistry::new();

    // lhs = div_s(x, y), rhs = 0 - x (does NOT trap on (MIN, -1) or y == 0!)
    // Precondition: y == -1, so ONLY (MIN, -1) distinguishes lhs (IntOverflow trap) from rhs (returns MIN).
    let pre = Region::build(|b| {
        b.push_let(ValId(10), ValType::I32, Op::ConstI32(-1));
        b.push_let(ValId(11), ValType::I32, Op::Bin(BinOp::I32Eq, ValId(1), ValId(10)));
        b.push_yield(&[ValId(11)]);
    });
    let lhs = Region::build(|b| {
        b.push_let(ValId(2), ValType::I32, Op::Bin(BinOp::I32DivS, ValId(0), ValId(1)));
        b.push_yield(&[ValId(2)]);
    });
    let rhs = Region::build(|b| {
        b.push_let(ValId(2), ValType::I32, Op::ConstI32(0));
        b.push_let(ValId(3), ValType::I32, Op::Bin(BinOp::I32Sub, ValId(2), ValId(0)));
        b.push_yield(&[ValId(3)]);
    });

    with_both_backends(|backend, name| {
        let res = backend
            .check_equivalence(&module, &reg, &lhs, &rhs, Some(&pre))
            .unwrap();
        match res {
            SmtResult::Sat(model) => {
                assert!(
                    model.scalar_values.contains(&(ValId(0), Val::I32(i32::MIN))),
                    "{name}: expected i32::MIN in model, got {:?}",
                    model.scalar_values
                );
                assert!(
                    model.scalar_values.contains(&(ValId(1), Val::I32(-1))),
                    "{name}: expected -1 in model, got {:?}",
                    model.scalar_values
                );
                // Double-check counterexample against reference interpreter.
                let heap = HeapState::from_module(&module, 1000).unwrap();
                assert_eq!(
                    eval_region(&module, &reg, &lhs, &model.scalar_values, heap.clone()),
                    Err(TrapCode::IntOverflow)
                );
                assert!(eval_region(&module, &reg, &rhs, &model.scalar_values, heap).is_ok());
            }
            other => panic!("{name}: expected Sat counterexample, got {other:?}"),
        }
    });
}

#[test]
fn test_signed_rem_bvsrem_not_bvsmod() {
    let module = Module::default();
    let reg = StratumRegistry::new();

    // (-7) % 3 == -1 in Wasm/bvsrem (whereas bvsmod would be +2).
    let lhs = Region::build(|b| {
        b.push_let(ValId(0), ValType::I32, Op::ConstI32(-7));
        b.push_let(ValId(1), ValType::I32, Op::ConstI32(3));
        b.push_let(ValId(2), ValType::I32, Op::Bin(BinOp::I32RemS, ValId(0), ValId(1)));
        b.push_yield(&[ValId(2)]);
    });
    let rhs = Region::build(|b| {
        b.push_let(ValId(0), ValType::I32, Op::ConstI32(-1));
        b.push_yield(&[ValId(0)]);
    });

    with_both_backends(|backend, name| {
        assert_eq!(
            backend.check_equivalence(&module, &reg, &lhs, &rhs, None).unwrap(),
            SmtResult::Unsat,
            "{name}: signed rem must match bvsrem (-1)"
        );
    });
}

#[test]
fn test_multi_memory_non_interference_and_witness() {
    let module = mod_with_mems(&[(0, 1, Some(1)), (1, 1, Some(1))]);
    let reg = StratumRegistry::new();

    // Non-interference: storing into MemId(0) at in-bounds addr does not change Load from MemId(1).
    let pre = Region::build(|b| {
        b.push_let(ValId(10), ValType::I32, Op::ConstI32(65_532));
        b.push_let(ValId(11), ValType::I32, Op::Bin(BinOp::I32LeU, ValId(0), ValId(10)));
        b.push_yield(&[ValId(11)]);
    });
    let lhs = Region::build(|b| {
        b.push_let(ValId(5), ValType::I32, Op::ConstI32(0x1234_5678));
        b.push_effect(EffectOp::Store {
            mem: MemId(0),
            addr: ValId(0),
            offset: 0,
            width: MemWidth::B4,
            val: ValId(5),
        });
        b.push_let(ValId(6), ValType::I32, Op::Load {
                mem: MemId(1),
                addr: ValId(1),
                offset: 0,
                width: MemWidth::B4,
                signed: false,
                result_ty: ValType::I32,
            });
        b.push_yield(&[ValId(6)]);
    });
    let rhs = Region::build(|b| {
        b.push_let(ValId(5), ValType::I32, Op::ConstI32(0x1234_5678));
        b.push_effect(EffectOp::Store {
            mem: MemId(0),
            addr: ValId(0),
            offset: 0,
            width: MemWidth::B4,
            val: ValId(5),
        });
        b.push_let(ValId(6), ValType::I32, Op::Load {
                mem: MemId(1),
                addr: ValId(1),
                offset: 0,
                width: MemWidth::B4,
                signed: false,
                result_ty: ValType::I32,
            });
        b.push_yield(&[ValId(6)]);
    });

    // Also test Load(MemId(1)) BEFORE vs AFTER Store(MemId(0)) when Store(MemId(0)) is in-bounds
    // (compare returned MemId(1) load value only, while MemId(0) differs -> wait: if MemId(0) IS
    // mutated in lhs and not in rhs, check_equivalence detects MemId(0) diff! So compare two
    // different stores to MemId(0) or same store, OR check a VC that asserts Load(1) == Load(1)!).
    let same_store_diff_val_check_vc_lhs = Region::build(|b| {
        b.push_let(ValId(6), ValType::I32, Op::Load {
                mem: MemId(1),
                addr: ValId(1),
                offset: 0,
                width: MemWidth::B4,
                signed: false,
                result_ty: ValType::I32,
            });
        b.push_let(ValId(5), ValType::I32, Op::ConstI32(0x1234_5678));
        b.push_effect(EffectOp::Store {
            mem: MemId(0),
            addr: ValId(0),
            offset: 0,
            width: MemWidth::B4,
            val: ValId(5),
        });
        b.push_let(ValId(7), ValType::I32, Op::Load {
                mem: MemId(1),
                addr: ValId(1),
                offset: 0,
                width: MemWidth::B4,
                signed: false,
                result_ty: ValType::I32,
            });
        b.push_let(ValId(8), ValType::I32, Op::Bin(BinOp::I32Eq, ValId(6), ValId(7)));
        b.push_yield(&[ValId(8)]);
    });
    let always_true = Region::build(|b| {
        b.push_let(ValId(6), ValType::I32, Op::ConstI32(1));
        b.push_yield(&[ValId(6)]);
    });
    let pre_both_in_bounds = Region::build(|b| {
        b.push_let(ValId(10), ValType::I32, Op::ConstI32(65_532));
        b.push_let(ValId(11), ValType::I32, Op::Bin(BinOp::I32LeU, ValId(0), ValId(10)));
        b.push_let(ValId(12), ValType::I32, Op::Bin(BinOp::I32LeU, ValId(1), ValId(10)));
        b.push_let(ValId(13), ValType::I32, Op::Bin(BinOp::I32And, ValId(11), ValId(12)));
        b.push_yield(&[ValId(13)]);
    });

    // Interference witness when BOTH write different values into MemId(0) at offset 8 -> Sat with witness byte!
    let store_a = Region::build(|b| {
        b.push_let(ValId(0), ValType::I32, Op::ConstI32(8));
        b.push_let(ValId(1), ValType::I32, Op::ConstI32(0xaa));
        b.push_effect(EffectOp::Store {
            mem: MemId(0),
            addr: ValId(0),
            offset: 0,
            width: MemWidth::B1,
            val: ValId(1),
        });
        b.push_yield(&[]);
    });
    let store_b = Region::build(|b| {
        b.push_let(ValId(0), ValType::I32, Op::ConstI32(8));
        b.push_let(ValId(1), ValType::I32, Op::ConstI32(0xbb));
        b.push_effect(EffectOp::Store {
            mem: MemId(0),
            addr: ValId(0),
            offset: 0,
            width: MemWidth::B1,
            val: ValId(1),
        });
        b.push_yield(&[]);
    });

    with_both_backends(|backend, name| {
        assert_eq!(
            backend
                .check_equivalence(&module, &reg, &lhs, &rhs, Some(&pre))
                .unwrap(),
            SmtResult::Unsat,
            "{name}: multi-memory Store(0) + Load(1) equivalence failed"
        );

        let vc = gnomon_kernel::VcObligation {
            kind: gnomon_kernel::VcKind::Init,
            params: vec![(ValId(0), ValType::I32), (ValId(1), ValType::I32)],
            assumptions: gnomon_kernel::RegionList::single(pre_both_in_bounds.clone()),
            goal: same_store_diff_val_check_vc_lhs.clone(),
        };
        assert_eq!(
            backend.check_vc(&module, &reg, &vc).unwrap(),
            SmtResult::Unsat,
            "{name}: Load(1) invariant across Store(0) failed"
        );
        // Also compare same_store_diff_val_check_vc_lhs vs always_true under pre (if MemId(0) wasn't written? Wait: rhs doesn't write MemId(0) so memory differs; VC proves Load(1)==Load(1)!).
        let _ = always_true;

        match backend.check_equivalence(&module, &reg, &store_a, &store_b, None).unwrap() {
            SmtResult::Sat(model) => {
                assert!(
                    model
                        .memory_bytes
                        .iter()
                        .any(|(mid, bytes)| *mid == MemId(0) && bytes.iter().any(|(off, _)| *off == 8)),
                    "{name}: expected witness offset 8 in MemId(0), got {:?}",
                    model.memory_bytes
                );
            }
            other => panic!("{name}: expected Sat witness on MemId(0) diff, got {other:?}"),
        }
    });
}

#[test]
fn test_invariant_loop_vcs_valid_and_broken_both_backends() {
    let module = Module::default();
    let reg = StratumRegistry::new();

    // Countdown loop with exact two's-complement invariant:
    // state = (i, acc), init = (n, 0)
    // precondition: n >= 0
    // invariant: i >= 0 && acc == (n - i)   (exact in two's complement!)
    // cond: i > 0
    // fuel: (u64)(u32)i
    // body: (i - 1, acc + 1)
    // postcondition: i == 0 && acc == n
    let make_loop = |bad_inv: bool, bad_fuel: bool| {
        let n = ValId(0);
        let i = ValId(10);
        let acc = ValId(11);
        let cond = Region::build(|b| {
        b.push_let(ValId(20), ValType::I32, Op::ConstI32(0));
        b.push_let(ValId(21), ValType::I32, Op::Bin(BinOp::I32GtS, i, ValId(20)));
        b.push_yield(&[ValId(21)]);
    });
        let invariant_pred = if bad_inv {
            // Broken invariant: acc < 5 fails on preservation when acc == 4, i > 0.
            Region::build(|b| {
        b.push_let(ValId(30), ValType::I32, Op::ConstI32(5));
        b.push_let(ValId(31), ValType::I32, Op::Bin(BinOp::I32LtS, acc, ValId(30)));
        b.push_yield(&[ValId(31)]);
    })
        } else {
            Region::build(|b| {
        b.push_let(ValId(30), ValType::I32, Op::ConstI32(0));
        b.push_let(ValId(31), ValType::I32, Op::Bin(BinOp::I32GeS, i, ValId(30)));
        b.push_let(ValId(32), ValType::I32, Op::Bin(BinOp::I32Sub, n, i));
        b.push_let(ValId(33), ValType::I32, Op::Bin(BinOp::I32Eq, acc, ValId(32)));
        b.push_let(ValId(34), ValType::I32, Op::Bin(BinOp::I32And, ValId(31), ValId(33)));
        b.push_yield(&[ValId(34)]);
    })
        };
        let fuel_measure = if bad_fuel {
            Region::build(|b| {
        b.push_let(ValId(40), ValType::I64, Op::ConstI64(1));
        b.push_yield(&[ValId(40)]);
    })
        } else {
            Region::build(|b| {
        b.push_let(ValId(40), ValType::I64, Op::Un(UnOp::I64ExtendI32U, i));
        b.push_yield(&[ValId(40)]);
    })
        };
        let body = Region::build(|b| {
        b.push_let(ValId(50), ValType::I32, Op::ConstI32(1));
        b.push_let(ValId(51), ValType::I32, Op::Bin(BinOp::I32Sub, i, ValId(50)));
        b.push_let(ValId(52), ValType::I32, Op::Bin(BinOp::I32Add, acc, ValId(50)));
        b.push_yield(&[ValId(51), ValId(52)]);
    });
        Region::invariant_loop(&[ValId(0), ValId(1)], &[(i, ValType::I32), (acc, ValType::I32)], &cond, &invariant_pred, &fuel_measure, &body)
    };

    let pre = Region::build(|b| {
        b.push_let(ValId(60), ValType::I32, Op::ConstI32(0));
        b.push_let(ValId(61), ValType::I32, Op::Bin(BinOp::I32GeS, ValId(0), ValId(60)));
        b.push_let(ValId(62), ValType::I32, Op::Bin(BinOp::I32Eq, ValId(1), ValId(60)));
        b.push_let(ValId(63), ValType::I32, Op::Bin(BinOp::I32And, ValId(61), ValId(62)));
        b.push_yield(&[ValId(63)]);
    });
    let post = Region::build(|b| {
        b.push_let(ValId(70), ValType::I32, Op::ConstI32(0));
        b.push_let(ValId(71), ValType::I32, Op::Bin(BinOp::I32Eq, ValId(10), ValId(70)));
        b.push_let(ValId(72), ValType::I32, Op::Bin(BinOp::I32Eq, ValId(11), ValId(0)));
        b.push_let(ValId(73), ValType::I32, Op::Bin(BinOp::I32And, ValId(71), ValId(72)));
        b.push_yield(&[ValId(73)]);
    });

    let valid_vcs = split_invariant_loop(
        vec![(ValId(0), ValType::I32), (ValId(1), ValType::I32)],
        Some(pre.clone()),
        &make_loop(false, false),
        post.clone(),
    )
    .unwrap();
    let bad_inv_vcs = split_invariant_loop(
        vec![(ValId(0), ValType::I32), (ValId(1), ValType::I32)],
        Some(pre.clone()),
        &make_loop(true, false),
        post.clone(),
    )
    .unwrap();
    let bad_fuel_vcs = split_invariant_loop(
        vec![(ValId(0), ValType::I32), (ValId(1), ValType::I32)],
        Some(pre),
        &make_loop(false, true),
        post,
    )
    .unwrap();

    with_both_backends(|backend, name| {
        assert_eq!(backend.check_vc(&module, &reg, &valid_vcs.init).unwrap(), SmtResult::Unsat, "{name}: init");
        assert_eq!(backend.check_vc(&module, &reg, &valid_vcs.preservation).unwrap(), SmtResult::Unsat, "{name}: pres");
        assert_eq!(backend.check_vc(&module, &reg, &valid_vcs.exit).unwrap(), SmtResult::Unsat, "{name}: exit");

        assert!(
            matches!(backend.check_vc(&module, &reg, &bad_inv_vcs.preservation).unwrap(), SmtResult::Sat(_)),
            "{name}: broken invariant must be Sat"
        );
        assert!(
            matches!(backend.check_vc(&module, &reg, &bad_fuel_vcs.preservation).unwrap(), SmtResult::Sat(_)),
            "{name}: non-decreasing fuel must be Sat"
        );
    });
}

#[test]
fn test_bit_ops_mem_bounds_copy_fill_grow_loop_control_flow() {
    let mut module = mod_with_mems(&[(0, 1, Some(2))]);
    module.globals.push(GlobalDef { id: GlobalId(0), ty: ValType::I32, mutable: true, init: Val::I32(0) });
    module.globals.push(GlobalDef { id: GlobalId(1), ty: ValType::I32, mutable: false, init: Val::I32(7) });
    let reg = StratumRegistry::new();

    // Test effective address BV64 overflow check: u32::MAX + offset 1 must trap OutOfBoundsMem!
    let oob_load = Region::build(|b| {
        b.push_let(ValId(0), ValType::I32, Op::ConstI32(-1));
        b.push_let(ValId(1), ValType::I32, Op::Load {
                mem: MemId(0),
                addr: ValId(0),
                offset: 1,
                width: MemWidth::B1,
                signed: false,
                result_ty: ValType::I32,
            });
        b.push_yield(&[ValId(1)]);
    });
    let explicit_oob_trap = Region::build(|b| {
        b.push_effect(EffectOp::Trap(TrapCode::OutOfBoundsMem));
        b.push_let(ValId(0), ValType::I32, Op::ConstI32(0));
        b.push_yield(&[ValId(0)]);
    });

    // Test MemoryGrow zero-initialization + MemorySize + GlobalGet/GlobalSet
    // Precondition: initial MemorySize(0) == 1 page so growing by 1 allocates page 1 as all zeros!
    let pre_size_1 = Region::build(|b| {
        b.push_let(ValId(10), ValType::I32, Op::MemorySize(MemId(0)));
        b.push_let(ValId(11), ValType::I32, Op::ConstI32(1));
        b.push_let(ValId(12), ValType::I32, Op::Bin(BinOp::I32Eq, ValId(10), ValId(11)));
        b.push_yield(&[ValId(12)]);
    });
    let grow_and_read = Region::build(|b| {
        b.push_let(ValId(0), ValType::I32, Op::ConstI32(1));
        b.push_let(ValId(1), ValType::I32, Op::MemoryGrow { mem: MemId(0), delta: ValId(0) });
        b.push_let(ValId(2), ValType::I32, Op::ConstI32(WASM_PAGE_SIZE as i32 + 16));
        b.push_let(ValId(3), ValType::I32, Op::Load {
                mem: MemId(0),
                addr: ValId(2),
                offset: 0,
                width: MemWidth::B4,
                signed: false,
                result_ty: ValType::I32,
            });
        b.push_let(ValId(4), ValType::I32, Op::GlobalGet(GlobalId(1)));
        b.push_let(ValId(5), ValType::I32, Op::Bin(BinOp::I32Add, ValId(3), ValId(4)));
        b.push_yield(&[ValId(1), ValId(5)]);
    });
    let grow_expected = Region::build(|b| {
        b.push_let(ValId(0), ValType::I32, Op::ConstI32(1));
        b.push_let(ValId(1), ValType::I32, Op::MemoryGrow { mem: MemId(0), delta: ValId(0) });
        b.push_let(ValId(2), ValType::I32, Op::ConstI32(7));
        b.push_yield(&[ValId(1), ValId(2)]);
    });

    // Test BoundedLoop finite unrolling + OutOfFuel when loop continues past max_iters
    let bounded_sum = |max_iters: u32| Region::build(|b| {
        b.push_let(ValId(1), ValType::I32, Op::ConstI32(0));
        b.push_subregion(&[(ValId(10), ValType::I32)], &Region::bounded_loop(max_iters, &[ValId(0), ValId(1)], &[(ValId(2), ValType::I32), (ValId(3), ValType::I32)], &Region::build(|b| {
        b.push_let(ValId(4), ValType::I32, Op::ConstI32(0));
        b.push_let(ValId(5), ValType::I32, Op::Bin(BinOp::I32GtS, ValId(2), ValId(4)));
        b.push_subregion(&[], &Region::if_else(ValId(5), &Region::build(|b| {
        b.push_let(ValId(6), ValType::I32, Op::Bin(BinOp::I32Add, ValId(3), ValId(2)));
        b.push_let(ValId(7), ValType::I32, Op::ConstI32(1));
        b.push_let(ValId(8), ValType::I32, Op::Bin(BinOp::I32Sub, ValId(2), ValId(7)));
        b.push_continue(1, None, &[ValId(8), ValId(6)]);
    }), &Region::empty(), &[]));
        b.push_yield(&[ValId(3)]);
    })));
        b.push_yield(&[ValId(10)]);
    });
    let pre_n_3 = Region::build(|b| {
        b.push_let(ValId(20), ValType::I32, Op::ConstI32(3));
        b.push_let(ValId(21), ValType::I32, Op::Bin(BinOp::I32Eq, ValId(0), ValId(20)));
        b.push_yield(&[ValId(21)]);
    });
    let const_6 = Region::build(|b| {
        b.push_let(ValId(1), ValType::I32, Op::ConstI32(6));
        b.push_yield(&[ValId(1)]);
    });
    let trap_fuel = Region::build(|b| {
        b.push_effect(EffectOp::Trap(TrapCode::OutOfFuel));
        b.push_let(ValId(1), ValType::I32, Op::ConstI32(0));
        b.push_yield(&[ValId(1)]);
    });

    // Test clz / ctz / popcnt / sign-extend
    let unop_lhs = Region::build(|b| {
        b.push_let(ValId(0), ValType::I32, Op::ConstI32(0x00ff_0010u32 as i32));
        b.push_let(ValId(1), ValType::I32, Op::Un(UnOp::I32Clz, ValId(0)));
        b.push_let(ValId(2), ValType::I32, Op::Un(UnOp::I32Ctz, ValId(0)));
        b.push_let(ValId(3), ValType::I32, Op::Un(UnOp::I32Popcnt, ValId(0)));
        b.push_let(ValId(4), ValType::I32, Op::Un(UnOp::I32Extend8S, ValId(0)));
        b.push_yield(&[ValId(1), ValId(2), ValId(3), ValId(4)]);
    });
    let unop_rhs = Region::build(|b| {
        b.push_let(ValId(1), ValType::I32, Op::ConstI32(8));
        b.push_let(ValId(2), ValType::I32, Op::ConstI32(4));
        b.push_let(ValId(3), ValType::I32, Op::ConstI32(9));
        b.push_let(ValId(4), ValType::I32, Op::ConstI32(0x10));
        b.push_yield(&[ValId(1), ValId(2), ValId(3), ValId(4)]);
    });

    // Overlapping intra-memory MemoryCopy & MemoryFill
    let mem_copy_lhs = Region::build(|b| {
        b.push_let(ValId(0), ValType::I32, Op::ConstI32(0));
        b.push_let(ValId(1), ValType::I32, Op::ConstI32(0x1122_3344));
        b.push_effect(EffectOp::Store { mem: MemId(0), addr: ValId(0), offset: 0, width: MemWidth::B4, val: ValId(1) });
        b.push_let(ValId(2), ValType::I32, Op::ConstI32(2));
        b.push_let(ValId(3), ValType::I32, Op::ConstI32(4));
        b.push_effect(EffectOp::MemoryCopy { dst_mem: MemId(0), src_mem: MemId(0), dst: ValId(2), src: ValId(0), len: ValId(3) });
        b.push_let(ValId(4), ValType::I32, Op::Load { mem: MemId(0), addr: ValId(2), offset: 0, width: MemWidth::B4, signed: false, result_ty: ValType::I32 });
        b.push_effect(EffectOp::MemoryFill { mem: MemId(0), dst: ValId(0), val: ValId(0), len: ValId(3) });
        b.push_effect(EffectOp::MemoryFill { mem: MemId(0), dst: ValId(2), val: ValId(0), len: ValId(3) });
        b.push_yield(&[ValId(4)]);
    });
    let mem_copy_rhs = Region::build(|b| {
        b.push_let(ValId(0), ValType::I32, Op::ConstI32(0));
        b.push_let(ValId(1), ValType::I32, Op::ConstI32(6));
        b.push_effect(EffectOp::MemoryFill { mem: MemId(0), dst: ValId(0), val: ValId(0), len: ValId(1) });
        b.push_let(ValId(2), ValType::I32, Op::ConstI32(0x1122_3344));
        b.push_yield(&[ValId(2)]);
    });

    with_both_backends(|backend, name| {
        assert_eq!(
            backend.check_equivalence(&module, &reg, &oob_load, &explicit_oob_trap, None).unwrap(),
            SmtResult::Unsat,
            "{name}: u32::MAX+1 BV64 bounds check failed"
        );
        assert_eq!(
            backend.check_equivalence(&module, &reg, &grow_and_read, &grow_expected, Some(&pre_size_1)).unwrap(),
            SmtResult::Unsat,
            "{name}: MemoryGrow zero-init check failed"
        );
        assert_eq!(
            backend.check_equivalence(&module, &reg, &bounded_sum(5), &const_6, Some(&pre_n_3)).unwrap(),
            SmtResult::Unsat,
            "{name}: BoundedLoop exact sum failed"
        );
        assert_eq!(
            backend.check_equivalence(&module, &reg, &bounded_sum(3), &trap_fuel, Some(&pre_n_3)).unwrap(),
            SmtResult::Unsat,
            "{name}: BoundedLoop OutOfFuel failed"
        );
        assert_eq!(
            backend.check_equivalence(&module, &reg, &unop_lhs, &unop_rhs, None).unwrap(),
            SmtResult::Unsat,
            "{name}: clz/ctz/popcnt/extend8s failed"
        );
        assert_eq!(
            backend.check_equivalence(&module, &reg, &mem_copy_lhs, &mem_copy_rhs, None).unwrap(),
            SmtResult::Unsat,
            "{name}: MemoryCopy/MemoryFill failed"
        );
    });
}

#[test]
fn test_egglog_simplifier_rewrites_stratum_laws_and_trap_safety() {
    let module = mod_with_mems(&[(0, 1, Some(1)), (1, 1, Some(1))]);
    let mut reg = StratumRegistry::new();

    // Register a promoted Stratum with both an Algebraic law and a MemoryFrame law.
    let double_op = StratumOp {
        id: StratumId(1),
        name: "double_i32".into(),
        layer: 1,
        params: vec![(ValId(0), ValType::I32)],
        results: vec![ValType::I32],
        body: Region::build(|b| {
        b.push_let(ValId(1), ValType::I32, Op::Bin(BinOp::I32Add, ValId(0), ValId(0)));
        b.push_yield(&[ValId(1)]);
    }),
        docstring: "doubles x".into(),
    };
    let double_law = Law {
        name: "double_plus_zero".into(),
        kind: LawKind::Algebraic,
        params: vec![(ValId(0), ValType::I32)],
        precondition: Region::empty(),
        lhs: Region::build(|b| {
        b.push_call(&[(ValId(1), ValType::I32)], CallTarget::Stratum(StratumId(1)), &[ValId(0)]);
        b.push_let(ValId(2), ValType::I32, Op::ConstI32(0));
        b.push_let(ValId(3), ValType::I32, Op::Bin(BinOp::I32Add, ValId(1), ValId(2)));
        b.push_yield(&[ValId(3)]);
    }),
        rhs: Region::build(|b| {
        b.push_let(ValId(1), ValType::I32, Op::ConstI32(1));
        b.push_let(ValId(2), ValType::I32, Op::Bin(BinOp::I32Shl, ValId(0), ValId(1)));
        b.push_yield(&[ValId(2)]);
    }),
        proof_digest: [0xab; 32],
    };
    reg.register_candidate_op(double_op.clone()).unwrap();
    reg.promote_stratum(Stratum { op: double_op, laws: LawList::single(double_law) })
        .unwrap();

    // Also register a mutating Stratum on MemId(0) with a MemoryFrame law proving MemId(1) untouched.
    let poke_mem0_op = StratumOp {
        id: StratumId(2),
        name: "poke_mem0".into(),
        layer: 1,
        params: vec![(ValId(0), ValType::I32)],
        results: vec![ValType::I32],
        body: Region::build(|b| {
        b.push_effect(EffectOp::Store {
                mem: MemId(0),
                addr: ValId(0),
                offset: 0,
                width: MemWidth::B4,
                val: ValId(0),
            });
        b.push_yield(&[ValId(0)]);
    }),
        docstring: "stores x at mem0[x]".into(),
    };
    let poke_frame_law = Law {
        name: "poke_mem0_preserves_mem1".into(),
        kind: LawKind::MemoryFrame { untouched_mem: MemId(1) },
        params: vec![(ValId(0), ValType::I32)],
        precondition: Region::empty(),
        lhs: Region::build(|b| {
        b.push_call(&[(ValId(1), ValType::I32)], CallTarget::Stratum(StratumId(2)), &[ValId(0)]);
        b.push_yield(&[ValId(1)]);
    }),
        rhs: Region::build(|b| {
        b.push_call(&[(ValId(1), ValType::I32)], CallTarget::Stratum(StratumId(2)), &[ValId(0)]);
        b.push_yield(&[ValId(1)]);
    }),
        proof_digest: [0xcd; 32],
    };
    reg.register_candidate_op(poke_mem0_op.clone()).unwrap();
    reg.promote_stratum(Stratum { op: poke_mem0_op, laws: LawList::single(poke_frame_law) })
        .unwrap();

    let simplifier = EgglogSimplifier::new(EqSatConfig { max_iters: 5, max_nodes: 5_000, timeout_ms: 500 });

    // 1. Algebraic simplification + node reduction + Stratum law firing
    let expr_region = Region::build(|b| {
        b.push_let(ValId(1), ValType::I32, Op::ConstI32(0));
        b.push_let(ValId(2), ValType::I32, Op::Bin(BinOp::I32Add, ValId(0), ValId(1)));
        b.push_let(ValId(3), ValType::I32, Op::ConstI32(1));
        b.push_let(ValId(4), ValType::I32, Op::Bin(BinOp::I32Mul, ValId(2), ValId(3)));
        b.push_let(ValId(5), ValType::I32, Op::Bin(BinOp::I32Xor, ValId(4), ValId(1)));
        b.push_yield(&[ValId(5)]);
    });
    let (simp, report) = simplifier.simplify_region(&expr_region, &reg).unwrap();
    assert!(report.iters_run <= 5 && report.iters_run >= 1);
    assert!(
        report.nodes_after < report.nodes_before,
        "expected node reduction: before={}, after={}",
        report.nodes_before,
        report.nodes_after
    );
    assert!(!report.laws_fired.is_empty(), "expected laws to fire");

    // 2. Stratum Algebraic law + MemoryFrame law + disjoint memory-frame rule firing
    let frame_region = Region::build(|b| {
        b.push_let(ValId(2), ValType::I32, Op::Load { mem: MemId(1), addr: ValId(0), offset: 0, width: MemWidth::B4, signed: false, result_ty: ValType::I32 });
        b.push_call(&[(ValId(3), ValType::I32)], CallTarget::Stratum(StratumId(1)), &[ValId(1)]);
        b.push_let(ValId(6), ValType::I32, Op::ConstI32(0));
        b.push_let(ValId(7), ValType::I32, Op::Bin(BinOp::I32Add, ValId(3), ValId(6)));
        b.push_effect(EffectOp::Store { mem: MemId(0), addr: ValId(0), offset: 0, width: MemWidth::B4, val: ValId(7) });
        b.push_call(&[(ValId(8), ValType::I32)], CallTarget::Stratum(StratumId(2)), &[ValId(0)]);
        b.push_let(ValId(4), ValType::I32, Op::Load { mem: MemId(1), addr: ValId(0), offset: 0, width: MemWidth::B4, signed: false, result_ty: ValType::I32 });
        b.push_let(ValId(5), ValType::I32, Op::Bin(BinOp::I32Sub, ValId(2), ValId(4)));
        b.push_yield(&[ValId(5)]);
    });
    let (frame_simp, frame_report) = simplifier.simplify_region(&frame_region, &reg).unwrap();
    assert!(
        frame_report.laws_fired.iter().any(|l| l == "disjoint-mem-load-store"),
        "expected disjoint-mem-load-store to fire, got {:?}",
        frame_report.laws_fired
    );
    assert!(
        frame_report.laws_fired.iter().any(|l| l == "poke_mem0_preserves_mem1"),
        "expected Stratum MemoryFrame law to fire, got {:?}",
        frame_report.laws_fired
    );
    assert!(
        frame_report.laws_fired.iter().any(|l| l == "double_plus_zero"),
        "expected Stratum Algebraic law to fire, got {:?}",
        frame_report.laws_fired
    );

    // 3. Trap preservation: div_s(MIN, -1), div_s(x, y) followed by v - v, Load followed by v - v!
    let div_trap_region = Region::build(|b| {
        b.push_let(ValId(0), ValType::I32, Op::ConstI32(i32::MIN));
        b.push_let(ValId(1), ValType::I32, Op::ConstI32(-1));
        b.push_let(ValId(2), ValType::I32, Op::Bin(BinOp::I32DivS, ValId(0), ValId(1)));
        b.push_yield(&[ValId(2)]);
    });
    let (div_simp, _) = simplifier.simplify_region(&div_trap_region, &reg).unwrap();

    let dead_load_region = Region::build(|b| {
        b.push_let(ValId(1), ValType::I32, Op::Load { mem: MemId(0), addr: ValId(0), offset: 0, width: MemWidth::B4, signed: false, result_ty: ValType::I32 });
        b.push_let(ValId(2), ValType::I32, Op::Bin(BinOp::I32Sub, ValId(1), ValId(1)));
        b.push_yield(&[ValId(2)]);
    });
    let (dead_load_simp, _) = simplifier.simplify_region(&dead_load_region, &reg).unwrap();

    // Verify ALL simplified regions are semantically equivalent to originals in Bitwuzla!
    let mut backend = BitwuzlaNativeBackend::new();
    assert_eq!(backend.check_equivalence(&module, &reg, &expr_region, &simp, None).unwrap(), SmtResult::Unsat);
    assert_eq!(backend.check_equivalence(&module, &reg, &frame_region, &frame_simp, None).unwrap(), SmtResult::Unsat);
    assert_eq!(backend.check_equivalence(&module, &reg, &div_trap_region, &div_simp, None).unwrap(), SmtResult::Unsat);
    assert_eq!(backend.check_equivalence(&module, &reg, &dead_load_region, &dead_load_simp, None).unwrap(), SmtResult::Unsat);
    // Double-check div_trap_simp still traps IntOverflow!
    let heap = HeapState::from_module(&module, 1000).unwrap();
    assert_eq!(eval_region(&module, &reg, &div_simp, &[], heap), Err(TrapCode::IntOverflow));
}

#[test]
fn test_host_contract_and_func_call_smt() {
    let mut module = mod_with_mems(&[(0, 1, Some(1))]);
    module.host_contracts.push(HostContract {
        id: HostCallId(0),
        module_name: "env".into(),
        field_name: "inc".into(),
        params: vec![(ValId(0), ValType::I32)],
        results: vec![(ValId(1), ValType::I32)],
        precondition: Region::build(|b| {
        b.push_let(ValId(10), ValType::I32, Op::ConstI32(100));
        b.push_let(ValId(11), ValType::I32, Op::Bin(BinOp::I32LtS, ValId(0), ValId(10)));
        b.push_yield(&[ValId(11)]);
    }),
        read_footprints: vec![(MemId(0), OffsetRange { base: SliceBound::Const(0), len: SliceBound::Const(4) })],
        write_footprints: vec![],
        postcondition: Region::build(|b| {
        b.push_let(ValId(12), ValType::I32, Op::ConstI32(1));
        b.push_let(ValId(13), ValType::I32, Op::Bin(BinOp::I32Add, ValId(0), ValId(12)));
        b.push_let(ValId(14), ValType::I32, Op::Bin(BinOp::I32Eq, ValId(1), ValId(13)));
        b.push_yield(&[ValId(14)]);
    }),
        sim_body: None,
    });
    let reg = StratumRegistry::new();

    let pre = Region::build(|b| {
        b.push_let(ValId(10), ValType::I32, Op::ConstI32(100));
        b.push_let(ValId(11), ValType::I32, Op::Bin(BinOp::I32LtS, ValId(0), ValId(10)));
        b.push_yield(&[ValId(11)]);
    });
    let lhs = Region::build(|b| {
        b.push_call(&[(ValId(1), ValType::I32)], CallTarget::Host(HostCallId(0)), &[ValId(0)]);
        b.push_yield(&[ValId(1)]);
    });
    let rhs = Region::build(|b| {
        b.push_let(ValId(1), ValType::I32, Op::ConstI32(1));
        b.push_let(ValId(2), ValType::I32, Op::Bin(BinOp::I32Add, ValId(0), ValId(1)));
        b.push_yield(&[ValId(2)]);
    });

    with_both_backends(|backend, name| {
        assert_eq!(
            backend.check_equivalence(&module, &reg, &lhs, &rhs, Some(&pre)).unwrap(),
            SmtResult::Unsat,
            "{name}: host contract equivalence failed"
        );
    });
}

#[test]
fn test_symbolic_memory_fill_and_persistent_pipe_reuse() {
    let module = mod_with_mems(&[(0, 1, Some(1))]);
    let reg = StratumRegistry::new();

    // Symbolic len <= 8: MemoryFill(0, 0, val, len) followed by MemoryFill(0, 0, val, len) is idempotent -> Unsat!
    let pre = Region::build(|b| {
        b.push_let(ValId(10), ValType::I32, Op::ConstI32(8));
        b.push_let(ValId(11), ValType::I32, Op::Bin(BinOp::I32LeU, ValId(1), ValId(10)));
        b.push_yield(&[ValId(11)]);
    });
    let fill_once = Region::build(|b| {
        b.push_let(ValId(2), ValType::I32, Op::ConstI32(0));
        b.push_effect(EffectOp::MemoryFill { mem: MemId(0), dst: ValId(2), val: ValId(0), len: ValId(1) });
        b.push_yield(&[]);
    });
    let fill_twice = Region::build(|b| {
        b.push_let(ValId(2), ValType::I32, Op::ConstI32(0));
        b.push_effect(EffectOp::MemoryFill { mem: MemId(0), dst: ValId(2), val: ValId(0), len: ValId(1) });
        b.push_effect(EffectOp::MemoryFill { mem: MemId(0), dst: ValId(2), val: ValId(0), len: ValId(1) });
        b.push_yield(&[]);
    });

    // Unbounded symbolic len without precondition must NEVER unsoundly return Unsat!
    let mut pipe = BitwuzlaPipeBackend::new().expect("spawn pipe");
    let mut native = BitwuzlaNativeBackend::new();

    for (backend, name) in [
        (&mut native as &mut dyn SmtBackend, "native"),
        (&mut pipe as &mut dyn SmtBackend, "pipe"),
    ] {
        assert_eq!(
            backend
                .check_equivalence(&module, &reg, &fill_once, &fill_twice, Some(&pre))
                .unwrap(),
            SmtResult::Unsat,
            "{name}: bounded symbolic MemoryFill idempotence failed"
        );
        let res_unbounded = backend
            .check_equivalence(&module, &reg, &fill_once, &fill_twice, None)
            .unwrap();
        assert!(
            matches!(res_unbounded, SmtResult::Unknown(_)),
            "{name}: unbounded symbolic MemoryFill must return Unknown, got {res_unbounded:?}"
        );
    }

    // Verify single persistent pipe child survives 20+ sequential queries cleanly.
    for _ in 0..20 {
        assert_eq!(
            pipe.check_equivalence(&module, &reg, &fill_once, &fill_twice, Some(&pre))
                .unwrap(),
            SmtResult::Unsat
        );
    }
    assert_eq!(pipe.query_count(), 22);
}

#[test]
fn test_egglog_div_rem_trap_preservation_and_caps() {
    let module = Module::default();
    let reg = StratumRegistry::new();
    let simplifier = EgglogSimplifier::new(EqSatConfig { max_iters: 10, max_nodes: 10_000, timeout_ms: 500 });

    // div_s(0, x) and div_s(x, x) and rem_u(x, x) MUST NOT drop potential DivByZero/IntOverflow traps!
    let div_zero_x = Region::build(|b| {
        b.push_let(ValId(1), ValType::I32, Op::ConstI32(0));
        b.push_let(ValId(2), ValType::I32, Op::Bin(BinOp::I32DivS, ValId(1), ValId(0)));
        b.push_yield(&[ValId(2)]);
    });
    let div_x_x = Region::build(|b| {
        b.push_let(ValId(2), ValType::I32, Op::Bin(BinOp::I32DivS, ValId(0), ValId(0)));
        b.push_yield(&[ValId(2)]);
    });
    let rem_x_x = Region::build(|b| {
        b.push_let(ValId(2), ValType::I32, Op::Bin(BinOp::I32RemU, ValId(0), ValId(0)));
        b.push_yield(&[ValId(2)]);
    });
    // div_s(x, 1) CAN be safely simplified to x!
    let div_x_one = Region::build(|b| {
        b.push_let(ValId(1), ValType::I32, Op::ConstI32(1));
        b.push_let(ValId(2), ValType::I32, Op::Bin(BinOp::I32DivS, ValId(0), ValId(1)));
        b.push_yield(&[ValId(2)]);
    });

    let mut backend = BitwuzlaNativeBackend::new();
    for region in [&div_zero_x, &div_x_x, &rem_x_x, &div_x_one] {
        let (simp, rep) = simplifier.simplify_region(region, &reg).unwrap();
        // Verify hard cap <= 5 is enforced even when config passes 10.
        assert!(rep.iters_run <= 5, "iters_run {} exceeded cap 5", rep.iters_run);
        assert_eq!(
            backend.check_equivalence(&module, &reg, region, &simp, None).unwrap(),
            SmtResult::Unsat
        );
    }
    let (simp_one, rep_one) = simplifier.simplify_region(&div_x_one, &reg).unwrap();
    assert!(rep_one.nodes_after < rep_one.nodes_before);
    assert!(rep_one.laws_fired.iter().any(|l| l == "divs-one-i32"));
    assert_eq!(backend.check_equivalence(&module, &reg, &div_x_one, &simp_one, None).unwrap(), SmtResult::Unsat);
}

#[test]
fn test_adversarial_sieve_soundness_regressions() {
    let mut module = mod_with_mems(&[(0, 1, Some(1))]);
    let mut reg = StratumRegistry::new();
    let simplifier = EgglogSimplifier::default();
    let mut backend = BitwuzlaPipeBackend::new().unwrap();

    // 1. i64.store32 (val: I64, width: B4) followed by i32.load (width: B4, result_ty: I32)
    // must NOT misfire store-load-forward-b4 into an ill-typed I64 value!
    let mixed_store_load = Region::build(|b| {
        b.push_effect(EffectOp::Store {
            mem: MemId(0),
            addr: ValId(0),
            offset: 0,
            width: MemWidth::B4,
            val: ValId(1), // ValType::I64!
        });
        b.push_let(ValId(2), ValType::I32, Op::Load {
                mem: MemId(0),
                addr: ValId(0),
                offset: 0,
                width: MemWidth::B4,
                signed: false,
                result_ty: ValType::I32,
            });
        b.push_let(ValId(3), ValType::I64, Op::ConstI64(1));
        b.push_let(ValId(4), ValType::I64, Op::Bin(BinOp::I64Add, ValId(1), ValId(3)));
        b.push_let(ValId(5), ValType::I32, Op::Un(UnOp::I32WrapI64, ValId(4)));
        b.push_let(ValId(6), ValType::I32, Op::Bin(BinOp::I32Add, ValId(2), ValId(5)));
        b.push_yield(&[ValId(6)]);
    });
    let (mixed_simp, _) = simplifier.simplify_region(&mixed_store_load, &reg).unwrap();
    assert_eq!(
        backend.check_equivalence(&module, &reg, &mixed_store_load, &mixed_simp, None).unwrap(),
        SmtResult::Unsat
    );

    // 2. Read-only Stratum that reads memory MUST NOT be CSE'd across an intervening Store!
    let load_op = StratumOp {
        id: StratumId(50),
        name: "read_m0".into(),
        layer: 1,
        params: vec![(ValId(0), ValType::I32)],
        results: vec![ValType::I32],
        body: Region::build(|b| {
        b.push_let(ValId(1), ValType::I32, Op::Load { mem: MemId(0), addr: ValId(0), offset: 0, width: MemWidth::B4, signed: false, result_ty: ValType::I32 });
        b.push_yield(&[ValId(1)]);
    }),
        docstring: String::new(),
    };
    let refl_law = Law {
        name: "refl_read_m0".into(),
        kind: LawKind::Algebraic,
        params: vec![(ValId(0), ValType::I32)],
        precondition: Region::empty(),
        lhs: Region::build(|b| {
        b.push_call(&[(ValId(1), ValType::I32)], CallTarget::Stratum(StratumId(50)), &[ValId(0)]);
        b.push_yield(&[ValId(1)]);
    }),
        rhs: Region::build(|b| {
        b.push_call(&[(ValId(1), ValType::I32)], CallTarget::Stratum(StratumId(50)), &[ValId(0)]);
        b.push_yield(&[ValId(1)]);
    }),
        proof_digest: [0x77; 32],
    };
    reg.promote_stratum(Stratum { op: load_op, laws: LawList::single(refl_law) }).unwrap();

    let stratum_across_store = Region::build(|b| {
        b.push_call(&[(ValId(2), ValType::I32)], CallTarget::Stratum(StratumId(50)), &[ValId(0)]);
        b.push_effect(EffectOp::Store { mem: MemId(0), addr: ValId(0), offset: 0, width: MemWidth::B4, val: ValId(1) });
        b.push_call(&[(ValId(3), ValType::I32)], CallTarget::Stratum(StratumId(50)), &[ValId(0)]);
        b.push_let(ValId(4), ValType::I32, Op::Bin(BinOp::I32Sub, ValId(3), ValId(2)));
        b.push_yield(&[ValId(4)]);
    });
    let (across_simp, _) = simplifier.simplify_region(&stratum_across_store, &reg).unwrap();
    assert_eq!(
        backend.check_equivalence(&module, &reg, &stratum_across_store, &across_simp, None).unwrap(),
        SmtResult::Unsat,
        "heap-reading Stratum must not be CSE'd across Store"
    );

    // 3. Multi-block IfElse must still report iters_run <= 5, and nested trap inside UnOp must be preserved!
    let multi_block = Region::if_else(ValId(0), &Region::build(|b| {
        b.push_let(ValId(2), ValType::I32, Op::Bin(BinOp::I32DivS, ValId(0), ValId(1)));
        b.push_let(ValId(3), ValType::I32, Op::Un(UnOp::I32Eqz, ValId(2)));
        b.push_let(ValId(4), ValType::I32, Op::Bin(BinOp::I32Sub, ValId(3), ValId(3)));
        b.push_yield(&[ValId(4)]);
    }), &Region::build(|b| {
        b.push_let(ValId(5), ValType::I32, Op::ConstI32(0));
        b.push_let(ValId(6), ValType::I32, Op::Bin(BinOp::I32Add, ValId(1), ValId(5)));
        b.push_yield(&[ValId(6)]);
    }), &[ValType::I32]);
    let (mb_simp, mb_rep) = simplifier.simplify_region(&multi_block, &reg).unwrap();
    assert!(mb_rep.iters_run <= 5, "multi-block iters_run {} exceeded 5", mb_rep.iters_run);
    assert_eq!(
        backend.check_equivalence(&module, &reg, &multi_block, &mb_simp, None).unwrap(),
        SmtResult::Unsat
    );

    // 4. HostContract sim_body violating write_footprints must trap HostContractViolation in SMT!
    module.host_contracts.push(HostContract {
        id: HostCallId(9),
        module_name: "env".into(),
        field_name: "rogue_sim".into(),
        params: vec![(ValId(0), ValType::I32)],
        results: vec![(ValId(1), ValType::I32)],
        precondition: Region::build(|b| {
        b.push_let(ValId(2), ValType::I32, Op::ConstI32(1));
        b.push_yield(&[ValId(2)]);
    }),
        read_footprints: vec![],
        write_footprints: vec![(MemId(0), OffsetRange { base: SliceBound::Const(0), len: SliceBound::Const(4) })],
        postcondition: Region::build(|b| {
        b.push_let(ValId(2), ValType::I32, Op::ConstI32(1));
        b.push_yield(&[ValId(2)]);
    }),
        // Writes at offset 8 (OUTSIDE write_footprints [0..4))!
        sim_body: Some(Region::build(|b| {
        b.push_let(ValId(3), ValType::I32, Op::ConstI32(8));
        b.push_let(ValId(4), ValType::I32, Op::ConstI32(0x7F));
        b.push_effect(EffectOp::Store { mem: MemId(0), addr: ValId(3), offset: 0, width: MemWidth::B1, val: ValId(4) });
        b.push_yield(&[ValId(0)]);
    })),
    });
    let call_rogue = Region::build(|b| {
        b.push_let(ValId(3), ValType::I32, Op::ConstI32(8));
        b.push_let(ValId(4), ValType::I32, Op::ConstI32(0));
        b.push_effect(EffectOp::Store { mem: MemId(0), addr: ValId(3), offset: 0, width: MemWidth::B1, val: ValId(4) });
        b.push_call(&[(ValId(1), ValType::I32)], CallTarget::Host(HostCallId(9)), &[ValId(0)]);
        b.push_yield(&[ValId(1)]);
    });
    let explicit_trap = Region::build(|b| {
        b.push_effect(EffectOp::Trap(TrapCode::HostContractViolation));
        b.push_let(ValId(1), ValType::I32, Op::Copy(ValId(0)));
        b.push_yield(&[ValId(1)]);
    });
    assert_eq!(
        backend.check_equivalence(&module, &reg, &call_rogue, &explicit_trap, None).unwrap(),
        SmtResult::Unsat
    );

    // 5. BoundedLoop with max_iters = u32::MAX (lifted Wasm loop):
    // proves bounded exit Unsat and returns Unknown when unbounded!
    let wasm_loop = Region::bounded_loop(u32::MAX, &[ValId(0)], &[(ValId(1), ValType::I32)], &Region::build(|b| {
        b.push_let(ValId(2), ValType::I32, Op::ConstI32(0));
        b.push_let(ValId(3), ValType::I32, Op::Bin(BinOp::I32Eq, ValId(1), ValId(2)));
        b.push_break(0, Some(ValId(3)), &[ValId(2)]);
        b.push_let(ValId(4), ValType::I32, Op::ConstI32(1));
        b.push_let(ValId(5), ValType::I32, Op::Bin(BinOp::I32Sub, ValId(1), ValId(4)));
        b.push_continue(0, None, &[ValId(5)]);
    }));
    let const_zero = Region::build(|b| {
        b.push_let(ValId(2), ValType::I32, Op::ConstI32(0));
        b.push_let(ValId(3), ValType::I32, Op::Bin(BinOp::I32And, ValId(0), ValId(2)));
        b.push_yield(&[ValId(3)]);
    });
    let pre_small = Region::build(|b| {
        b.push_let(ValId(2), ValType::I32, Op::ConstI32(4));
        b.push_let(ValId(3), ValType::I32, Op::Bin(BinOp::I32LeU, ValId(0), ValId(2)));
        b.push_yield(&[ValId(3)]);
    });
    assert_eq!(
        backend.check_equivalence(&module, &reg, &wasm_loop, &const_zero, Some(&pre_small)).unwrap(),
        SmtResult::Unsat
    );
    assert!(matches!(
        backend.check_equivalence(&module, &reg, &wasm_loop, &const_zero, None).unwrap(),
        SmtResult::Unknown(_)
    ));

    // 6. Read-only Stratum whose law lowers StratumCall to trapping I32DivS MUST preserve
    // traps even when its output is cancelled via `v - v -> 0` (regression for StratumCallSingle)!
    let div_stratum_op = StratumOp {
        id: StratumId(60),
        name: "checked_quot".into(),
        layer: 1,
        params: vec![(ValId(0), ValType::I32), (ValId(1), ValType::I32)],
        results: vec![ValType::I32],
        body: Region::build(|b| {
        b.push_let(ValId(2), ValType::I32, Op::Bin(BinOp::I32DivS, ValId(0), ValId(1)));
        b.push_yield(&[ValId(2)]);
    }),
        docstring: String::new(),
    };
    let div_inline_law = Law {
        name: "inline_checked_quot".into(),
        kind: LawKind::Algebraic,
        params: vec![(ValId(0), ValType::I32), (ValId(1), ValType::I32)],
        precondition: Region::empty(),
        lhs: Region::build(|b| {
        b.push_call(&[(ValId(2), ValType::I32)], CallTarget::Stratum(StratumId(60)), &[ValId(0), ValId(1)]);
        b.push_yield(&[ValId(2)]);
    }),
        rhs: Region::build(|b| {
        b.push_let(ValId(2), ValType::I32, Op::Bin(BinOp::I32DivS, ValId(0), ValId(1)));
        b.push_yield(&[ValId(2)]);
    }),
        proof_digest: [0x60; 32],
    };
    reg.promote_stratum(Stratum { op: div_stratum_op, laws: LawList::single(div_inline_law) }).unwrap();

    let stratum_div_cancel = Region::build(|b| {
        b.push_call(&[(ValId(2), ValType::I32)], CallTarget::Stratum(StratumId(60)), &[ValId(0), ValId(1)]);
        b.push_let(ValId(3), ValType::I32, Op::Bin(BinOp::I32Sub, ValId(2), ValId(2)));
        b.push_yield(&[ValId(3)]);
    });
    let (stratum_div_simp, _) = simplifier.simplify_region(&stratum_div_cancel, &reg).unwrap();
    // Evaluating simplified region on divisor x == 0 MUST still trap with DivByZero!
    let trap_res = gnomon_kernel::eval_region(
        &module,
        &reg,
        &stratum_div_simp,
        &[(ValId(0), Val::I32(42)), (ValId(1), Val::I32(0))],
        gnomon_kernel::HeapState::from_module(&module, 1024).unwrap(),
    );
    assert_eq!(trap_res, Err(TrapCode::DivByZero));
    assert_eq!(
        backend.check_equivalence(&module, &reg, &stratum_div_cancel, &stratum_div_simp, None).unwrap(),
        SmtResult::Unsat
    );
}

#[test]
fn test_uf_congruence_cegar_soundness_and_speed() {
    // Pure-total 64-bit nonlinear mixer Stratum (MurmurHash3 fmix64).
    let module = Module::default();
    let mut reg = StratumRegistry::new();
    let fmix_body = Region::build(|b| {
        b.push_let(ValId(1), ValType::I64, Op::ConstI64(33));
        b.push_let(ValId(2), ValType::I64, Op::Bin(BinOp::I64ShrU, ValId(0), ValId(1)));
        b.push_let(ValId(3), ValType::I64, Op::Bin(BinOp::I64Xor, ValId(0), ValId(2)));
        b.push_let(ValId(4), ValType::I64, Op::ConstI64(0xff51_afd7_ed55_8ccdu64 as i64));
        b.push_let(ValId(5), ValType::I64, Op::Bin(BinOp::I64Mul, ValId(3), ValId(4)));
        b.push_let(ValId(6), ValType::I64, Op::Bin(BinOp::I64ShrU, ValId(5), ValId(1)));
        b.push_let(ValId(7), ValType::I64, Op::Bin(BinOp::I64Xor, ValId(5), ValId(6)));
        b.push_let(ValId(8), ValType::I64, Op::ConstI64(0xc4ce_b9fe_1a85_ec53u64 as i64));
        b.push_let(ValId(9), ValType::I64, Op::Bin(BinOp::I64Mul, ValId(7), ValId(8)));
        b.push_let(ValId(10), ValType::I64, Op::Bin(BinOp::I64ShrU, ValId(9), ValId(1)));
        b.push_let(ValId(11), ValType::I64, Op::Bin(BinOp::I64Xor, ValId(9), ValId(10)));
        b.push_yield(&[ValId(11)]);
    });
    let fmix_call = Region::build(|b| {
        b.push_call(&[(ValId(1), ValType::I64)], CallTarget::Stratum(StratumId(70)), &[ValId(0)]);
        b.push_yield(&[ValId(1)]);
    });
    reg.promote_stratum(Stratum {
        op: StratumOp {
            id: StratumId(70),
            name: "fmix64_cegar".into(),
            layer: 1,
            params: vec![(ValId(0), ValType::I64)],
            results: vec![ValType::I64],
            body: fmix_body,
            docstring: "Nonlinear 64-bit mixer".into(),
        },
        laws: LawList::single(Law {
            name: "fmix64_refl".into(),
            kind: LawKind::Algebraic,
            params: vec![(ValId(0), ValType::I64)],
            precondition: Region::empty(),
            lhs: fmix_call.clone(),
            rhs: fmix_call,
            proof_digest: [0x70; 32],
        }),
    })
    .unwrap();

    // 1. True equivalence with nontrivial algebraic input difference:
    //    fmix64^4((x << 1) + x + y) == fmix64^4(x * 3 + y)
    let lhs = Region::build(|b| {
        b.push_let(ValId(2), ValType::I64, Op::ConstI64(1));
        b.push_let(ValId(3), ValType::I64, Op::Bin(BinOp::I64Shl, ValId(0), ValId(2)));
        b.push_let(ValId(4), ValType::I64, Op::Bin(BinOp::I64Add, ValId(3), ValId(0)));
        b.push_let(ValId(5), ValType::I64, Op::Bin(BinOp::I64Add, ValId(4), ValId(1)));
        let mut cur = ValId(5);
        for nid in 10u32..14 {
            b.push_call(&[(ValId(nid), ValType::I64)], CallTarget::Stratum(StratumId(70)), &[cur]);
            cur = ValId(nid);
        }
        b.push_yield(&[cur]);
    });
    let rhs = Region::build(|b| {
        b.push_let(ValId(2), ValType::I64, Op::ConstI64(3));
        b.push_let(ValId(3), ValType::I64, Op::Bin(BinOp::I64Mul, ValId(0), ValId(2)));
        b.push_let(ValId(4), ValType::I64, Op::Bin(BinOp::I64Add, ValId(3), ValId(1)));
        let mut cur = ValId(4);
        for nid in 10u32..14 {
            b.push_call(&[(ValId(nid), ValType::I64)], CallTarget::Stratum(StratumId(70)), &[cur]);
            cur = ValId(nid);
        }
        b.push_yield(&[cur]);
    });

    // Both native and pipe backends must prove UNSAT quickly via UF congruence CEGAR!
    let mut native = BitwuzlaNativeBackend::with_time_limit_ms(5_000);
    assert_eq!(native.check_equivalence(&module, &reg, &lhs, &rhs, None).unwrap(), SmtResult::Unsat);
    let mut pipe = BitwuzlaPipeBackend::new().unwrap();
    assert_eq!(pipe.check_equivalence(&module, &reg, &lhs, &rhs, None).unwrap(), SmtResult::Unsat);

    // 2. Soundness check: injecting a 1-bit bug (x * 3 + y + 1) MUST fall back to concrete
    //    and return a real SAT counterexample verified in gnomon-kernel!
    let buggy = Region::build(|b| {
        b.push_let(ValId(2), ValType::I64, Op::ConstI64(3));
        b.push_let(ValId(3), ValType::I64, Op::Bin(BinOp::I64Mul, ValId(0), ValId(2)));
        b.push_let(ValId(4), ValType::I64, Op::Bin(BinOp::I64Add, ValId(3), ValId(1)));
        b.push_let(ValId(5), ValType::I64, Op::ConstI64(1));
        b.push_let(ValId(6), ValType::I64, Op::Bin(BinOp::I64Add, ValId(4), ValId(5)));
        b.push_call(&[(ValId(10), ValType::I64)], CallTarget::Stratum(StratumId(70)), &[ValId(6)]);
        b.push_yield(&[ValId(10)]);
    });
    let ok_1 = Region::build(|b| {
        b.push_let(ValId(2), ValType::I64, Op::ConstI64(3));
        b.push_let(ValId(3), ValType::I64, Op::Bin(BinOp::I64Mul, ValId(0), ValId(2)));
        b.push_let(ValId(4), ValType::I64, Op::Bin(BinOp::I64Add, ValId(3), ValId(1)));
        b.push_call(&[(ValId(10), ValType::I64)], CallTarget::Stratum(StratumId(70)), &[ValId(4)]);
        b.push_yield(&[ValId(10)]);
    });
    let sat_res = native.check_equivalence(&module, &reg, &buggy, &ok_1, None).unwrap();
    assert!(matches!(sat_res, SmtResult::Sat(_)), "expected concrete SAT counterexample, got {sat_res:?}");
}

fn make_intrinsic_host(id: u32, module_name: &str, field_name: &str) -> HostContract {
    let true_pred = Region::build(|b| {
        b.push_let(ValId(0), ValType::I32, Op::ConstI32(1));
        b.push_yield(&[ValId(0)]);
    });
    HostContract {
        id: HostCallId(id),
        module_name: module_name.into(),
        field_name: field_name.into(),
        params: vec![(ValId(0), ValType::I32)],
        results: vec![],
        precondition: true_pred.clone(),
        read_footprints: vec![],
        write_footprints: vec![],
        postcondition: true_pred,
        sim_body: None,
    }
}

#[test]
fn test_contract_pure_pre_post_and_ensures_binding_both_backends() {
    let module = Module::default();
    let reg = StratumRegistry::new();

    // entry(x: i32, y: i32) -> i32 { x + y }
    let entry = FuncDef {
        id: FuncId(0),
        name: "add_pair".into(),
        export_name: Some("add_pair".into()),
        params: vec![(ValId(0), ValType::I32), (ValId(1), ValType::I32)],
        results: vec![ValType::I32],
        body: Region::build(|b| {
            b.push_let(ValId(2), ValType::I32, Op::Bin(BinOp::I32Add, ValId(0), ValId(1)));
            b.push_yield(&[ValId(2)]);
        }),
    };
    // requires(x, y): 0 <= x <= 1000 && 0 <= y <= 1000
    let req = Region::build(|b| {
        b.push_let(ValId(10), ValType::I32, Op::ConstI32(0));
        b.push_let(ValId(11), ValType::I32, Op::ConstI32(1000));
        b.push_let(ValId(12), ValType::I32, Op::Bin(BinOp::I32GeS, ValId(0), ValId(10)));
        b.push_let(ValId(13), ValType::I32, Op::Bin(BinOp::I32LeS, ValId(0), ValId(11)));
        b.push_let(ValId(14), ValType::I32, Op::Bin(BinOp::I32GeS, ValId(1), ValId(10)));
        b.push_let(ValId(15), ValType::I32, Op::Bin(BinOp::I32LeS, ValId(1), ValId(11)));
        b.push_let(ValId(16), ValType::I32, Op::Bin(BinOp::I32And, ValId(12), ValId(13)));
        b.push_let(ValId(17), ValType::I32, Op::Bin(BinOp::I32And, ValId(14), ValId(15)));
        b.push_let(ValId(18), ValType::I32, Op::Bin(BinOp::I32And, ValId(16), ValId(17)));
        b.push_yield(&[ValId(18)]);
    });
    // ensures_valid(x: ValId(0), y: ValId(1), ret: ValId(2)): ret >= x && ret <= 2000
    let ens_valid = Region::build(|b| {
        b.push_let(ValId(10), ValType::I32, Op::ConstI32(2000));
        b.push_let(ValId(11), ValType::I32, Op::Bin(BinOp::I32GeS, ValId(2), ValId(0)));
        b.push_let(ValId(12), ValType::I32, Op::Bin(BinOp::I32LeS, ValId(2), ValId(10)));
        b.push_let(ValId(13), ValType::I32, Op::Bin(BinOp::I32And, ValId(11), ValId(12)));
        b.push_yield(&[ValId(13)]);
    });
    // ensures_false(x, y, ret): ret <= 1500
    let ens_false = Region::build(|b| {
        b.push_let(ValId(10), ValType::I32, Op::ConstI32(1500));
        b.push_let(ValId(11), ValType::I32, Op::Bin(BinOp::I32LeS, ValId(2), ValId(10)));
        b.push_yield(&[ValId(11)]);
    });
    // ensures_ret_only(ret: ValId(0)): ret >= 0 && ret <= 2000
    let ens_ret_only = FuncDef {
        id: FuncId(1),
        name: "ens_ret_only".into(),
        export_name: None,
        params: vec![(ValId(0), ValType::I32)],
        results: vec![ValType::I32],
        body: Region::build(|b| {
            b.push_let(ValId(10), ValType::I32, Op::ConstI32(0));
            b.push_let(ValId(11), ValType::I32, Op::ConstI32(2000));
            b.push_let(ValId(12), ValType::I32, Op::Bin(BinOp::I32GeS, ValId(0), ValId(10)));
            b.push_let(ValId(13), ValType::I32, Op::Bin(BinOp::I32LeS, ValId(0), ValId(11)));
            b.push_let(ValId(14), ValType::I32, Op::Bin(BinOp::I32And, ValId(12), ValId(13)));
            b.push_yield(&[ValId(14)]);
        }),
    };

    with_both_backends(|backend, name| {
        let valid_spec = ContractSpec::from_func(&entry).with_requires(&req).with_ensures(&ens_valid);
        assert_eq!(
            backend.check_contract(&module, &reg, &valid_spec).unwrap(),
            SmtResult::Unsat,
            "{name}: valid pre/post contract must be UNSAT"
        );

        let ret_only_spec = ContractSpec::from_func(&entry)
            .with_requires(&req)
            .with_ensures_func(&ens_ret_only);
        assert_eq!(
            backend.check_contract(&module, &reg, &ret_only_spec).unwrap(),
            SmtResult::Unsat,
            "{name}: ret-only ensures_func must be UNSAT"
        );

        let false_spec = ContractSpec::from_func(&entry).with_requires(&req).with_ensures(&ens_false);
        match backend.check_contract(&module, &reg, &false_spec).unwrap() {
            SmtResult::Sat(model) => {
                let x = model
                    .scalar_values
                    .iter()
                    .find(|(id, _)| *id == ValId(0))
                    .unwrap()
                    .1
                    .as_i32()
                    .unwrap();
                let y = model
                    .scalar_values
                    .iter()
                    .find(|(id, _)| *id == ValId(1))
                    .unwrap()
                    .1
                    .as_i32()
                    .unwrap();
                assert!((0..=1000).contains(&x) && (0..=1000).contains(&y), "{name}: pre violated");
                assert!(x + y > 1500, "{name}: counterexample must falsify ret <= 1500, got {x}+{y}");
            }
            other => panic!("{name}: expected Sat for falsified postcondition, got {other:?}"),
        }

        // Bad ensures_params arity returns EncodingError.
        let bad_params = [(ValId(0), ValType::I32), (ValId(1), ValType::I32)];
        let mut bad_spec = ContractSpec::from_func(&entry).with_ensures(&ens_valid);
        bad_spec.ensures_params = Some(&bad_params);
        assert!(
            matches!(
                backend.check_contract(&module, &reg, &bad_spec),
                Err(SieveError::EncodingError(_))
            ),
            "{name}: mismatched ensures_params arity must error"
        );
    });
}

#[test]
fn test_contract_trap_freedom_and_allow_traps_both_backends() {
    let module = mod_with_mems(&[(0, 1, Some(1))]);
    let reg = StratumRegistry::new();

    // div_u(x, y) -> x /u y
    let div_params = [(ValId(0), ValType::I32), (ValId(1), ValType::I32)];
    let div_entry = Region::build(|b| {
        b.push_let(ValId(2), ValType::I32, Op::Bin(BinOp::I32DivU, ValId(0), ValId(1)));
        b.push_yield(&[ValId(2)]);
    });
    let y_ne_zero = Region::build(|b| {
        b.push_let(ValId(2), ValType::I32, Op::ConstI32(0));
        b.push_let(ValId(3), ValType::I32, Op::Bin(BinOp::I32Ne, ValId(1), ValId(2)));
        b.push_yield(&[ValId(3)]);
    });
    let ens_le_x = Region::build(|b| {
        b.push_let(ValId(3), ValType::I32, Op::Bin(BinOp::I32LeU, ValId(2), ValId(0)));
        b.push_yield(&[ValId(3)]);
    });
    let ens_lt_x = Region::build(|b| {
        b.push_let(ValId(3), ValType::I32, Op::Bin(BinOp::I32LtU, ValId(2), ValId(0)));
        b.push_yield(&[ValId(3)]);
    });

    // load_i32(addr) -> i32
    let load_params = [(ValId(0), ValType::I32)];
    let load_entry = Region::build(|b| {
        b.push_let(
            ValId(1),
            ValType::I32,
            Op::Load {
                mem: MemId(0),
                addr: ValId(0),
                offset: 0,
                width: MemWidth::B4,
                signed: false,
                result_ty: ValType::I32,
            },
        );
        b.push_yield(&[ValId(1)]);
    });
    let addr_in_bounds = Region::build(|b| {
        b.push_let(ValId(1), ValType::I32, Op::ConstI32((WASM_PAGE_SIZE - 4) as i32));
        b.push_let(ValId(2), ValType::I32, Op::Bin(BinOp::I32LeU, ValId(0), ValId(1)));
        b.push_yield(&[ValId(2)]);
    });

    with_both_backends(|backend, name| {
        // 1. Unguarded div_u traps on y == 0.
        let spec_div_unguarded = ContractSpec::new(&div_params, &[ValType::I32], &div_entry);
        match backend.check_contract(&module, &reg, &spec_div_unguarded).unwrap() {
            SmtResult::Sat(m) => {
                assert!(m.scalar_values.contains(&(ValId(1), Val::I32(0))), "{name}: expected y=0");
            }
            other => panic!("{name}: expected Sat for unguarded div0, got {other:?}"),
        }

        // 2. Guarded div_u is trap-free and satisfies ret <=u x.
        let spec_div_guarded = ContractSpec::new(&div_params, &[ValType::I32], &div_entry)
            .with_requires(&y_ne_zero)
            .with_ensures(&ens_le_x);
        assert_eq!(
            backend.check_contract(&module, &reg, &spec_div_guarded).unwrap(),
            SmtResult::Unsat,
            "{name}: guarded div_u must be UNSAT"
        );

        // 3. check_trap_free = false allows y == 0 trap, still checks postcondition on y != 0.
        let spec_partial_ok = ContractSpec::new(&div_params, &[ValType::I32], &div_entry)
            .with_ensures(&ens_le_x)
            .with_check_trap_free(false);
        assert_eq!(
            backend.check_contract(&module, &reg, &spec_partial_ok).unwrap(),
            SmtResult::Unsat,
            "{name}: partial correctness div_u <=u x must be UNSAT"
        );
        let spec_partial_bad = ContractSpec::new(&div_params, &[ValType::I32], &div_entry)
            .with_ensures(&ens_lt_x)
            .with_check_trap_free(false);
        match backend.check_contract(&module, &reg, &spec_partial_bad).unwrap() {
            SmtResult::Sat(m) => {
                let y = m.scalar_values.iter().find(|(id, _)| *id == ValId(1)).unwrap().1.as_i32().unwrap();
                assert_ne!(y, 0, "{name}: partial correctness counterexample must not trap");
            }
            other => panic!("{name}: expected Sat for ret <u x, got {other:?}"),
        }

        // 4. OOB load caught when unguarded, proved when guarded.
        let spec_load_bad = ContractSpec::new(&load_params, &[ValType::I32], &load_entry);
        match backend.check_contract(&module, &reg, &spec_load_bad).unwrap() {
            SmtResult::Sat(m) => {
                let addr = m.scalar_values.iter().find(|(id, _)| *id == ValId(0)).unwrap().1.as_u32().unwrap();
                assert!(addr > (WASM_PAGE_SIZE - 4) as u32, "{name}: expected OOB addr, got {addr}");
            }
            other => panic!("{name}: expected Sat for unguarded load, got {other:?}"),
        }
        let spec_load_ok =
            ContractSpec::new(&load_params, &[ValType::I32], &load_entry).with_requires(&addr_in_bounds);
        assert_eq!(
            backend.check_contract(&module, &reg, &spec_load_ok).unwrap(),
            SmtResult::Unsat,
            "{name}: guarded load must be UNSAT"
        );
    });
}

#[test]
fn test_contract_inductive_stateful_globals_and_memory_both_backends() {
    // Module:
    // - Memory 0: 1 page; init_data writes orig_qty = 100i64 at offset 0
    //   (with an earlier overlapping non-zero segment to test overwrite order).
    // - Global 0 (mut i64, init 0): leaves_qty
    // - Global 1 (mut i64, init 0): cum_filled
    // Notice raw initial Wasm state has orig=100, leaves=0, cum=0, so I(raw_init) is FALSE!
    let mut orig_bytes = 100i64.to_le_bytes().to_vec();
    orig_bytes.shrink_to_fit();
    let module = Module {
        memories: vec![MemoryDef {
            id: MemId(0),
            min_pages: 1,
            max_pages: Some(1),
            init_data: vec![(0, vec![0xFF; 8]), (0, orig_bytes)],
        }],
        globals: vec![
            GlobalDef { id: GlobalId(0), ty: ValType::I64, mutable: true, init: Val::I64(0) },
            GlobalDef { id: GlobalId(1), ty: ValType::I64, mutable: true, init: Val::I64(0) },
        ],
        ..Module::default()
    };
    let reg = StratumRegistry::new();

    // Invariant I(): orig > 0 && leaves >= 0 && cum >= 0 && leaves + cum == orig
    let inv = Region::build(|b| {
        b.push_let(ValId(0), ValType::I32, Op::ConstI32(0));
        b.push_let(
            ValId(1),
            ValType::I64,
            Op::Load {
                mem: MemId(0),
                addr: ValId(0),
                offset: 0,
                width: MemWidth::B8,
                signed: true,
                result_ty: ValType::I64,
            },
        );
        b.push_let(ValId(2), ValType::I64, Op::GlobalGet(GlobalId(0))); // leaves
        b.push_let(ValId(3), ValType::I64, Op::GlobalGet(GlobalId(1))); // cum
        b.push_let(ValId(4), ValType::I64, Op::ConstI64(0));
        b.push_let(ValId(5), ValType::I32, Op::Bin(BinOp::I64GtS, ValId(1), ValId(4))); // orig > 0
        b.push_let(ValId(6), ValType::I32, Op::Bin(BinOp::I64GeS, ValId(2), ValId(4))); // leaves >= 0
        b.push_let(ValId(7), ValType::I32, Op::Bin(BinOp::I64GeS, ValId(3), ValId(4))); // cum >= 0
        b.push_let(ValId(8), ValType::I64, Op::Bin(BinOp::I64Add, ValId(2), ValId(3))); // leaves + cum
        b.push_let(ValId(9), ValType::I32, Op::Bin(BinOp::I64Eq, ValId(8), ValId(1))); // == orig
        b.push_let(ValId(10), ValType::I32, Op::Bin(BinOp::I32And, ValId(5), ValId(6)));
        b.push_let(ValId(11), ValType::I32, Op::Bin(BinOp::I32And, ValId(7), ValId(9)));
        b.push_let(ValId(12), ValType::I32, Op::Bin(BinOp::I32And, ValId(10), ValId(11)));
        b.push_yield(&[ValId(12)]);
    });

    // init_ok(): leaves = load_i64(0); cum = 0
    let init_ok = Region::build(|b| {
        b.push_let(ValId(0), ValType::I32, Op::ConstI32(0));
        b.push_let(
            ValId(1),
            ValType::I64,
            Op::Load {
                mem: MemId(0),
                addr: ValId(0),
                offset: 0,
                width: MemWidth::B8,
                signed: true,
                result_ty: ValType::I64,
            },
        );
        b.push_let(ValId(2), ValType::I64, Op::ConstI64(0));
        b.push_effect(EffectOp::GlobalSet { id: GlobalId(0), val: ValId(1) });
        b.push_effect(EffectOp::GlobalSet { id: GlobalId(1), val: ValId(2) });
        b.push_yield(&[]);
    });

    // init_buggy(): forgets to set leaves (stays 0 != 100)
    let init_buggy = Region::build(|b| {
        b.push_let(ValId(0), ValType::I64, Op::ConstI64(0));
        b.push_effect(EffectOp::GlobalSet { id: GlobalId(1), val: ValId(0) });
        b.push_yield(&[]);
    });

    // req_fill(qty: i64): qty > 0 && qty <= leaves
    let fill_params = [(ValId(0), ValType::I64)];
    let req_fill = Region::build(|b| {
        b.push_let(ValId(1), ValType::I64, Op::ConstI64(0));
        b.push_let(ValId(2), ValType::I64, Op::GlobalGet(GlobalId(0)));
        b.push_let(ValId(3), ValType::I32, Op::Bin(BinOp::I64GtS, ValId(0), ValId(1)));
        b.push_let(ValId(4), ValType::I32, Op::Bin(BinOp::I64LeS, ValId(0), ValId(2)));
        b.push_let(ValId(5), ValType::I32, Op::Bin(BinOp::I32And, ValId(3), ValId(4)));
        b.push_yield(&[ValId(5)]);
    });

    // on_fill_ok(qty: i64) -> i64 { leaves -= qty; cum += qty; return cum; }
    let on_fill_ok = Region::build(|b| {
        b.push_let(ValId(1), ValType::I64, Op::GlobalGet(GlobalId(0)));
        b.push_let(ValId(2), ValType::I64, Op::GlobalGet(GlobalId(1)));
        b.push_let(ValId(3), ValType::I64, Op::Bin(BinOp::I64Sub, ValId(1), ValId(0)));
        b.push_let(ValId(4), ValType::I64, Op::Bin(BinOp::I64Add, ValId(2), ValId(0)));
        b.push_effect(EffectOp::GlobalSet { id: GlobalId(0), val: ValId(3) });
        b.push_effect(EffectOp::GlobalSet { id: GlobalId(1), val: ValId(4) });
        b.push_yield(&[ValId(4)]);
    });

    // on_fill_buggy(qty: i64) -> i64 { cum += qty; (forgets leaves -= qty!) return cum; }
    let on_fill_buggy = Region::build(|b| {
        b.push_let(ValId(2), ValType::I64, Op::GlobalGet(GlobalId(1)));
        b.push_let(ValId(4), ValType::I64, Op::Bin(BinOp::I64Add, ValId(2), ValId(0)));
        b.push_effect(EffectOp::GlobalSet { id: GlobalId(1), val: ValId(4) });
        b.push_yield(&[ValId(4)]);
    });

    // ensures_fill(qty: ValId(0), ret: ValId(1)): ret >= qty
    let ens_fill = Region::build(|b| {
        b.push_let(ValId(2), ValType::I32, Op::Bin(BinOp::I64GeS, ValId(1), ValId(0)));
        b.push_yield(&[ValId(2)]);
    });

    with_both_backends(|backend, name| {
        // 1. Base-case init_ok establishes invariant from raw Module initial state.
        let init_ok_spec = ContractSpec::new(&[], &[], &init_ok)
            .with_invariant(&inv)
            .with_initial_state(true);
        assert_eq!(
            backend.check_contract(&module, &reg, &init_ok_spec).unwrap(),
            SmtResult::Unsat,
            "{name}: valid init must establish invariant"
        );

        // 2. Base-case init_buggy MUST be caught as Sat (proves I(raw_init) is NOT assumed!).
        let init_buggy_spec = ContractSpec::new(&[], &[], &init_buggy)
            .with_invariant(&inv)
            .with_initial_state(true);
        match backend.check_contract(&module, &reg, &init_buggy_spec).unwrap() {
            SmtResult::Sat(m) => {
                assert_eq!(
                    m.global_values,
                    vec![(GlobalId(0), Val::I64(0)), (GlobalId(1), Val::I64(0))],
                    "{name}: init_buggy must report initial global values"
                );
                let mem0 = m.memory_bytes.iter().find(|(id, _)| *id == MemId(0)).expect("mem0 bytes");
                let mut raw = [0u8; 8];
                for &(off, byte) in &mem0.1 {
                    if (off as usize) < 8 {
                        raw[off as usize] = byte;
                    }
                }
                assert_eq!(i64::from_le_bytes(raw), 100, "{name}: init_data must reflect 100i64");
            }
            other => panic!("{name}: expected Sat for init_buggy, got {other:?}"),
        }

        // 3. Inductive step on_fill_ok preserves invariant from arbitrary symbolic state.
        let step_ok_spec = ContractSpec::new(&fill_params, &[ValType::I64], &on_fill_ok)
            .with_requires(&req_fill)
            .with_ensures(&ens_fill)
            .with_invariant(&inv);
        assert_eq!(
            backend.check_contract(&module, &reg, &step_ok_spec).unwrap(),
            SmtResult::Unsat,
            "{name}: valid inductive step must be UNSAT"
        );

        // 4. Buggy step on_fill_buggy returns Sat with replayable symbolic state counterexample!
        let step_buggy_spec = ContractSpec::new(&fill_params, &[ValType::I64], &on_fill_buggy)
            .with_requires(&req_fill)
            .with_ensures(&ens_fill)
            .with_invariant(&inv);
        match backend.check_contract(&module, &reg, &step_buggy_spec).unwrap() {
            SmtResult::Sat(m) => {
                let mut heap = HeapState::from_module(&module, 10_000).unwrap();
                for &(gid, val) in &m.global_values {
                    heap.globals[gid.0 as usize] = val;
                }
                for (mid, bytes) in &m.memory_bytes {
                    let mem = heap.memory_mut(*mid).unwrap();
                    for &(off, b) in bytes {
                        mem.bytes[off as usize] = b;
                    }
                }
                // Pre-state invariant and precondition MUST hold in gnomon-kernel:
                let (inv_pre_v, _) = eval_region(&module, &reg, &inv, &[], heap.clone()).unwrap();
                assert_ne!(inv_pre_v[0], Val::I32(0), "{name}: counterexample must satisfy I(pre)");
                let (req_v, _) =
                    eval_region(&module, &reg, &req_fill, &m.scalar_values, heap.clone()).unwrap();
                assert_ne!(req_v[0], Val::I32(0), "{name}: counterexample must satisfy requires");
                // Post-state invariant MUST be violated in gnomon-kernel:
                let (_, post_heap) =
                    eval_region(&module, &reg, &on_fill_buggy, &m.scalar_values, heap).unwrap();
                let (inv_post_v, _) = eval_region(&module, &reg, &inv, &[], post_heap).unwrap();
                assert_eq!(inv_post_v[0], Val::I32(0), "{name}: counterexample must falsify I(post)");
            }
            other => panic!("{name}: expected Sat for on_fill_buggy, got {other:?}"),
        }
    });
}

#[test]
fn test_inline_gnomon_assume_and_assert_soundness_both_backends() {
    let mut module = mod_with_mems(&[(0, 1, Some(1))]);
    module.host_contracts = vec![
        make_intrinsic_host(0, "gnomon", "gnomon_assume"),
        make_intrinsic_host(1, "gnomon", "gnomon_assert"),
        make_intrinsic_host(2, "env", "assume"),
        make_intrinsic_host(3, "", "gnomon::assert"),
    ];
    let reg = StratumRegistry::new();

    // 1. Valid inline harness: assume(y != 0); q = x /u y; assert(q <=u x)
    let params2 = [(ValId(0), ValType::I32), (ValId(1), ValType::I32)];
    let valid_harness = Region::build(|b| {
        b.push_let(ValId(2), ValType::I32, Op::ConstI32(0));
        b.push_let(ValId(3), ValType::I32, Op::Bin(BinOp::I32Ne, ValId(1), ValId(2)));
        b.push_call(&[], CallTarget::Host(HostCallId(0)), &[ValId(3)]);
        b.push_let(ValId(4), ValType::I32, Op::Bin(BinOp::I32DivU, ValId(0), ValId(1)));
        b.push_let(ValId(5), ValType::I32, Op::Bin(BinOp::I32LeU, ValId(4), ValId(0)));
        b.push_call(&[], CallTarget::Host(HostCallId(1)), &[ValId(5)]);
        b.push_yield(&[ValId(4)]);
    });

    // 2. Failing assert: assume(x >= 10); assert(x > 10) -> Sat with x == 10
    let params1 = [(ValId(0), ValType::I32)];
    let failing_assert = Region::build(|b| {
        b.push_let(ValId(1), ValType::I32, Op::ConstI32(10));
        b.push_let(ValId(2), ValType::I32, Op::Bin(BinOp::I32GeS, ValId(0), ValId(1)));
        b.push_call(&[], CallTarget::Host(HostCallId(2)), &[ValId(2)]);
        b.push_let(ValId(3), ValType::I32, Op::Bin(BinOp::I32GtS, ValId(0), ValId(1)));
        b.push_call(&[], CallTarget::Host(HostCallId(3)), &[ValId(3)]);
        b.push_yield(&[]);
    });

    // 3. CRITICAL SOUNDNESS: trap BEFORE assume(false) MUST STILL BE CAUGHT!
    let trap_before_assume_false = Region::build(|b| {
        b.push_let(ValId(2), ValType::I32, Op::Bin(BinOp::I32DivU, ValId(0), ValId(1)));
        b.push_let(ValId(3), ValType::I32, Op::ConstI32(0));
        b.push_call(&[], CallTarget::Host(HostCallId(0)), &[ValId(3)]);
        b.push_yield(&[ValId(2)]);
    });

    // 4. CRITICAL SOUNDNESS: trap BEFORE assume(false) INSIDE an IfElse branch!
    let trap_before_assume_in_branch = {
        let mut rb = RegionBuilder::new();
        let then_id = rb.embed_region_id(&Region::build(|b| {
            b.push_let(ValId(2), ValType::I32, Op::ConstI32(1));
            b.push_let(ValId(3), ValType::I32, Op::Bin(BinOp::I32DivU, ValId(2), ValId(1)));
            b.push_let(ValId(4), ValType::I32, Op::ConstI32(0));
            b.push_call(&[], CallTarget::Host(HostCallId(0)), &[ValId(4)]);
            b.push_yield(&[ValId(3)]);
        }));
        let else_id = rb.embed_region_id(&Region::build(|b| {
            b.push_let(ValId(5), ValType::I32, Op::ConstI32(0));
            b.push_yield(&[ValId(5)]);
        }));
        let res_tys = rb.alloc_tys(&[ValType::I32]);
        let if_node = rb.alloc_node(RegionNode::IfElse {
            cond: ValId(0),
            then_region: then_id,
            else_region: else_id,
            results: res_tys,
        });
        rb.push_subregion_id(&[(ValId(6), ValType::I32)], if_node);
        rb.push_yield(&[ValId(6)]);
        rb.finish()
    };

    // 5. CRITICAL SOUNDNESS: trap in branch, then assume(false) AFTER IfElse!
    let trap_in_branch_assume_after = {
        let mut rb = RegionBuilder::new();
        let then_id = rb.embed_region_id(&Region::build(|b| {
            b.push_effect(EffectOp::Trap(TrapCode::Unreachable));
            b.push_yield(&[]);
        }));
        let else_id = rb.embed_region_id(&Region::build(|b| {
            b.push_yield(&[]);
        }));
        let if_node = rb.alloc_node(RegionNode::IfElse {
            cond: ValId(0),
            then_region: then_id,
            else_region: else_id,
            results: gnomon_kernel::Span::EMPTY,
        });
        rb.push_subregion_id(&[], if_node);
        rb.push_let(ValId(2), ValType::I32, Op::ConstI32(0));
        rb.push_call(&[], CallTarget::Host(HostCallId(0)), &[ValId(2)]);
        rb.push_yield(&[]);
        rb.finish()
    };

    // 6. CRITICAL SOUNDNESS: MemoryFill unroll overflow BEFORE assume(false) MUST return Unknown
    //    when in-bounds (not Unsat!), and Sat when OOB is reachable!
    let overflow_before_assume_false = Region::build(|b| {
        b.push_let(ValId(1), ValType::I32, Op::ConstI32(0));
        b.push_let(ValId(2), ValType::I32, Op::ConstI32(7));
        b.push_effect(EffectOp::MemoryFill {
            mem: MemId(0),
            dst: ValId(1),
            val: ValId(2),
            len: ValId(0),
        });
        b.push_call(&[], CallTarget::Host(HostCallId(0)), &[ValId(1)]); // assume(0)
        b.push_yield(&[]);
    });
    let len_le_1000 = Region::build(|b| {
        b.push_let(ValId(1), ValType::I32, Op::ConstI32(1000));
        b.push_let(ValId(2), ValType::I32, Op::Bin(BinOp::I32LeU, ValId(0), ValId(1)));
        b.push_yield(&[ValId(2)]);
    });

    // 7. Inline assume/assert inside check_vc and check_equivalence!
    let vc_goal_with_assume = Region::build(|b| {
        b.push_let(ValId(1), ValType::I32, Op::ConstI32(0));
        b.push_let(ValId(2), ValType::I32, Op::Bin(BinOp::I32Ne, ValId(0), ValId(1)));
        b.push_call(&[], CallTarget::Host(HostCallId(0)), &[ValId(2)]);
        b.push_let(ValId(3), ValType::I32, Op::Bin(BinOp::I32DivU, ValId(0), ValId(0)));
        b.push_let(ValId(4), ValType::I32, Op::ConstI32(1));
        b.push_let(ValId(5), ValType::I32, Op::Bin(BinOp::I32Eq, ValId(3), ValId(4)));
        b.push_call(&[], CallTarget::Host(HostCallId(1)), &[ValId(5)]);
        b.push_yield(&[ValId(5)]);
    });
    let vc_ok = VcObligation {
        kind: VcKind::Init,
        params: vec![(ValId(0), ValType::I32)],
        assumptions: RegionList::empty(),
        goal: vc_goal_with_assume,
    };

    let eq_lhs = Region::build(|b| {
        b.push_let(ValId(1), ValType::I32, Op::ConstI32(0));
        b.push_let(ValId(2), ValType::I32, Op::Bin(BinOp::I32Ne, ValId(0), ValId(1)));
        b.push_call(&[], CallTarget::Host(HostCallId(0)), &[ValId(2)]);
        b.push_let(ValId(3), ValType::I32, Op::Bin(BinOp::I32DivU, ValId(0), ValId(0)));
        b.push_yield(&[ValId(3)]);
    });
    let eq_rhs = Region::build(|b| {
        b.push_let(ValId(1), ValType::I32, Op::ConstI32(1));
        b.push_yield(&[ValId(1)]);
    });

    with_both_backends(|backend, name| {
        let s1 = ContractSpec::new(&params2, &[ValType::I32], &valid_harness);
        assert_eq!(
            backend.check_contract(&module, &reg, &s1).unwrap(),
            SmtResult::Unsat,
            "{name}: valid inline assume+assert harness must be UNSAT"
        );

        let s2 = ContractSpec::new(&params1, &[], &failing_assert);
        match backend.check_contract(&module, &reg, &s2).unwrap() {
            SmtResult::Sat(m) => {
                assert!(
                    m.scalar_values.contains(&(ValId(0), Val::I32(10))),
                    "{name}: expected x=10 counterexample, got {:?}",
                    m.scalar_values
                );
            }
            other => panic!("{name}: expected Sat for failing inline assert, got {other:?}"),
        }

        let s3 = ContractSpec::new(&params2, &[ValType::I32], &trap_before_assume_false);
        match backend.check_contract(&module, &reg, &s3).unwrap() {
            SmtResult::Sat(m) => {
                assert!(
                    m.scalar_values.contains(&(ValId(1), Val::I32(0))),
                    "{name}: trap before assume(0) must produce y=0 counterexample"
                );
            }
            other => panic!("{name}: trap BEFORE assume(0) MUST be caught as Sat, got {other:?}"),
        }

        let s4 = ContractSpec::new(&params2, &[ValType::I32], &trap_before_assume_in_branch);
        match backend.check_contract(&module, &reg, &s4).unwrap() {
            SmtResult::Sat(m) => {
                let c = m.scalar_values.iter().find(|(id, _)| *id == ValId(0)).unwrap().1.as_i32().unwrap();
                let y = m.scalar_values.iter().find(|(id, _)| *id == ValId(1)).unwrap().1.as_i32().unwrap();
                assert!(c != 0 && y == 0, "{name}: expected cond!=0 && y==0, got cond={c}, y={y}");
            }
            other => panic!("{name}: trap BEFORE assume(0) in branch MUST be Sat, got {other:?}"),
        }

        let s5 = ContractSpec::new(&params1, &[], &trap_in_branch_assume_after);
        match backend.check_contract(&module, &reg, &s5).unwrap() {
            SmtResult::Sat(m) => {
                let c = m.scalar_values.iter().find(|(id, _)| *id == ValId(0)).unwrap().1.as_i32().unwrap();
                assert_ne!(c, 0, "{name}: expected cond!=0 for trap in branch before assume(0)");
            }
            other => panic!("{name}: trap in branch before assume(0) MUST be Sat, got {other:?}"),
        }

        let s6_oob = ContractSpec::new(&params1, &[], &overflow_before_assume_false);
        assert!(
            matches!(backend.check_contract(&module, &reg, &s6_oob).unwrap(), SmtResult::Sat(_)),
            "{name}: OOB MemoryFill BEFORE assume(0) must return Sat"
        );
        let s6_overflow =
            ContractSpec::new(&params1, &[], &overflow_before_assume_false).with_requires(&len_le_1000);
        assert!(
            matches!(backend.check_contract(&module, &reg, &s6_overflow).unwrap(), SmtResult::Unknown(_)),
            "{name}: in-bounds unroll overflow BEFORE assume(0) must return Unknown, not Unsat"
        );

        assert_eq!(
            backend.check_vc(&module, &reg, &vc_ok).unwrap(),
            SmtResult::Unsat,
            "{name}: inline assume+assert in check_vc must be UNSAT"
        );
        assert_eq!(
            backend.check_equivalence(&module, &reg, &eq_lhs, &eq_rhs, None).unwrap(),
            SmtResult::Unsat,
            "{name}: inline assume in check_equivalence must be UNSAT"
        );
    });
}

#[test]
fn test_contract_uf_cegar_pure_total_stratum_both_backends() {
    let module = Module::default();
    let mut reg = StratumRegistry::new();

    let fmix_body = Region::build(|b| {
        b.push_let(ValId(1), ValType::I64, Op::ConstI64(33));
        b.push_let(ValId(2), ValType::I64, Op::Bin(BinOp::I64ShrU, ValId(0), ValId(1)));
        b.push_let(ValId(3), ValType::I64, Op::Bin(BinOp::I64Xor, ValId(0), ValId(2)));
        b.push_let(ValId(4), ValType::I64, Op::ConstI64(0xff51_afd7_ed55_8ccdu64 as i64));
        b.push_let(ValId(5), ValType::I64, Op::Bin(BinOp::I64Mul, ValId(3), ValId(4)));
        b.push_let(ValId(6), ValType::I64, Op::Bin(BinOp::I64ShrU, ValId(5), ValId(1)));
        b.push_let(ValId(7), ValType::I64, Op::Bin(BinOp::I64Xor, ValId(5), ValId(6)));
        b.push_let(ValId(8), ValType::I64, Op::ConstI64(0xc4ce_b9fe_1a85_ec53u64 as i64));
        b.push_let(ValId(9), ValType::I64, Op::Bin(BinOp::I64Mul, ValId(7), ValId(8)));
        b.push_let(ValId(10), ValType::I64, Op::Bin(BinOp::I64ShrU, ValId(9), ValId(1)));
        b.push_let(ValId(11), ValType::I64, Op::Bin(BinOp::I64Xor, ValId(9), ValId(10)));
        b.push_yield(&[ValId(11)]);
    });
    let fmix_call = Region::build(|b| {
        b.push_call(&[(ValId(1), ValType::I64)], CallTarget::Stratum(StratumId(71)), &[ValId(0)]);
        b.push_yield(&[ValId(1)]);
    });
    reg.promote_stratum(Stratum {
        op: StratumOp {
            id: StratumId(71),
            name: "fmix64_contract".into(),
            layer: 1,
            params: vec![(ValId(0), ValType::I64)],
            results: vec![ValType::I64],
            body: fmix_body,
            docstring: "Nonlinear 64-bit mixer".into(),
        },
        laws: LawList::single(Law {
            name: "fmix64_contract_refl".into(),
            kind: LawKind::Algebraic,
            params: vec![(ValId(0), ValType::I64)],
            precondition: Region::empty(),
            lhs: fmix_call.clone(),
            rhs: fmix_call,
            proof_digest: [0x71; 32],
        }),
    })
    .unwrap();

    let params = [(ValId(0), ValType::I64), (ValId(1), ValType::I64)];
    // entry_ok(x, y) = fmix64^4((x << 1) + x + y)
    let entry_ok = Region::build(|b| {
        b.push_let(ValId(2), ValType::I64, Op::ConstI64(1));
        b.push_let(ValId(3), ValType::I64, Op::Bin(BinOp::I64Shl, ValId(0), ValId(2)));
        b.push_let(ValId(4), ValType::I64, Op::Bin(BinOp::I64Add, ValId(3), ValId(0)));
        b.push_let(ValId(5), ValType::I64, Op::Bin(BinOp::I64Add, ValId(4), ValId(1)));
        let mut cur = ValId(5);
        for nid in 10u32..14 {
            b.push_call(&[(ValId(nid), ValType::I64)], CallTarget::Stratum(StratumId(71)), &[cur]);
            cur = ValId(nid);
        }
        b.push_yield(&[cur]);
    });
    // ensures(x: 0, y: 1, ret: 2): ret == fmix64^4(x * 3 + y)
    let ensures_4 = Region::build(|b| {
        b.push_let(ValId(3), ValType::I64, Op::ConstI64(3));
        b.push_let(ValId(4), ValType::I64, Op::Bin(BinOp::I64Mul, ValId(0), ValId(3)));
        b.push_let(ValId(5), ValType::I64, Op::Bin(BinOp::I64Add, ValId(4), ValId(1)));
        let mut cur = ValId(5);
        for nid in 10u32..14 {
            b.push_call(&[(ValId(nid), ValType::I64)], CallTarget::Stratum(StratumId(71)), &[cur]);
            cur = ValId(nid);
        }
        b.push_let(ValId(20), ValType::I32, Op::Bin(BinOp::I64Eq, ValId(2), cur));
        b.push_yield(&[ValId(20)]);
    });

    // Buggy single-round entry: fmix64(x * 3 + y + 1) vs ensures fmix64(x * 3 + y)
    let entry_buggy = Region::build(|b| {
        b.push_let(ValId(3), ValType::I64, Op::ConstI64(3));
        b.push_let(ValId(4), ValType::I64, Op::Bin(BinOp::I64Mul, ValId(0), ValId(3)));
        b.push_let(ValId(5), ValType::I64, Op::Bin(BinOp::I64Add, ValId(4), ValId(1)));
        b.push_let(ValId(6), ValType::I64, Op::ConstI64(1));
        b.push_let(ValId(7), ValType::I64, Op::Bin(BinOp::I64Add, ValId(5), ValId(6)));
        b.push_call(&[(ValId(10), ValType::I64)], CallTarget::Stratum(StratumId(71)), &[ValId(7)]);
        b.push_yield(&[ValId(10)]);
    });
    let ensures_1 = Region::build(|b| {
        b.push_let(ValId(3), ValType::I64, Op::ConstI64(3));
        b.push_let(ValId(4), ValType::I64, Op::Bin(BinOp::I64Mul, ValId(0), ValId(3)));
        b.push_let(ValId(5), ValType::I64, Op::Bin(BinOp::I64Add, ValId(4), ValId(1)));
        b.push_call(&[(ValId(10), ValType::I64)], CallTarget::Stratum(StratumId(71)), &[ValId(5)]);
        b.push_let(ValId(20), ValType::I32, Op::Bin(BinOp::I64Eq, ValId(2), ValId(10)));
        b.push_yield(&[ValId(20)]);
    });

    let mut native = BitwuzlaNativeBackend::with_time_limit_ms(5_000);
    let mut pipe = BitwuzlaPipeBackend::new().unwrap();
    for (backend, name) in [
        (&mut native as &mut dyn SmtBackend, "native"),
        (&mut pipe as &mut dyn SmtBackend, "pipe"),
    ] {
        let ok_spec = ContractSpec::new(&params, &[ValType::I64], &entry_ok).with_ensures(&ensures_4);
        assert_eq!(
            backend.check_contract(&module, &reg, &ok_spec).unwrap(),
            SmtResult::Unsat,
            "{name}: UF CEGAR in check_contract must prove fmix64^4 contract quickly"
        );
        let bad_spec =
            ContractSpec::new(&params, &[ValType::I64], &entry_buggy).with_ensures(&ensures_1);
        assert!(
            matches!(backend.check_contract(&module, &reg, &bad_spec).unwrap(), SmtResult::Sat(_)),
            "{name}: buggy fmix64 contract must fall back to concrete Layer-0 and return Sat"
        );
    }
}

#[test]
fn test_contract_allow_traps_assert_and_pre_loop_overflow_both_backends() {
    let module = Module {
        host_contracts: vec![
            make_intrinsic_host(0, "gnomon", "gnomon_assume"),
            make_intrinsic_host(1, "gnomon", "gnomon_assert"),
        ],
        ..Module::default()
    };
    let reg = StratumRegistry::new();
    let params1 = [(ValId(0), ValType::I32)];

    // 1. Regression for check_trap_free: false vs inline gnomon_assert(0):
    //    let q = 100 /u x; gnomon_assert(0);
    //    DivByZero on x == 0 is allowed, but gnomon_assert(0) on x != 0 MUST still return Sat!
    let div_then_assert_false = Region::build(|b| {
        b.push_let(ValId(1), ValType::I32, Op::ConstI32(100));
        b.push_let(ValId(2), ValType::I32, Op::Bin(BinOp::I32DivU, ValId(1), ValId(0)));
        b.push_let(ValId(3), ValType::I32, Op::ConstI32(0));
        b.push_call(&[], CallTarget::Host(HostCallId(1)), &[ValId(3)]);
        b.push_yield(&[ValId(2)]);
    });
    //    let q = 100 /u x; gnomon_assert(q <=u 100);
    //    With check_trap_free: false, x == 0 trap is allowed and x != 0 satisfies assert -> Unsat.
    let div_then_assert_true = Region::build(|b| {
        b.push_let(ValId(1), ValType::I32, Op::ConstI32(100));
        b.push_let(ValId(2), ValType::I32, Op::Bin(BinOp::I32DivU, ValId(1), ValId(0)));
        b.push_let(ValId(3), ValType::I32, Op::Bin(BinOp::I32LeU, ValId(2), ValId(1)));
        b.push_call(&[], CallTarget::Host(HostCallId(1)), &[ValId(3)]);
        b.push_yield(&[ValId(2)]);
    });

    // 2. Regression for BoundedLoop > 64 iters inside `requires`:
    //    loop (i = 0; i < n; i += 1) {} returns 1 (max_iters = 100 > MAX_SMT_LOOP_UNROLL = 64).
    let req_loop_100 = {
        let mut rb = RegionBuilder::new();
        let body_id = rb.embed_region_id(&Region::build(|b| {
            // ValId(10) is loop state `i`; break with 1 when i >=u ValId(0) (n), else continue(i + 1).
            b.push_let(ValId(11), ValType::I32, Op::Bin(BinOp::I32GeU, ValId(10), ValId(0)));
            b.push_let(ValId(12), ValType::I32, Op::ConstI32(1));
            b.push_break(0, Some(ValId(11)), &[ValId(12)]);
            b.push_let(ValId(13), ValType::I32, Op::Bin(BinOp::I32Add, ValId(10), ValId(12)));
            b.push_continue(0, None, &[ValId(13)]);
        }));
        rb.push_let(ValId(1), ValType::I32, Op::ConstI32(0));
        let init_vars = rb.alloc_vals(&[ValId(1)]);
        let state_vars = rb.alloc_vars(&[(ValId(10), ValType::I32)]);
        let loop_node = rb.alloc_node(RegionNode::BoundedLoop {
            max_iters: 100,
            init_vars,
            state_vars,
            body: body_id,
        });
        rb.push_subregion_id(&[(ValId(2), ValType::I32)], loop_node);
        rb.push_yield(&[ValId(2)]);
        rb.finish()
    };
    // entry(n) -> n; ensures: ret <=u 64 (holds on all non-overflowing n <= 64, unknown for n > 64!)
    let id_entry = Region::build(|b| {
        b.push_yield(&[ValId(0)]);
    });
    let ens_le_64 = Region::build(|b| {
        b.push_let(ValId(2), ValType::I32, Op::ConstI32(64));
        b.push_let(ValId(3), ValType::I32, Op::Bin(BinOp::I32LeU, ValId(1), ValId(2)));
        b.push_yield(&[ValId(3)]);
    });

    with_both_backends(|backend, name| {
        let s_assert_fail = ContractSpec::new(&params1, &[ValType::I32], &div_then_assert_false)
            .with_check_trap_free(false);
        match backend.check_contract(&module, &reg, &s_assert_fail).unwrap() {
            SmtResult::Sat(m) => {
                let x = m
                    .scalar_values
                    .iter()
                    .find(|(id, _)| *id == ValId(0))
                    .unwrap()
                    .1
                    .as_i32()
                    .unwrap();
                assert_ne!(x, 0, "{name}: assert(0) counterexample under allow-traps must have x != 0");
            }
            other => panic!(
                "{name}: inline gnomon_assert(0) MUST NOT be masked by check_trap_free: false, got {other:?}"
            ),
        }

        let s_assert_ok = ContractSpec::new(&params1, &[ValType::I32], &div_then_assert_true)
            .with_check_trap_free(false);
        assert_eq!(
            backend.check_contract(&module, &reg, &s_assert_ok).unwrap(),
            SmtResult::Unsat,
            "{name}: valid assert with check_trap_free: false must still be UNSAT"
        );

        let s_pre_overflow = ContractSpec::new(&params1, &[ValType::I32], &id_entry)
            .with_requires(&req_loop_100)
            .with_ensures(&ens_le_64);
        assert!(
            matches!(backend.check_contract(&module, &reg, &s_pre_overflow).unwrap(), SmtResult::Unknown(_)),
            "{name}: BoundedLoop > 64 overflow in `requires` must return Unknown, not Unsat"
        );
    });

    // 3. Regression for `EffectOp::Trap(Unreachable)` on a symbolic branch inside a
    //    value-returning function (must fold `path_active` to `Some(false)` instead of
    //    emitting a dead empty fallthrough that collides with `Return(&[val])`).
    let trap_branch_in_value_func = {
        let mut rb = RegionBuilder::new();
        let then_id = rb.embed_region_id(&Region::build(|b| {
            b.push_effect(EffectOp::Trap(TrapCode::Unreachable));
        }));
        let else_id = rb.embed_region_id(&Region::build(|b| {
            b.push_let(ValId(2), ValType::I32, Op::ConstI32(1));
            b.push_return(&[ValId(2)]);
        }));
        let if_node = rb.alloc_node(RegionNode::IfElse {
            cond: ValId(0),
            then_region: then_id,
            else_region: else_id,
            results: gnomon_kernel::Span::EMPTY,
        });
        rb.push_subregion_id(&[], if_node);
        rb.finish()
    };
    with_both_backends(|backend, name| {
        let spec = ContractSpec::new(&params1, &[ValType::I32], &trap_branch_in_value_func);
        match backend.check_contract(&module, &reg, &spec).unwrap() {
            SmtResult::Sat(m) => {
                let c = m
                    .scalar_values
                    .iter()
                    .find(|(id, _)| *id == ValId(0))
                    .unwrap()
                    .1
                    .as_i32()
                    .unwrap();
                assert_ne!(c, 0, "{name}: expected cond != 0 triggering Unreachable trap");
            }
            other => panic!("{name}: expected Sat for Unreachable branch, got {other:?}"),
        }
    });
}
