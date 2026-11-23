use gnomon_kernel::{
    BinOp, CallTarget, EffectOp, GlobalDef, GlobalId, HeapState, HostCallId, HostContract,
    Law, LawKind, LawList, MemId, MemWidth, MemoryDef, Module, OffsetRange, Op, Region, SliceBound,
    Stratum, StratumId, StratumOp, StratumRegistry, TrapCode, UnOp, Val, ValId, ValType,
    WASM_PAGE_SIZE, eval_region, split_invariant_loop,
};
use gnomon_sieve::{
    BitwuzlaNativeBackend, BitwuzlaPipeBackend, EgglogSimplifier, EqSatConfig, SmtBackend,
    SmtResult,
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
