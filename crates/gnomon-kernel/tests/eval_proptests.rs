use gnomon_kernel::*;
use proptest::prelude::*;

fn empty_mod_reg() -> (Module, StratumRegistry) {
    (Module::default(), StratumRegistry::new())
}

fn mod_with_mem(min_pages: u32, max_pages: Option<u32>) -> Module {
    Module {
        memories: vec![MemoryDef { id: MemId(0), min_pages, max_pages, init_data: vec![] }],
        ..Module::default()
    }
}

#[test]
fn test_div_rem_trap_semantics() {
    let (m, reg) = empty_mod_reg();
    let heap = HeapState::from_module(&m, 1000).unwrap();

    let eval_bin = |op: BinOp, ty: ValType, a: Val, b: Val| {
        let r = Region::build(|rb| {
            rb.push_let(ValId(2), ty, Op::Bin(op, ValId(0), ValId(1)));
            rb.push_yield(&[ValId(2)]);
        });
        eval_region(&m, &reg, &r, &[(ValId(0), a), (ValId(1), b)], heap.clone()).map(|(v, _)| v[0])
    };

    assert_eq!(eval_bin(BinOp::I32DivS, ValType::I32, Val::I32(i32::MIN), Val::I32(-1)), Err(TrapCode::IntOverflow));
    assert_eq!(eval_bin(BinOp::I32RemS, ValType::I32, Val::I32(i32::MIN), Val::I32(-1)), Ok(Val::I32(0)));
    assert_eq!(eval_bin(BinOp::I32DivS, ValType::I32, Val::I32(7), Val::I32(0)), Err(TrapCode::DivByZero));
    assert_eq!(eval_bin(BinOp::I32DivU, ValType::I32, Val::I32(7), Val::I32(0)), Err(TrapCode::DivByZero));
    assert_eq!(eval_bin(BinOp::I32RemS, ValType::I32, Val::I32(7), Val::I32(0)), Err(TrapCode::DivByZero));
    assert_eq!(eval_bin(BinOp::I32RemU, ValType::I32, Val::I32(7), Val::I32(0)), Err(TrapCode::DivByZero));

    assert_eq!(eval_bin(BinOp::I64DivS, ValType::I64, Val::I64(i64::MIN), Val::I64(-1)), Err(TrapCode::IntOverflow));
    assert_eq!(eval_bin(BinOp::I64RemS, ValType::I64, Val::I64(i64::MIN), Val::I64(-1)), Ok(Val::I64(0)));
    assert_eq!(eval_bin(BinOp::I64DivS, ValType::I64, Val::I64(9), Val::I64(0)), Err(TrapCode::DivByZero));
    assert_eq!(eval_bin(BinOp::I64DivU, ValType::I64, Val::I64(9), Val::I64(0)), Err(TrapCode::DivByZero));
    assert_eq!(eval_bin(BinOp::I64RemS, ValType::I64, Val::I64(9), Val::I64(0)), Err(TrapCode::DivByZero));
    assert_eq!(eval_bin(BinOp::I64RemU, ValType::I64, Val::I64(9), Val::I64(0)), Err(TrapCode::DivByZero));
}

#[test]
fn test_unops_and_rotates() {
    let (m, reg) = empty_mod_reg();
    let heap = HeapState::from_module(&m, 1000).unwrap();
    let r = Region::build(|b| {
        b.push_let(ValId(1), ValType::I32, Op::Un(UnOp::I32Extend8S, ValId(0)));
        b.push_let(ValId(2), ValType::I32, Op::Un(UnOp::I32Extend16S, ValId(0)));
        b.push_let(ValId(3), ValType::I64, Op::Un(UnOp::I64ExtendI32U, ValId(0)));
        b.push_let(ValId(4), ValType::I64, Op::Un(UnOp::I64Extend32S, ValId(3)));
        b.push_let(ValId(5), ValType::I32, Op::Un(UnOp::I32Popcnt, ValId(0)));
        b.push_let(ValId(6), ValType::I32, Op::Un(UnOp::I32Clz, ValId(0)));
        b.push_let(ValId(7), ValType::I32, Op::Un(UnOp::I32Ctz, ValId(0)));
        b.push_yield(&[ValId(1), ValId(2), ValId(3), ValId(4), ValId(5), ValId(6), ValId(7)]);
    });
    let x = 0x80ff_u32 as i32;
    let (vals, _) = eval_region(&m, &reg, &r, &[(ValId(0), Val::I32(x))], heap).unwrap();
    assert_eq!(vals, vec![
        Val::I32(-1),
        Val::I32((x as i16) as i32),
        Val::I64(0x80ff),
        Val::I64(0x80ff),
        Val::I32(x.count_ones() as i32),
        Val::I32(x.leading_zeros() as i32),
        Val::I32(x.trailing_zeros() as i32),
    ]);
}

#[test]
fn test_multi_memory_bounds_le_copy_fill_grow() {
    let m = Module {
        memories: vec![
            MemoryDef { id: MemId(0), min_pages: 1, max_pages: Some(2), init_data: vec![(0, vec![0x80, 0x7f, 0x01, 0x02])] },
            MemoryDef { id: MemId(1), min_pages: 1, max_pages: Some(1), init_data: vec![(0, vec![0xaa; 8])] },
        ],
        ..Module::default()
    };
    let reg = StratumRegistry::new();
    let heap = HeapState::from_module(&m, 10_000).unwrap();

    let r = Region::build(|b| {
        b.push_let(ValId(0), ValType::I32, Op::ConstI32(0));
        b.push_let(ValId(1), ValType::I32, Op::Load { mem: MemId(0), addr: ValId(0), offset: 0, width: MemWidth::B1, signed: true, result_ty: ValType::I32 });
        b.push_let(ValId(2), ValType::I32, Op::Load { mem: MemId(0), addr: ValId(0), offset: 0, width: MemWidth::B1, signed: false, result_ty: ValType::I32 });
        b.push_let(ValId(3), ValType::I32, Op::Load { mem: MemId(0), addr: ValId(0), offset: 0, width: MemWidth::B4, signed: false, result_ty: ValType::I32 });
        b.push_let(ValId(4), ValType::I64, Op::ConstI64(0x0102_0304_0506_0708));
        b.push_effect(EffectOp::Store { mem: MemId(0), addr: ValId(0), offset: 16, width: MemWidth::B8, val: ValId(4) });
        b.push_let(ValId(5), ValType::I64, Op::Load { mem: MemId(0), addr: ValId(0), offset: 16, width: MemWidth::B8, signed: false, result_ty: ValType::I64 });
        b.push_let(ValId(6), ValType::I32, Op::ConstI32(1));
        b.push_let(ValId(7), ValType::I32, Op::MemoryGrow { mem: MemId(0), delta: ValId(6) });
        b.push_let(ValId(8), ValType::I32, Op::MemorySize(MemId(0)));
        b.push_let(ValId(9), ValType::I32, Op::MemoryGrow { mem: MemId(0), delta: ValId(6) });
        b.push_yield(&[ValId(1), ValId(2), ValId(3), ValId(5), ValId(7), ValId(8), ValId(9)]);
    });
    let (vals, mut heap2) = eval_region(&m, &reg, &r, &[], heap).unwrap();
    assert_eq!(vals, vec![
        Val::I32(-128),
        Val::I32(128),
        Val::I32(0x0201_7f80),
        Val::I64(0x0102_0304_0506_0708),
        Val::I32(1),
        Val::I32(2),
        Val::I32(-1),
    ]);
    assert_eq!(&heap2.memory(MemId(1)).unwrap().bytes[..8], &[0xaa; 8]);

    heap2.memory_mut(MemId(0)).unwrap().fill(32, 0x5a, 4).unwrap();
    heap2.memory_copy(MemId(0), MemId(0), 34, 32, 4).unwrap();
    assert_eq!(&heap2.memory(MemId(0)).unwrap().bytes[32..38], &[0x5a; 6]);
    heap2.memory_copy(MemId(1), MemId(0), 16, 16, 8).unwrap();
    assert_eq!(&heap2.memory(MemId(1)).unwrap().bytes[16..24], &0x0102_0304_0506_0708u64.to_le_bytes());

    let oob = Region::build(|b| {
        b.push_let(ValId(0), ValType::I32, Op::ConstI32(-1));
        b.push_let(ValId(1), ValType::I32, Op::Load { mem: MemId(0), addr: ValId(0), offset: 1, width: MemWidth::B1, signed: false, result_ty: ValType::I32 });
        b.push_yield(&[ValId(1)]);
    });
    assert_eq!(eval_region(&m, &reg, &oob, &[], heap2), Err(TrapCode::OutOfBoundsMem));
}

#[test]
fn test_structured_control_flow() {
    let (m, reg) = empty_mod_reg();
    let heap = HeapState::from_module(&m, 5000).unwrap();

    let inner = Region::build(|b| {
        b.push_break(1, Some(ValId(0)), &[ValId(2)]);
        b.push_break(0, None, &[ValId(1)]);
    });
    let nested = Region::build(|b| {
        b.push_let(ValId(1), ValType::I32, Op::ConstI32(10));
        b.push_let(ValId(2), ValType::I32, Op::ConstI32(99));
        b.push_subregion(&[(ValId(3), ValType::I32)], &inner);
        b.push_yield(&[ValId(3)]);
    });
    assert_eq!(eval_region(&m, &reg, &nested, &[(ValId(0), Val::I32(1))], heap.clone()).unwrap().0, vec![Val::I32(99)]);
    assert_eq!(eval_region(&m, &reg, &nested, &[(ValId(0), Val::I32(0))], heap.clone()).unwrap().0, vec![Val::I32(10)]);

    let make_loop = |max_iters: u32| {
        let then_br = Region::build(|b| {
            b.push_let(ValId(6), ValType::I32, Op::Bin(BinOp::I32Add, ValId(3), ValId(2)));
            b.push_let(ValId(7), ValType::I32, Op::ConstI32(1));
            b.push_let(ValId(8), ValType::I32, Op::Bin(BinOp::I32Sub, ValId(2), ValId(7)));
            b.push_continue(1, None, &[ValId(8), ValId(6)]);
        });
        let if_reg = Region::if_else(ValId(5), &then_br, &Region::empty(), &[]);
        let body = Region::build(|b| {
            b.push_let(ValId(4), ValType::I32, Op::ConstI32(0));
            b.push_let(ValId(5), ValType::I32, Op::Bin(BinOp::I32GtS, ValId(2), ValId(4)));
            b.push_subregion(&[], &if_reg);
            b.push_yield(&[ValId(3)]);
        });
        let lp = Region::bounded_loop(
            max_iters,
            &[ValId(0), ValId(1)],
            &[(ValId(2), ValType::I32), (ValId(3), ValType::I32)],
            &body,
        );
        Region::build(|b| {
            b.push_let(ValId(1), ValType::I32, Op::ConstI32(0));
            b.push_subregion(&[(ValId(10), ValType::I32)], &lp);
            b.push_yield(&[ValId(10)]);
        })
    };
    assert_eq!(eval_region(&m, &reg, &make_loop(10), &[(ValId(0), Val::I32(5))], heap.clone()).unwrap().0, vec![Val::I32(15)]);
    assert_eq!(eval_region(&m, &reg, &make_loop(4), &[(ValId(0), Val::I32(5))], heap.clone()), Err(TrapCode::OutOfFuel));

    let ret_inner = Region::build(|b| b.push_return(&[ValId(0)]));
    let ret = Region::build(|b| {
        b.push_let(ValId(0), ValType::I32, Op::ConstI32(42));
        b.push_subregion(&[], &ret_inner);
    });
    assert_eq!(eval_region(&m, &reg, &ret, &[], heap).unwrap().0, vec![Val::I32(42)]);
}

#[test]
fn test_vc_splitter_soundness_and_failure_modes() {
    let (m, reg) = empty_mod_reg();
    let heap = HeapState::from_module(&m, 10_000).unwrap();

    let make_inv_loop = |bad_inv: bool, bad_fuel: bool| {
        let i = ValId(10);
        let acc = ValId(11);
        let cond = Region::build(|b| {
            b.push_let(ValId(20), ValType::I32, Op::ConstI32(0));
            b.push_let(ValId(21), ValType::I32, Op::Bin(BinOp::I32GtS, i, ValId(20)));
            b.push_yield(&[ValId(21)]);
        });
        let invariant_pred = if bad_inv {
            Region::build(|b| {
                b.push_let(ValId(30), ValType::I32, Op::ConstI32(5));
                b.push_let(ValId(31), ValType::I32, Op::Bin(BinOp::I32LtS, acc, ValId(30)));
                b.push_yield(&[ValId(31)]);
            })
        } else {
            Region::build(|b| {
                b.push_let(ValId(30), ValType::I32, Op::ConstI32(0));
                b.push_let(ValId(31), ValType::I32, Op::Bin(BinOp::I32GeS, i, ValId(30)));
                b.push_let(ValId(32), ValType::I32, Op::Bin(BinOp::I32GeS, acc, ValId(30)));
                b.push_let(ValId(33), ValType::I32, Op::Bin(BinOp::I32And, ValId(31), ValId(32)));
                b.push_yield(&[ValId(33)]);
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
        Region::invariant_loop(
            &[ValId(0), ValId(1)],
            &[(i, ValType::I32), (acc, ValType::I32)],
            &cond,
            &invariant_pred,
            &fuel_measure,
            &body,
        )
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
        b.push_yield(&[ValId(71)]);
    });

    let good_vcs = split_invariant_loop(
        vec![(ValId(0), ValType::I32), (ValId(1), ValType::I32)],
        Some(pre.clone()),
        &make_inv_loop(false, false),
        post.clone(),
    ).unwrap();

    for n in 0..=8 {
        assert_eq!(eval_vc(&m, &reg, &good_vcs.init, &[Val::I32(n), Val::I32(0)], heap.clone()), VcEvalResult::Holds);
    }
    assert_eq!(eval_vc(&m, &reg, &good_vcs.init, &[Val::I32(-1), Val::I32(0)], heap.clone()), VcEvalResult::Vacuous);
    assert_eq!(eval_vc(&m, &reg, &good_vcs.preservation, &[Val::I32(3), Val::I32(2), Val::I32(5), Val::I32(0)], heap.clone()), VcEvalResult::Holds);
    assert_eq!(eval_vc(&m, &reg, &good_vcs.exit, &[Val::I32(0), Val::I32(5), Val::I32(5), Val::I32(0)], heap.clone()), VcEvalResult::Holds);

    let bad_inv_vcs = split_invariant_loop(
        vec![(ValId(0), ValType::I32), (ValId(1), ValType::I32)],
        Some(pre.clone()),
        &make_inv_loop(true, false),
        post.clone(),
    ).unwrap();
    assert_eq!(eval_vc(&m, &reg, &bad_inv_vcs.preservation, &[Val::I32(2), Val::I32(4), Val::I32(6), Val::I32(0)], heap.clone()), VcEvalResult::Violated(None));

    let bad_fuel_vcs = split_invariant_loop(
        vec![(ValId(0), ValType::I32), (ValId(1), ValType::I32)],
        Some(pre),
        &make_inv_loop(false, true),
        post,
    ).unwrap();
    assert_eq!(eval_vc(&m, &reg, &bad_fuel_vcs.preservation, &[Val::I32(2), Val::I32(1), Val::I32(3), Val::I32(0)], heap), VcEvalResult::Violated(None));
}

#[test]
fn test_host_contract_footprints_and_frame_check() {
    let mut m = mod_with_mem(1, None);
    let ok_host = HostContract {
        id: HostCallId(0),
        module_name: "env".into(),
        field_name: "poke".into(),
        params: vec![(ValId(0), ValType::I32), (ValId(1), ValType::I32)],
        results: vec![(ValId(2), ValType::I32)],
        precondition: Region::build(|b| {
            b.push_let(ValId(10), ValType::I32, Op::ConstI32(4));
            b.push_let(ValId(11), ValType::I32, Op::Bin(BinOp::I32LeU, ValId(1), ValId(10)));
            b.push_yield(&[ValId(11)]);
        }),
        read_footprints: vec![],
        write_footprints: vec![(MemId(0), OffsetRange { base: SliceBound::Arg(0), len: SliceBound::Arg(1) })],
        postcondition: Region::build(|b| {
            b.push_let(ValId(12), ValType::I32, Op::Bin(BinOp::I32Eq, ValId(2), ValId(1)));
            b.push_yield(&[ValId(12)]);
        }),
        sim_body: Some(Region::build(|b| {
            b.push_let(ValId(13), ValType::I32, Op::ConstI32(0x42));
            b.push_effect(EffectOp::Store { mem: MemId(0), addr: ValId(0), offset: 0, width: MemWidth::B1, val: ValId(13) });
            b.push_yield(&[ValId(1)]);
        })),
    };
    let mut bad_frame = ok_host.clone();
    bad_frame.id = HostCallId(1);
    bad_frame.sim_body = Some(Region::build(|b| {
        b.push_let(ValId(13), ValType::I32, Op::ConstI32(0x42));
        b.push_effect(EffectOp::Store { mem: MemId(0), addr: ValId(0), offset: 8, width: MemWidth::B1, val: ValId(13) });
        b.push_yield(&[ValId(1)]);
    }));
    m.host_contracts = vec![ok_host, bad_frame];
    let reg = StratumRegistry::new();
    let heap = HeapState::from_module(&m, 5000).unwrap();

    let call = |hid: HostCallId, ptr: i32, len: i32| {
        let r = Region::build(|b| {
            b.push_let(ValId(0), ValType::I32, Op::ConstI32(ptr));
            b.push_let(ValId(1), ValType::I32, Op::ConstI32(len));
            b.push_call(&[(ValId(2), ValType::I32)], CallTarget::Host(hid), &[ValId(0), ValId(1)]);
            b.push_yield(&[ValId(2)]);
        });
        eval_region(&m, &reg, &r, &[], heap.clone())
    };
    assert_eq!(call(HostCallId(0), 16, 4).unwrap().0, vec![Val::I32(4)]);
    assert_eq!(call(HostCallId(0), 16, 8), Err(TrapCode::HostContractViolation));
    assert_eq!(call(HostCallId(0), 65535, 4), Err(TrapCode::OutOfBoundsMem));
    assert_eq!(call(HostCallId(1), 16, 4), Err(TrapCode::HostContractViolation));
}

#[test]
fn test_stratum_registry_gates_and_lowering() {
    let mut reg = StratumRegistry::new();
    let inc_body = Region::build(|b| {
        b.push_let(ValId(1), ValType::I32, Op::ConstI32(1));
        b.push_let(ValId(2), ValType::I32, Op::Bin(BinOp::I32Add, ValId(0), ValId(1)));
        b.push_yield(&[ValId(2)]);
    });
    let op1 = StratumOp {
        id: StratumId(1),
        name: "inc".into(),
        layer: 1,
        params: vec![(ValId(0), ValType::I32)],
        results: vec![ValType::I32],
        body: inc_body.clone(),
        docstring: "x + 1".into(),
    };
    let mut bad_l0 = op1.clone();
    bad_l0.layer = 0;
    assert_eq!(reg.register_candidate_op(bad_l0), Err(RegistryError::InvalidLayerZero));

    let law = Law {
        name: "inc_ok".into(),
        kind: LawKind::Algebraic,
        params: vec![(ValId(0), ValType::I32)],
        precondition: Region::empty(),
        lhs: inc_body.clone(),
        rhs: inc_body,
        proof_digest: [1u8; 32],
    };
    assert_eq!(reg.promote_stratum(Stratum { op: op1.clone(), laws: LawList::empty() }), Err(RegistryError::MissingProvedLaw));
    let mut bad_digest = law.clone();
    bad_digest.proof_digest = [0u8; 32];
    assert_eq!(reg.promote_stratum(Stratum { op: op1.clone(), laws: LawList::single(bad_digest) }), Err(RegistryError::EmptyProofDigest));

    reg.promote_stratum(Stratum { op: op1, laws: LawList::single(law.clone()) }).unwrap();

    let bad_layer = StratumOp {
        id: StratumId(2),
        name: "bad_inc2".into(),
        layer: 1,
        params: vec![(ValId(0), ValType::I32)],
        results: vec![ValType::I32],
        body: Region::build(|b| {
            b.push_call(&[(ValId(1), ValType::I32)], CallTarget::Stratum(StratumId(1)), &[ValId(0)]);
            b.push_yield(&[ValId(1)]);
        }),
        docstring: "".into(),
    };
    assert_eq!(
        reg.register_candidate_op(bad_layer.clone()),
        Err(RegistryError::NonAcyclicLayer { caller_layer: 1, callee: StratumId(1), callee_layer: 1 })
    );

    let mut good_l2 = bad_layer;
    good_l2.layer = 2;
    good_l2.name = "inc2".into();
    good_l2.body = Region::build(|b| {
        b.push_call(&[(ValId(1), ValType::I32)], CallTarget::Stratum(StratumId(1)), &[ValId(0)]);
        b.push_call(&[(ValId(2), ValType::I32)], CallTarget::Stratum(StratumId(1)), &[ValId(1)]);
        b.push_yield(&[ValId(2)]);
    });
    reg.promote_stratum(Stratum { op: good_l2, laws: LawList::single(law) }).unwrap();

    let call_l2 = Region::build(|b| {
        b.push_call(&[(ValId(1), ValType::I32)], CallTarget::Stratum(StratumId(2)), &[ValId(0)]);
        b.push_yield(&[ValId(1)]);
    });
    let mut next = 10;
    let lowered = reg.lower_region_to_layer0(&call_l2, &mut next).unwrap();
    let m = Module::default();
    let heap = HeapState::from_module(&m, 5000).unwrap();
    assert_eq!(
        eval_region(&m, &reg, &call_l2, &[(ValId(0), Val::I32(41))], heap.clone()).unwrap().0,
        eval_region(&m, &reg, &lowered, &[(ValId(0), Val::I32(41))], heap).unwrap().0
    );

    let spill_op = StratumOp {
        id: StratumId(3),
        name: "inc3_spill".into(),
        layer: 1,
        params: vec![],
        results: vec![],
        body: Region::empty(),
        docstring: String::new(),
    };
    let spill_law = Law {
        name: "spill_ok".into(),
        kind: LawKind::Algebraic,
        params: vec![],
        precondition: Region::empty(),
        lhs: Region::empty(),
        rhs: Region::empty(),
        proof_digest: [0x33; 32],
    };
    reg.promote_stratum(Stratum { op: spill_op, laws: LawList::single(spill_law) }).unwrap();
    assert_eq!(reg.promoted().len(), 3);
    assert!(reg.get_stratum(StratumId(1)).is_some());
    assert!(reg.get_stratum(StratumId(2)).is_some());
    assert!(reg.get_stratum(StratumId(3)).is_some());
}

proptest! {
    #[test]
    fn prop_twos_complement_and_memory_non_interference(a: i32, b: i32, c: i64, d: i64, addr in 0u32..4096u32, byte_val: u8) {
        let m = Module {
            memories: vec![
                MemoryDef { id: MemId(0), min_pages: 1, max_pages: Some(1), init_data: vec![] },
                MemoryDef { id: MemId(1), min_pages: 1, max_pages: Some(1), init_data: vec![(0, vec![0x3c; 4096])] },
            ],
            ..Module::default()
        };
        let reg = StratumRegistry::new();
        let heap = HeapState::from_module(&m, 10_000).unwrap();
        let r = Region::build(|rb| {
            rb.push_let(ValId(10), ValType::I32, Op::Bin(BinOp::I32Add, ValId(0), ValId(1)));
            rb.push_let(ValId(11), ValType::I32, Op::Bin(BinOp::I32Rotl, ValId(0), ValId(1)));
            rb.push_let(ValId(12), ValType::I64, Op::Bin(BinOp::I64Mul, ValId(2), ValId(3)));
            rb.push_let(ValId(13), ValType::I64, Op::Bin(BinOp::I64ShrS, ValId(2), ValId(3)));
            rb.push_effect(EffectOp::Store { mem: MemId(0), addr: ValId(4), offset: 0, width: MemWidth::B1, val: ValId(5) });
            rb.push_let(ValId(14), ValType::I32, Op::Load { mem: MemId(0), addr: ValId(4), offset: 0, width: MemWidth::B1, signed: false, result_ty: ValType::I32 });
            rb.push_yield(&[ValId(10), ValId(11), ValId(12), ValId(13), ValId(14)]);
        });
        let bindings = vec![
            (ValId(0), Val::I32(a)),
            (ValId(1), Val::I32(b)),
            (ValId(2), Val::I64(c)),
            (ValId(3), Val::I64(d)),
            (ValId(4), Val::I32(addr as i32)),
            (ValId(5), Val::I32(byte_val as i32)),
        ];
        let (vals, out_heap) = eval_region(&m, &reg, &r, &bindings, heap).unwrap();
        prop_assert_eq!(vals[0], Val::I32(a.wrapping_add(b)));
        prop_assert_eq!(vals[1], Val::I32((a as u32).rotate_left((b as u32) & 31) as i32));
        prop_assert_eq!(vals[2], Val::I64(c.wrapping_mul(d)));
        prop_assert_eq!(vals[3], Val::I64(c.wrapping_shr(d as u32)));
        prop_assert_eq!(vals[4], Val::I32(byte_val as i32));
        prop_assert!(out_heap.memory(MemId(1)).unwrap().bytes[..4096].iter().all(|&x| x == 0x3c));
    }
}

#[test]
fn test_adversarial_audit_regressions() {
    let mut reg = StratumRegistry::new();
    let pure_op = StratumOp {
        id: StratumId(10),
        name: "pure_id".into(),
        layer: 1,
        params: vec![(ValId(0), ValType::I32)],
        results: vec![ValType::I32],
        body: Region::yield_vals(&[ValId(0)]),
        docstring: String::new(),
    };
    let mut_op = StratumOp {
        id: StratumId(11),
        name: "mut_store".into(),
        layer: 1,
        params: vec![(ValId(0), ValType::I32)],
        results: vec![ValType::I32],
        body: Region::build(|b| {
            b.push_effect(EffectOp::Store {
                mem: MemId(0),
                addr: ValId(0),
                offset: 0,
                width: MemWidth::B1,
                val: ValId(0),
            });
            b.push_yield(&[ValId(0)]);
        }),
        docstring: String::new(),
    };
    let triv_law = |sid: u32| {
        let call_it = Region::build(|b| {
            b.push_call(&[(ValId(1), ValType::I32)], CallTarget::Stratum(StratumId(sid)), &[ValId(0)]);
            b.push_yield(&[ValId(1)]);
        });
        Law {
            name: "id".into(),
            kind: LawKind::Algebraic,
            params: vec![(ValId(0), ValType::I32)],
            precondition: Region::empty(),
            lhs: call_it.clone(),
            rhs: call_it,
            proof_digest: [0x55; 32],
        }
    };
    reg.promote_stratum(Stratum { op: pure_op, laws: LawList::single(triv_law(10)) }).unwrap();
    reg.promote_stratum(Stratum { op: mut_op, laws: LawList::single(triv_law(11)) }).unwrap();

    let call_pure = Region::build(|b| {
        b.push_call(&[(ValId(1), ValType::I32)], CallTarget::Stratum(StratumId(10)), &[ValId(0)]);
        b.push_yield(&[ValId(1)]);
    });
    let call_mut = Region::build(|b| {
        b.push_call(&[(ValId(1), ValType::I32)], CallTarget::Stratum(StratumId(11)), &[ValId(0)]);
        b.push_yield(&[ValId(1)]);
    });
    assert!(!validate_read_only(&call_pure));
    assert!(!validate_read_only(&call_mut));
    assert!(validate_read_only_with_registry(&call_pure, &reg));
    assert!(!validate_read_only_with_registry(&call_mut, &reg));

    let cand_op = StratumOp {
        id: StratumId(20),
        name: "cand_only".into(),
        layer: 1,
        params: vec![],
        results: vec![ValType::I32],
        body: Region::build(|b| {
            b.push_let(ValId(0), ValType::I32, Op::ConstI32(7));
            b.push_yield(&[ValId(0)]);
        }),
        docstring: String::new(),
    };
    reg.register_candidate_op(cand_op).unwrap();
    let bad_caller = StratumOp {
        id: StratumId(21),
        name: "calls_unprom".into(),
        layer: 2,
        params: vec![],
        results: vec![ValType::I32],
        body: Region::build(|b| {
            b.push_call(&[(ValId(0), ValType::I32)], CallTarget::Stratum(StratumId(20)), &[]);
            b.push_yield(&[ValId(0)]);
        }),
        docstring: String::new(),
    };
    let empty_law = Law {
        name: "l".into(),
        kind: LawKind::Algebraic,
        params: vec![],
        precondition: Region::empty(),
        lhs: Region::empty(),
        rhs: Region::empty(),
        proof_digest: [0x11; 32],
    };
    assert_eq!(
        reg.promote_stratum(Stratum { op: bad_caller, laws: LawList::single(empty_law.clone()) }),
        Err(RegistryError::UnknownStratum(StratumId(20)))
    );
    let dup_cand_name = StratumOp {
        id: StratumId(22),
        name: "cand_only".into(),
        layer: 1,
        params: vec![],
        results: vec![],
        body: Region::empty(),
        docstring: String::new(),
    };
    assert_eq!(
        reg.promote_stratum(Stratum { op: dup_cand_name, laws: LawList::single(empty_law) }),
        Err(RegistryError::DuplicateName)
    );

    let one_reg = Region::build(|b| {
        b.push_let(ValId(2), ValType::I32, Op::ConstI32(1));
        b.push_yield(&[ValId(2)]);
    });
    let zero_u64 = Region::build(|b| {
        b.push_let(ValId(2), ValType::I64, Op::ConstI64(0));
        b.push_yield(&[ValId(2)]);
    });
    let ret_body = Region::build(|b| b.push_return(&[ValId(1)]));
    let ret_body_loop = Region::invariant_loop(
        &[ValId(0)],
        &[(ValId(1), ValType::I32)],
        &one_reg,
        &one_reg,
        &zero_u64,
        &ret_body,
    );
    assert_eq!(
        split_invariant_loop(vec![(ValId(0), ValType::I32)], None, &ret_body_loop, one_reg.clone()),
        Err(VcError::UnstructuredControlFlow)
    );

    let trap_cond = Region::build(|b| {
        b.push_let(ValId(2), ValType::I32, Op::ConstI32(0));
        b.push_let(ValId(3), ValType::I32, Op::Bin(BinOp::I32DivU, ValId(1), ValId(2)));
        b.push_yield(&[ValId(3)]);
    });
    let id_body = Region::yield_vals(&[ValId(1)]);
    let trap_cond_loop = Region::invariant_loop(
        &[ValId(0)],
        &[(ValId(1), ValType::I32)],
        &trap_cond,
        &one_reg,
        &zero_u64,
        &id_body,
    );
    let vcs = split_invariant_loop(vec![(ValId(0), ValType::I32)], None, &trap_cond_loop, one_reg).unwrap();
    let m = Module::default();
    let heap = HeapState::from_module(&m, 1000).unwrap();
    assert_eq!(
        eval_vc(&m, &reg, &vcs.preservation, &[Val::I32(5), Val::I32(5)], heap),
        VcEvalResult::Violated(Some(TrapCode::DivByZero))
    );

    let free_bin = Region::build(|b| {
        b.push_let(ValId(1), ValType::I32, Op::ConstI32(10));
        b.push_let(ValId(2), ValType::I32, Op::Bin(BinOp::I32Add, ValId(1), ValId(5)));
        b.push_yield(&[ValId(2)]);
    });
    let mut nf = 0u32;
    let remapped = remap_region_vals(&free_bin, &[], &mut nf);
    let h2 = HeapState::from_module(&m, 1000).unwrap();
    assert_eq!(
        eval_region(&m, &reg, &remapped, &[(ValId(5), Val::I32(32))], h2).unwrap().0,
        vec![Val::I32(42)]
    );

    let mut gm = mod_with_mem(1, Some(1));
    gm.globals.push(GlobalDef { id: GlobalId(0), ty: ValType::I32, mutable: false, init: Val::I32(9) });
    let shadow_inner = Region::build(|b| {
        b.push_let(ValId(0), ValType::I32, Op::ConstI32(100));
        b.push_yield(&[ValId(0)]);
    });
    let shadow_reg = Region::build(|b| {
        b.push_subregion(&[(ValId(2), ValType::I32)], &shadow_inner);
        b.push_let(ValId(3), ValType::I32, Op::Bin(BinOp::I32Add, ValId(0), ValId(2)));
        b.push_yield(&[ValId(3)]);
    });
    let gh = HeapState::from_module(&gm, 1000).unwrap();
    assert_eq!(
        eval_region(&gm, &reg, &shadow_reg, &[(ValId(0), Val::I32(7))], gh.clone()).unwrap().0,
        vec![Val::I32(107)]
    );

    let immut_set = Region::build(|b| {
        b.push_let(ValId(0), ValType::I32, Op::ConstI32(1));
        b.push_effect(EffectOp::GlobalSet { id: GlobalId(0), val: ValId(0) });
        b.push_yield(&[]);
    });
    assert_eq!(eval_region(&gm, &reg, &immut_set, &[], gh.clone()), Err(TrapCode::Unreachable));

    let fill_len0_oob = Region::build(|b| {
        b.push_let(ValId(0), ValType::I32, Op::ConstI32((WASM_PAGE_SIZE + 1) as i32));
        b.push_let(ValId(1), ValType::I32, Op::ConstI32(0));
        b.push_effect(EffectOp::MemoryFill { mem: MemId(0), dst: ValId(0), val: ValId(1), len: ValId(1) });
        b.push_yield(&[]);
    });
    assert_eq!(eval_region(&gm, &reg, &fill_len0_oob, &[], gh), Err(TrapCode::OutOfBoundsMem));
}

#[test]
fn test_ir_slot_lossless_round_trip() {
    assert_eq!(core::mem::size_of::<IrSlot>(), 24);
    assert_eq!(core::mem::align_of::<IrSlot>(), 4);

    assert_eq!(IrSlot::val(ValId(42)).to_val(), Some(ValId(42)));
    for ty in [ValType::I32, ValType::I64] {
        assert_eq!(IrSlot::var(ValId(7), ty).to_var(), Some((ValId(7), ty)));
        assert_eq!(IrSlot::ty(ty).to_ty(), Some(ty));
    }

    let unops = [
        UnOp::I32Eqz,
        UnOp::I64Eqz,
        UnOp::I32Clz,
        UnOp::I32Ctz,
        UnOp::I32Popcnt,
        UnOp::I64Clz,
        UnOp::I64Ctz,
        UnOp::I64Popcnt,
        UnOp::I32WrapI64,
        UnOp::I64ExtendI32S,
        UnOp::I64ExtendI32U,
        UnOp::I32Extend8S,
        UnOp::I32Extend16S,
        UnOp::I64Extend8S,
        UnOp::I64Extend16S,
        UnOp::I64Extend32S,
    ];
    for (idx, u) in unops.iter().copied().enumerate() {
        let s = Stmt::Let { dst: ValId(idx as u32), ty: u.output_ty(), op: Op::Un(u, ValId(99)) };
        assert_eq!(IrSlot::from_stmt(s).to_stmt(), Some(s));
    }

    let binops = [
        BinOp::I32Eq,
        BinOp::I32Ne,
        BinOp::I32LtS,
        BinOp::I32LtU,
        BinOp::I32GtS,
        BinOp::I32GtU,
        BinOp::I32LeS,
        BinOp::I32LeU,
        BinOp::I32GeS,
        BinOp::I32GeU,
        BinOp::I64Eq,
        BinOp::I64Ne,
        BinOp::I64LtS,
        BinOp::I64LtU,
        BinOp::I64GtS,
        BinOp::I64GtU,
        BinOp::I64LeS,
        BinOp::I64LeU,
        BinOp::I64GeS,
        BinOp::I64GeU,
        BinOp::I32Add,
        BinOp::I32Sub,
        BinOp::I32Mul,
        BinOp::I32DivS,
        BinOp::I32DivU,
        BinOp::I32RemS,
        BinOp::I32RemU,
        BinOp::I64Add,
        BinOp::I64Sub,
        BinOp::I64Mul,
        BinOp::I64DivS,
        BinOp::I64DivU,
        BinOp::I64RemS,
        BinOp::I64RemU,
        BinOp::I32And,
        BinOp::I32Or,
        BinOp::I32Xor,
        BinOp::I32Shl,
        BinOp::I32ShrS,
        BinOp::I32ShrU,
        BinOp::I32Rotl,
        BinOp::I32Rotr,
        BinOp::I64And,
        BinOp::I64Or,
        BinOp::I64Xor,
        BinOp::I64Shl,
        BinOp::I64ShrS,
        BinOp::I64ShrU,
        BinOp::I64Rotl,
        BinOp::I64Rotr,
    ];
    for (idx, b) in binops.iter().copied().enumerate() {
        let s = Stmt::Let {
            dst: ValId(idx as u32),
            ty: b.output_ty(),
            op: Op::Bin(b, ValId(1), ValId(2)),
        };
        assert_eq!(IrSlot::from_stmt(s).to_stmt(), Some(s));
    }

    for &i64_v in &[0i64, -1i64, i64::MIN, i64::MAX, 0x1234_5678_9abc_def0i64] {
        let s = Stmt::Let { dst: ValId(3), ty: ValType::I64, op: Op::ConstI64(i64_v) };
        assert_eq!(IrSlot::from_stmt(s).to_stmt(), Some(s));
    }
    for &i32_v in &[0i32, -1i32, i32::MIN, i32::MAX] {
        let s = Stmt::Let { dst: ValId(4), ty: ValType::I32, op: Op::ConstI32(i32_v) };
        assert_eq!(IrSlot::from_stmt(s).to_stmt(), Some(s));
    }
    for op in [
        Op::Copy(ValId(5)),
        Op::Select { cond: ValId(1), true_val: ValId(2), false_val: ValId(3) },
        Op::GlobalGet(GlobalId(7)),
        Op::MemorySize(MemId(2)),
        Op::MemoryGrow { mem: MemId(1), delta: ValId(8) },
    ] {
        let s = Stmt::Let { dst: ValId(9), ty: ValType::I32, op };
        assert_eq!(IrSlot::from_stmt(s).to_stmt(), Some(s));
    }
    for width in [MemWidth::B1, MemWidth::B2, MemWidth::B4, MemWidth::B8] {
        for signed in [false, true] {
            for ty in [ValType::I32, ValType::I64] {
                for result_ty in [ValType::I32, ValType::I64] {
                    let s = Stmt::Let {
                        dst: ValId(10),
                        ty,
                        op: Op::Load {
                            mem: MemId(3),
                            addr: ValId(11),
                            offset: 0x1234_5678,
                            width,
                            signed,
                            result_ty,
                        },
                    };
                    assert_eq!(IrSlot::from_stmt(s).to_stmt(), Some(s));
                }
            }
        }
        let eff = EffectOp::Store {
            mem: MemId(2),
            addr: ValId(3),
            offset: 64,
            width,
            val: ValId(4),
        };
        assert_eq!(IrSlot::from_stmt(Stmt::Effect(eff)).to_stmt(), Some(Stmt::Effect(eff)));
    }
    for trap in [
        TrapCode::DivByZero,
        TrapCode::IntOverflow,
        TrapCode::OutOfBoundsMem,
        TrapCode::OutOfFuel,
        TrapCode::HostContractViolation,
        TrapCode::Unreachable,
    ] {
        let s = Stmt::Effect(EffectOp::Trap(trap));
        assert_eq!(IrSlot::from_stmt(s).to_stmt(), Some(s));
    }
    for eff in [
        EffectOp::MemoryCopy {
            dst_mem: MemId(1),
            src_mem: MemId(2),
            dst: ValId(3),
            src: ValId(4),
            len: ValId(5),
        },
        EffectOp::MemoryFill { mem: MemId(3), dst: ValId(6), val: ValId(7), len: ValId(8) },
        EffectOp::GlobalSet { id: GlobalId(9), val: ValId(10) },
        EffectOp::Nop,
    ] {
        let s = Stmt::Effect(eff);
        assert_eq!(IrSlot::from_stmt(s).to_stmt(), Some(s));
    }
    let stmts = [
        Stmt::Region { results: Span { start: 1, len: 2 }, region: RegionNodeId(9) },
        Stmt::Call {
            results: Span { start: 1, len: 2 },
            target: CallTarget::Func(FuncId(3)),
            args: Span { start: 4, len: 5 },
        },
        Stmt::Call {
            results: Span { start: 0, len: 1 },
            target: CallTarget::Host(HostCallId(7)),
            args: Span { start: 2, len: 3 },
        },
        Stmt::Call {
            results: Span::EMPTY,
            target: CallTarget::Stratum(StratumId(11)),
            args: Span { start: 1, len: 1 },
        },
        Stmt::Yield(Span { start: 2, len: 3 }),
        Stmt::Break { depth: 2, cond: None, values: Span { start: 1, len: 4 } },
        Stmt::Break { depth: 3, cond: Some(ValId(8)), values: Span::EMPTY },
        Stmt::Continue { depth: 0, cond: None, values: Span::EMPTY },
        Stmt::Continue { depth: 1, cond: Some(ValId(12)), values: Span { start: 5, len: 2 } },
        Stmt::Return(Span { start: 6, len: 1 }),
    ];
    for s in stmts {
        assert_eq!(IrSlot::from_stmt(s).to_stmt(), Some(s));
    }
    let nodes = [
        RegionNode::Block(Span { start: 3, len: 7 }),
        RegionNode::IfElse {
            cond: ValId(1),
            then_region: RegionNodeId(2),
            else_region: RegionNodeId(3),
            results: Span { start: 4, len: 5 },
        },
        RegionNode::BoundedLoop {
            max_iters: 100,
            init_vars: Span { start: 1, len: 2 },
            state_vars: Span { start: 3, len: 4 },
            body: RegionNodeId(5),
        },
        RegionNode::InvariantLoop {
            init_vars: Span { start: 1, len: 2 },
            state_vars: Span { start: 3, len: 4 },
            cond: RegionNodeId(5),
            invariant_pred: RegionNodeId(6),
            fuel_measure: RegionNodeId(7),
            body: RegionNodeId(8),
        },
    ];
    for n in nodes {
        let mut pool = SlotPool::new();
        let id = pool.push_node(n);
        let reg = Region { pool, root: n };
        assert_eq!(reg.try_node(id), Some(n));
    }

    // Exercise Env lexical shadowing across inline (<16) and spill (>=16) ValIds.
    let m = Module::default();
    let r = StratumRegistry::new();
    let shadow_reg = Region::build(|b| {
        b.push_let(ValId(0), ValType::I32, Op::ConstI32(10));
        b.push_let(ValId(20), ValType::I64, Op::ConstI64(-7));
        let inner = Region::build(|ib| {
            ib.push_let(ValId(0), ValType::I64, Op::ConstI64(99));
            ib.push_let(ValId(20), ValType::I32, Op::ConstI32(-3));
            ib.push_yield(&[ValId(0), ValId(20)]);
        });
        b.push_subregion(&[(ValId(1), ValType::I64), (ValId(2), ValType::I32)], &inner);
        b.push_yield(&[ValId(0), ValId(20), ValId(1), ValId(2)]);
    });
    let heap = HeapState::from_module(&m, 1000).unwrap();
    let (vals, _) = eval_region(&m, &r, &shadow_reg, &[], heap).unwrap();
    assert_eq!(vals, vec![Val::I32(10), Val::I64(-7), Val::I64(99), Val::I32(-3)]);
}

#[test]
fn test_registry_candidate_and_ro_store_spills() {
    let make_op = |id: u32, name: &str| StratumOp {
        id: StratumId(id),
        name: name.into(),
        layer: 1,
        params: Vec::new(),
        results: Vec::new(),
        body: Region::empty(),
        docstring: String::new(),
    };
    let make_stratum = |id: u32, name: &str| Stratum {
        op: make_op(id, name),
        laws: LawList::single(Law {
            name: format!("{name}_law"),
            kind: LawKind::Algebraic,
            params: Vec::new(),
            precondition: Region::empty(),
            lhs: Region::empty(),
            rhs: Region::empty(),
            proof_digest: [1u8; 32],
        }),
    };

    // Exercise inline CandidateStore remove at index 0 (with 2 elements) and index 1.
    let mut reg = StratumRegistry::new();
    assert_eq!(reg.register_candidate_op(make_op(1, "c1")), Ok(StratumId(1)));
    assert_eq!(reg.register_candidate_op(make_op(2, "c2")), Ok(StratumId(2)));
    assert_eq!(reg.promote_stratum(make_stratum(1, "c1")), Ok(StratumId(1)));
    assert_eq!(reg.candidates().len(), 1);
    assert_eq!(reg.candidates()[0].id, StratumId(2));
    assert_eq!(reg.register_candidate_op(make_op(3, "c3")), Ok(StratumId(3)));
    assert_eq!(reg.promote_stratum(make_stratum(3, "c3")), Ok(StratumId(3)));
    assert_eq!(reg.candidates().len(), 1);
    assert_eq!(reg.candidates()[0].id, StratumId(2));
    assert_eq!(reg.promote_stratum(make_stratum(2, "c2")), Ok(StratumId(2)));
    assert!(reg.candidates().is_empty());

    // Exercise CandidateStore spill (3rd+) and ReadOnlyIdStore spill (5th+), then spill removal.
    let mut reg2 = StratumRegistry::new();
    for id in 10..=14u32 {
        let name = format!("cand_{id}");
        assert_eq!(reg2.register_candidate_op(make_op(id, &name)), Ok(StratumId(id)));
    }
    assert_eq!(reg2.candidates().len(), 5);
    for id in 10..=14u32 {
        assert!(reg2.get_op(StratumId(id)).is_some());
        assert!(reg2.is_stratum_read_only(StratumId(id)));
    }
    assert_eq!(reg2.promote_stratum(make_stratum(12, "cand_12")), Ok(StratumId(12)));
    assert_eq!(reg2.candidates().len(), 4);
    assert_eq!(reg2.promoted().len(), 1);
    assert!(reg2.get_stratum(StratumId(12)).is_some());
    assert!(reg2.is_stratum_read_only(StratumId(12)));
    assert!(reg2.candidates().iter().all(|c| c.id != StratumId(12)));
}
