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
        let r = Region::Block(vec![
            Stmt::Let { dst: ValId(2), ty, op: Op::Bin(op, ValId(0), ValId(1)) },
            Stmt::Yield(vec![ValId(2)]),
        ]);
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
    let r = Region::Block(vec![
        Stmt::Let { dst: ValId(1), ty: ValType::I32, op: Op::Un(UnOp::I32Extend8S, ValId(0)) },
        Stmt::Let { dst: ValId(2), ty: ValType::I32, op: Op::Un(UnOp::I32Extend16S, ValId(0)) },
        Stmt::Let { dst: ValId(3), ty: ValType::I64, op: Op::Un(UnOp::I64ExtendI32U, ValId(0)) },
        Stmt::Let { dst: ValId(4), ty: ValType::I64, op: Op::Un(UnOp::I64Extend32S, ValId(3)) },
        Stmt::Let { dst: ValId(5), ty: ValType::I32, op: Op::Un(UnOp::I32Popcnt, ValId(0)) },
        Stmt::Let { dst: ValId(6), ty: ValType::I32, op: Op::Un(UnOp::I32Clz, ValId(0)) },
        Stmt::Let { dst: ValId(7), ty: ValType::I32, op: Op::Un(UnOp::I32Ctz, ValId(0)) },
        Stmt::Yield(vec![ValId(1), ValId(2), ValId(3), ValId(4), ValId(5), ValId(6), ValId(7)]),
    ]);
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

    // Little-endian signed/unsigned loads + effective-address u32 overflow check
    let r = Region::Block(vec![
        Stmt::Let { dst: ValId(0), ty: ValType::I32, op: Op::ConstI32(0) },
        Stmt::Let { dst: ValId(1), ty: ValType::I32, op: Op::Load { mem: MemId(0), addr: ValId(0), offset: 0, width: MemWidth::B1, signed: true, result_ty: ValType::I32 } },
        Stmt::Let { dst: ValId(2), ty: ValType::I32, op: Op::Load { mem: MemId(0), addr: ValId(0), offset: 0, width: MemWidth::B1, signed: false, result_ty: ValType::I32 } },
        Stmt::Let { dst: ValId(3), ty: ValType::I32, op: Op::Load { mem: MemId(0), addr: ValId(0), offset: 0, width: MemWidth::B4, signed: false, result_ty: ValType::I32 } },
        Stmt::Let { dst: ValId(4), ty: ValType::I64, op: Op::ConstI64(0x0102_0304_0506_0708) },
        Stmt::Effect(EffectOp::Store { mem: MemId(0), addr: ValId(0), offset: 16, width: MemWidth::B8, val: ValId(4) }),
        Stmt::Let { dst: ValId(5), ty: ValType::I64, op: Op::Load { mem: MemId(0), addr: ValId(0), offset: 16, width: MemWidth::B8, signed: false, result_ty: ValType::I64 } },
        Stmt::Let { dst: ValId(6), ty: ValType::I32, op: Op::ConstI32(1) },
        Stmt::Let { dst: ValId(7), ty: ValType::I32, op: Op::MemoryGrow { mem: MemId(0), delta: ValId(6) } },
        Stmt::Let { dst: ValId(8), ty: ValType::I32, op: Op::MemorySize(MemId(0)) },
        Stmt::Let { dst: ValId(9), ty: ValType::I32, op: Op::MemoryGrow { mem: MemId(0), delta: ValId(6) } },
        Stmt::Yield(vec![ValId(1), ValId(2), ValId(3), ValId(5), ValId(7), ValId(8), ValId(9)]),
    ]);
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
    // MemId(1) untouched by MemId(0) ops
    assert_eq!(&heap2.memory(MemId(1)).unwrap().bytes[..8], &[0xaa; 8]);

    // Overlapping intra-memory copy & cross-memory copy & fill
    heap2.memory_mut(MemId(0)).unwrap().fill(32, 0x5a, 4).unwrap();
    heap2.memory_copy(MemId(0), MemId(0), 34, 32, 4).unwrap();
    assert_eq!(&heap2.memory(MemId(0)).unwrap().bytes[32..38], &[0x5a; 6]);
    heap2.memory_copy(MemId(1), MemId(0), 16, 16, 8).unwrap();
    assert_eq!(&heap2.memory(MemId(1)).unwrap().bytes[16..24], &0x0102_0304_0506_0708u64.to_le_bytes());

    // Effective address u32::MAX + offset 1 must trap OutOfBoundsMem, never wrap to 0
    let oob = Region::Block(vec![
        Stmt::Let { dst: ValId(0), ty: ValType::I32, op: Op::ConstI32(-1) },
        Stmt::Let { dst: ValId(1), ty: ValType::I32, op: Op::Load { mem: MemId(0), addr: ValId(0), offset: 1, width: MemWidth::B1, signed: false, result_ty: ValType::I32 } },
        Stmt::Yield(vec![ValId(1)]),
    ]);
    assert_eq!(eval_region(&m, &reg, &oob, &[], heap2), Err(TrapCode::OutOfBoundsMem));
}

#[test]
fn test_structured_control_flow() {
    let (m, reg) = empty_mod_reg();
    let heap = HeapState::from_module(&m, 5000).unwrap();

    // Nested Block + conditional Break(depth 0 and depth 1) + IfElse
    let nested = Region::Block(vec![
        Stmt::Let { dst: ValId(1), ty: ValType::I32, op: Op::ConstI32(10) },
        Stmt::Let { dst: ValId(2), ty: ValType::I32, op: Op::ConstI32(99) },
        Stmt::Region {
            results: vec![(ValId(3), ValType::I32)],
            region: Region::Block(vec![
                Stmt::Break { depth: 1, cond: Some(ValId(0)), values: vec![ValId(2)] },
                Stmt::Break { depth: 0, cond: None, values: vec![ValId(1)] },
            ]),
        },
        Stmt::Yield(vec![ValId(3)]),
    ]);
    assert_eq!(eval_region(&m, &reg, &nested, &[(ValId(0), Val::I32(1))], heap.clone()).unwrap().0, vec![Val::I32(99)]);
    assert_eq!(eval_region(&m, &reg, &nested, &[(ValId(0), Val::I32(0))], heap.clone()).unwrap().0, vec![Val::I32(10)]);

    // BoundedLoop: sum 1..=n using Continue, normal exit, and OutOfFuel on max_iters
    let make_loop = |max_iters: u32| Region::Block(vec![
        Stmt::Let { dst: ValId(1), ty: ValType::I32, op: Op::ConstI32(0) },
        Stmt::Region {
            results: vec![(ValId(10), ValType::I32)],
            region: Region::BoundedLoop {
                max_iters,
                init_vars: vec![ValId(0), ValId(1)],
                state_vars: vec![(ValId(2), ValType::I32), (ValId(3), ValType::I32)],
                body: Box::new(Region::Block(vec![
                    Stmt::Let { dst: ValId(4), ty: ValType::I32, op: Op::ConstI32(0) },
                    Stmt::Let { dst: ValId(5), ty: ValType::I32, op: Op::Bin(BinOp::I32GtS, ValId(2), ValId(4)) },
                    Stmt::Region {
                        results: vec![],
                        region: Region::IfElse {
                            cond: ValId(5),
                            then_region: Box::new(Region::Block(vec![
                                Stmt::Let { dst: ValId(6), ty: ValType::I32, op: Op::Bin(BinOp::I32Add, ValId(3), ValId(2)) },
                                Stmt::Let { dst: ValId(7), ty: ValType::I32, op: Op::ConstI32(1) },
                                Stmt::Let { dst: ValId(8), ty: ValType::I32, op: Op::Bin(BinOp::I32Sub, ValId(2), ValId(7)) },
                                Stmt::Continue { depth: 1, cond: None, values: vec![ValId(8), ValId(6)] },
                            ])),
                            else_region: Box::new(Region::Block(vec![])),
                            results: vec![],
                        },
                    },
                    Stmt::Yield(vec![ValId(3)]),
                ])),
            },
        },
        Stmt::Yield(vec![ValId(10)]),
    ]);
    assert_eq!(eval_region(&m, &reg, &make_loop(10), &[(ValId(0), Val::I32(5))], heap.clone()).unwrap().0, vec![Val::I32(15)]);
    assert_eq!(eval_region(&m, &reg, &make_loop(4), &[(ValId(0), Val::I32(5))], heap.clone()), Err(TrapCode::OutOfFuel));

    // Return unwinds multiple regions cleanly
    let ret = Region::Block(vec![
        Stmt::Let { dst: ValId(0), ty: ValType::I32, op: Op::ConstI32(42) },
        Stmt::Region { results: vec![], region: Region::Block(vec![Stmt::Return(vec![ValId(0)])]) },
    ]);
    assert_eq!(eval_region(&m, &reg, &ret, &[], heap).unwrap().0, vec![Val::I32(42)]);
}

#[test]
fn test_vc_splitter_soundness_and_failure_modes() {
    let (m, reg) = empty_mod_reg();
    let heap = HeapState::from_module(&m, 10_000).unwrap();

    // Countdown loop: state = (i, acc), init = (n, 0), inv: (i >= 0) && (acc >= 0), fuel: (u64)i
    let make_inv_loop = |bad_inv: bool, bad_fuel: bool| {
        let i = ValId(10);
        let acc = ValId(11);
        let cond = Region::Block(vec![
            Stmt::Let { dst: ValId(20), ty: ValType::I32, op: Op::ConstI32(0) },
            Stmt::Let { dst: ValId(21), ty: ValType::I32, op: Op::Bin(BinOp::I32GtS, i, ValId(20)) },
            Stmt::Yield(vec![ValId(21)]),
        ]);
        let invariant_pred = if bad_inv {
            Region::Block(vec![
                Stmt::Let { dst: ValId(30), ty: ValType::I32, op: Op::ConstI32(5) },
                Stmt::Let { dst: ValId(31), ty: ValType::I32, op: Op::Bin(BinOp::I32LtS, acc, ValId(30)) },
                Stmt::Yield(vec![ValId(31)]),
            ])
        } else {
            Region::Block(vec![
                Stmt::Let { dst: ValId(30), ty: ValType::I32, op: Op::ConstI32(0) },
                Stmt::Let { dst: ValId(31), ty: ValType::I32, op: Op::Bin(BinOp::I32GeS, i, ValId(30)) },
                Stmt::Let { dst: ValId(32), ty: ValType::I32, op: Op::Bin(BinOp::I32GeS, acc, ValId(30)) },
                Stmt::Let { dst: ValId(33), ty: ValType::I32, op: Op::Bin(BinOp::I32And, ValId(31), ValId(32)) },
                Stmt::Yield(vec![ValId(33)]),
            ])
        };
        let fuel_measure = if bad_fuel {
            Region::Block(vec![
                Stmt::Let { dst: ValId(40), ty: ValType::I64, op: Op::ConstI64(1) },
                Stmt::Yield(vec![ValId(40)]),
            ])
        } else {
            Region::Block(vec![
                Stmt::Let { dst: ValId(40), ty: ValType::I64, op: Op::Un(UnOp::I64ExtendI32U, i) },
                Stmt::Yield(vec![ValId(40)]),
            ])
        };
        let body = Region::Block(vec![
            Stmt::Let { dst: ValId(50), ty: ValType::I32, op: Op::ConstI32(1) },
            Stmt::Let { dst: ValId(51), ty: ValType::I32, op: Op::Bin(BinOp::I32Sub, i, ValId(50)) },
            Stmt::Let { dst: ValId(52), ty: ValType::I32, op: Op::Bin(BinOp::I32Add, acc, ValId(50)) },
            Stmt::Yield(vec![ValId(51), ValId(52)]),
        ]);
        Region::InvariantLoop {
            init_vars: vec![ValId(0), ValId(1)],
            state_vars: vec![(i, ValType::I32), (acc, ValType::I32)],
            cond: Box::new(cond),
            invariant_pred: Box::new(invariant_pred),
            fuel_measure: Box::new(fuel_measure),
            body: Box::new(body),
        }
    };

    let pre = Region::Block(vec![
        Stmt::Let { dst: ValId(60), ty: ValType::I32, op: Op::ConstI32(0) },
        Stmt::Let { dst: ValId(61), ty: ValType::I32, op: Op::Bin(BinOp::I32GeS, ValId(0), ValId(60)) },
        Stmt::Let { dst: ValId(62), ty: ValType::I32, op: Op::Bin(BinOp::I32Eq, ValId(1), ValId(60)) },
        Stmt::Let { dst: ValId(63), ty: ValType::I32, op: Op::Bin(BinOp::I32And, ValId(61), ValId(62)) },
        Stmt::Yield(vec![ValId(63)]),
    ]);
    let post = Region::Block(vec![
        Stmt::Let { dst: ValId(70), ty: ValType::I32, op: Op::ConstI32(0) },
        Stmt::Let { dst: ValId(71), ty: ValType::I32, op: Op::Bin(BinOp::I32Eq, ValId(10), ValId(70)) },
        Stmt::Yield(vec![ValId(71)]),
    ]);

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
        id: HostCallId(0), module_name: "env".into(), field_name: "poke".into(),
        params: vec![(ValId(0), ValType::I32), (ValId(1), ValType::I32)],
        results: vec![(ValId(2), ValType::I32)],
        precondition: Region::Block(vec![
            Stmt::Let { dst: ValId(10), ty: ValType::I32, op: Op::ConstI32(4) },
            Stmt::Let { dst: ValId(11), ty: ValType::I32, op: Op::Bin(BinOp::I32LeU, ValId(1), ValId(10)) },
            Stmt::Yield(vec![ValId(11)]),
        ]),
        read_footprints: vec![],
        write_footprints: vec![(MemId(0), OffsetRange { base: SliceBound::Arg(0), len: SliceBound::Arg(1) })],
        postcondition: Region::Block(vec![
            Stmt::Let { dst: ValId(12), ty: ValType::I32, op: Op::Bin(BinOp::I32Eq, ValId(2), ValId(1)) },
            Stmt::Yield(vec![ValId(12)]),
        ]),
        sim_body: Some(Region::Block(vec![
            Stmt::Let { dst: ValId(13), ty: ValType::I32, op: Op::ConstI32(0x42) },
            Stmt::Effect(EffectOp::Store { mem: MemId(0), addr: ValId(0), offset: 0, width: MemWidth::B1, val: ValId(13) }),
            Stmt::Yield(vec![ValId(1)]),
        ])),
    };
    let mut bad_frame = ok_host.clone();
    bad_frame.id = HostCallId(1);
    bad_frame.sim_body = Some(Region::Block(vec![
        Stmt::Let { dst: ValId(13), ty: ValType::I32, op: Op::ConstI32(0x42) },
        Stmt::Effect(EffectOp::Store { mem: MemId(0), addr: ValId(0), offset: 8, width: MemWidth::B1, val: ValId(13) }),
        Stmt::Yield(vec![ValId(1)]),
    ]));
    m.host_contracts = vec![ok_host, bad_frame];
    let reg = StratumRegistry::new();
    let heap = HeapState::from_module(&m, 5000).unwrap();

    let call = |hid: HostCallId, ptr: i32, len: i32| {
        let r = Region::Block(vec![
            Stmt::Let { dst: ValId(0), ty: ValType::I32, op: Op::ConstI32(ptr) },
            Stmt::Let { dst: ValId(1), ty: ValType::I32, op: Op::ConstI32(len) },
            Stmt::Call { results: vec![(ValId(2), ValType::I32)], target: CallTarget::Host(hid), args: vec![ValId(0), ValId(1)] },
            Stmt::Yield(vec![ValId(2)]),
        ]);
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
    let inc_body = Region::Block(vec![
        Stmt::Let { dst: ValId(1), ty: ValType::I32, op: Op::ConstI32(1) },
        Stmt::Let { dst: ValId(2), ty: ValType::I32, op: Op::Bin(BinOp::I32Add, ValId(0), ValId(1)) },
        Stmt::Yield(vec![ValId(2)]),
    ]);
    let op1 = StratumOp {
        id: StratumId(1), name: "inc".into(), layer: 1,
        params: vec![(ValId(0), ValType::I32)], results: vec![ValType::I32], body: inc_body.clone(), docstring: "x + 1".into(),
    };
    let mut bad_l0 = op1.clone();
    bad_l0.layer = 0;
    assert_eq!(reg.register_candidate_op(bad_l0), Err(RegistryError::InvalidLayerZero));

    let law = Law {
        name: "inc_ok".into(), kind: LawKind::Algebraic, params: vec![(ValId(0), ValType::I32)], precondition: None,
        lhs: inc_body.clone(), rhs: inc_body, proof_digest: [1u8; 32],
    };
    assert_eq!(reg.promote_stratum(Stratum { op: op1.clone(), laws: vec![] }), Err(RegistryError::MissingProvedLaw));
    let mut bad_digest = law.clone();
    bad_digest.proof_digest = [0u8; 32];
    assert_eq!(reg.promote_stratum(Stratum { op: op1.clone(), laws: vec![bad_digest] }), Err(RegistryError::EmptyProofDigest));

    reg.promote_stratum(Stratum { op: op1, laws: vec![law.clone()] }).unwrap();

    // Same-layer call rejected by acyclicity gate
    let bad_layer = StratumOp {
        id: StratumId(2), name: "bad_inc2".into(), layer: 1,
        params: vec![(ValId(0), ValType::I32)], results: vec![ValType::I32],
        body: Region::Block(vec![
            Stmt::Call { results: vec![(ValId(1), ValType::I32)], target: CallTarget::Stratum(StratumId(1)), args: vec![ValId(0)] },
            Stmt::Yield(vec![ValId(1)]),
        ]),
        docstring: "".into(),
    };
    assert_eq!(
        reg.register_candidate_op(bad_layer.clone()),
        Err(RegistryError::NonAcyclicLayer { caller_layer: 1, callee: StratumId(1), callee_layer: 1 })
    );

    let mut good_l2 = bad_layer;
    good_l2.layer = 2;
    good_l2.name = "inc2".into();
    good_l2.body = Region::Block(vec![
        Stmt::Call { results: vec![(ValId(1), ValType::I32)], target: CallTarget::Stratum(StratumId(1)), args: vec![ValId(0)] },
        Stmt::Call { results: vec![(ValId(2), ValType::I32)], target: CallTarget::Stratum(StratumId(1)), args: vec![ValId(1)] },
        Stmt::Yield(vec![ValId(2)]),
    ]);
    reg.promote_stratum(Stratum { op: good_l2, laws: vec![law] }).unwrap();

    let call_l2 = Region::Block(vec![
        Stmt::Call { results: vec![(ValId(1), ValType::I32)], target: CallTarget::Stratum(StratumId(2)), args: vec![ValId(0)] },
        Stmt::Yield(vec![ValId(1)]),
    ]);
    let mut next = 10;
    let lowered = reg.lower_region_to_layer0(&call_l2, &mut next).unwrap();
    let m = Module::default();
    let heap = HeapState::from_module(&m, 5000).unwrap();
    assert_eq!(
        eval_region(&m, &reg, &call_l2, &[(ValId(0), Val::I32(41))], heap.clone()).unwrap().0,
        eval_region(&m, &reg, &lowered, &[(ValId(0), Val::I32(41))], heap).unwrap().0
    );
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
        let r = Region::Block(vec![
            Stmt::Let { dst: ValId(10), ty: ValType::I32, op: Op::Bin(BinOp::I32Add, ValId(0), ValId(1)) },
            Stmt::Let { dst: ValId(11), ty: ValType::I32, op: Op::Bin(BinOp::I32Rotl, ValId(0), ValId(1)) },
            Stmt::Let { dst: ValId(12), ty: ValType::I64, op: Op::Bin(BinOp::I64Mul, ValId(2), ValId(3)) },
            Stmt::Let { dst: ValId(13), ty: ValType::I64, op: Op::Bin(BinOp::I64ShrS, ValId(2), ValId(3)) },
            Stmt::Effect(EffectOp::Store { mem: MemId(0), addr: ValId(4), offset: 0, width: MemWidth::B1, val: ValId(5) }),
            Stmt::Let { dst: ValId(14), ty: ValType::I32, op: Op::Load { mem: MemId(0), addr: ValId(4), offset: 0, width: MemWidth::B1, signed: false, result_ty: ValType::I32 } },
            Stmt::Yield(vec![ValId(10), ValId(11), ValId(12), ValId(13), ValId(14)]),
        ]);
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
        // MemId(1) strictly untouched when writing to MemId(0)
        prop_assert!(out_heap.memory(MemId(1)).unwrap().bytes[..4096].iter().all(|&x| x == 0x3c));
    }
}

#[test]
fn test_adversarial_audit_regressions() {
    // 1. validate_read_only must reject CallTarget::Stratum without a registry,
    // while validate_read_only_with_registry accepts pure Strata and rejects mutating Strata.
    let mut reg = StratumRegistry::new();
    let pure_op = StratumOp {
        id: StratumId(10),
        name: "pure_id".into(),
        layer: 1,
        params: vec![(ValId(0), ValType::I32)],
        results: vec![ValType::I32],
        body: Region::Block(vec![Stmt::Yield(vec![ValId(0)])]),
        docstring: String::new(),
    };
    let mut_op = StratumOp {
        id: StratumId(11),
        name: "mut_store".into(),
        layer: 1,
        params: vec![(ValId(0), ValType::I32)],
        results: vec![ValType::I32],
        body: Region::Block(vec![
            Stmt::Effect(EffectOp::Store {
                mem: MemId(0),
                addr: ValId(0),
                offset: 0,
                width: MemWidth::B1,
                val: ValId(0),
            }),
            Stmt::Yield(vec![ValId(0)]),
        ]),
        docstring: String::new(),
    };
    let triv_law = |sid: u32| Law {
        name: "id".into(),
        kind: LawKind::Algebraic,
        params: vec![(ValId(0), ValType::I32)],
        precondition: None,
        lhs: Region::Block(vec![
            Stmt::Call { results: vec![(ValId(1), ValType::I32)], target: CallTarget::Stratum(StratumId(sid)), args: vec![ValId(0)] },
            Stmt::Yield(vec![ValId(1)]),
        ]),
        rhs: Region::Block(vec![
            Stmt::Call { results: vec![(ValId(1), ValType::I32)], target: CallTarget::Stratum(StratumId(sid)), args: vec![ValId(0)] },
            Stmt::Yield(vec![ValId(1)]),
        ]),
        proof_digest: [0x55; 32],
    };
    reg.promote_stratum(Stratum { op: pure_op, laws: vec![triv_law(10)] }).unwrap();
    reg.promote_stratum(Stratum { op: mut_op, laws: vec![triv_law(11)] }).unwrap();

    let call_pure = Region::Block(vec![
        Stmt::Call { results: vec![(ValId(1), ValType::I32)], target: CallTarget::Stratum(StratumId(10)), args: vec![ValId(0)] },
        Stmt::Yield(vec![ValId(1)]),
    ]);
    let call_mut = Region::Block(vec![
        Stmt::Call { results: vec![(ValId(1), ValType::I32)], target: CallTarget::Stratum(StratumId(11)), args: vec![ValId(0)] },
        Stmt::Yield(vec![ValId(1)]),
    ]);
    assert!(!validate_read_only(&call_pure));
    assert!(!validate_read_only(&call_mut));
    assert!(validate_read_only_with_registry(&call_pure, &reg));
    assert!(!validate_read_only_with_registry(&call_mut, &reg));

    // 2. promote_stratum must reject calls to UNPROMOTED candidate strata and duplicate candidate names.
    let cand_op = StratumOp {
        id: StratumId(20),
        name: "cand_only".into(),
        layer: 1,
        params: vec![],
        results: vec![ValType::I32],
        body: Region::Block(vec![
            Stmt::Let { dst: ValId(0), ty: ValType::I32, op: Op::ConstI32(7) },
            Stmt::Yield(vec![ValId(0)]),
        ]),
        docstring: String::new(),
    };
    reg.register_candidate_op(cand_op).unwrap();
    let bad_caller = StratumOp {
        id: StratumId(21),
        name: "calls_unprom".into(),
        layer: 2,
        params: vec![],
        results: vec![ValType::I32],
        body: Region::Block(vec![
            Stmt::Call { results: vec![(ValId(0), ValType::I32)], target: CallTarget::Stratum(StratumId(20)), args: vec![] },
            Stmt::Yield(vec![ValId(0)]),
        ]),
        docstring: String::new(),
    };
    let empty_law = Law {
        name: "l".into(),
        kind: LawKind::Algebraic,
        params: vec![],
        precondition: None,
        lhs: Region::Block(vec![]),
        rhs: Region::Block(vec![]),
        proof_digest: [0x11; 32],
    };
    assert_eq!(
        reg.promote_stratum(Stratum { op: bad_caller, laws: vec![empty_law.clone()] }),
        Err(RegistryError::UnknownStratum(StratumId(20)))
    );
    let dup_cand_name = StratumOp {
        id: StratumId(22),
        name: "cand_only".into(),
        layer: 1,
        params: vec![],
        results: vec![],
        body: Region::Block(vec![]),
        docstring: String::new(),
    };
    assert_eq!(
        reg.promote_stratum(Stratum { op: dup_cand_name, laws: vec![empty_law] }),
        Err(RegistryError::DuplicateName)
    );

    // 3. split_invariant_loop rejects unstructured Return / escaping Break and preserves traps in cond/body/fuel.
    let one_reg = Region::Block(vec![
        Stmt::Let { dst: ValId(2), ty: ValType::I32, op: Op::ConstI32(1) },
        Stmt::Yield(vec![ValId(2)]),
    ]);
    let zero_u64 = Region::Block(vec![
        Stmt::Let { dst: ValId(2), ty: ValType::I64, op: Op::ConstI64(0) },
        Stmt::Yield(vec![ValId(2)]),
    ]);
    let ret_body_loop = Region::InvariantLoop {
        init_vars: vec![ValId(0)],
        state_vars: vec![(ValId(1), ValType::I32)],
        cond: Box::new(one_reg.clone()),
        invariant_pred: Box::new(one_reg.clone()),
        fuel_measure: Box::new(zero_u64.clone()),
        body: Box::new(Region::Block(vec![Stmt::Return(vec![ValId(1)])])),
    };
    assert_eq!(
        split_invariant_loop(vec![(ValId(0), ValType::I32)], None, &ret_body_loop, one_reg.clone()),
        Err(VcError::UnstructuredControlFlow)
    );

    let trap_cond = Region::Block(vec![
        Stmt::Let { dst: ValId(2), ty: ValType::I32, op: Op::ConstI32(0) },
        Stmt::Let { dst: ValId(3), ty: ValType::I32, op: Op::Bin(BinOp::I32DivU, ValId(1), ValId(2)) },
        Stmt::Yield(vec![ValId(3)]),
    ]);
    let trap_cond_loop = Region::InvariantLoop {
        init_vars: vec![ValId(0)],
        state_vars: vec![(ValId(1), ValType::I32)],
        cond: Box::new(trap_cond),
        invariant_pred: Box::new(one_reg.clone()),
        fuel_measure: Box::new(zero_u64),
        body: Box::new(Region::Block(vec![Stmt::Yield(vec![ValId(1)])])),
    };
    let vcs = split_invariant_loop(vec![(ValId(0), ValType::I32)], None, &trap_cond_loop, one_reg).unwrap();
    let m = Module::default();
    let heap = HeapState::from_module(&m, 1000).unwrap();
    assert_eq!(
        eval_vc(&m, &reg, &vcs.preservation, &[Val::I32(5), Val::I32(5)], heap),
        VcEvalResult::Violated(Some(TrapCode::DivByZero))
    );

    // 4. remap_region_vals with next_fresh = 0 must never collide with free ValIds in Op::Bin.
    let free_bin = Region::Block(vec![
        Stmt::Let { dst: ValId(1), ty: ValType::I32, op: Op::ConstI32(10) },
        Stmt::Let { dst: ValId(2), ty: ValType::I32, op: Op::Bin(BinOp::I32Add, ValId(1), ValId(5)) },
        Stmt::Yield(vec![ValId(2)]),
    ]);
    let mut nf = 0u32;
    let remapped = remap_region_vals(&free_bin, &[], &mut nf);
    let h2 = HeapState::from_module(&m, 1000).unwrap();
    assert_eq!(
        eval_region(&m, &reg, &remapped, &[(ValId(5), Val::I32(32))], h2).unwrap().0,
        vec![Val::I32(42)]
    );

    // 5. Lexical scoping: inner Region::Block shadowing ValId(0) must not clobber outer ValId(0),
    // zero-length OOB fill/copy traps, and immutable GlobalSet traps.
    let mut gm = mod_with_mem(1, Some(1));
    gm.globals.push(GlobalDef { id: GlobalId(0), ty: ValType::I32, mutable: false, init: Val::I32(9) });
    let shadow_reg = Region::Block(vec![
        Stmt::Region {
            results: vec![(ValId(2), ValType::I32)],
            region: Region::Block(vec![
                Stmt::Let { dst: ValId(0), ty: ValType::I32, op: Op::ConstI32(100) },
                Stmt::Yield(vec![ValId(0)]),
            ]),
        },
        Stmt::Let { dst: ValId(3), ty: ValType::I32, op: Op::Bin(BinOp::I32Add, ValId(0), ValId(2)) },
        Stmt::Yield(vec![ValId(3)]),
    ]);
    let gh = HeapState::from_module(&gm, 1000).unwrap();
    assert_eq!(
        eval_region(&gm, &reg, &shadow_reg, &[(ValId(0), Val::I32(7))], gh.clone()).unwrap().0,
        vec![Val::I32(107)]
    );

    let immut_set = Region::Block(vec![
        Stmt::Let { dst: ValId(0), ty: ValType::I32, op: Op::ConstI32(1) },
        Stmt::Effect(EffectOp::GlobalSet { id: GlobalId(0), val: ValId(0) }),
        Stmt::Yield(vec![]),
    ]);
    assert_eq!(eval_region(&gm, &reg, &immut_set, &[], gh.clone()), Err(TrapCode::Unreachable));

    let fill_len0_oob = Region::Block(vec![
        Stmt::Let { dst: ValId(0), ty: ValType::I32, op: Op::ConstI32((WASM_PAGE_SIZE + 1) as i32) },
        Stmt::Let { dst: ValId(1), ty: ValType::I32, op: Op::ConstI32(0) },
        Stmt::Effect(EffectOp::MemoryFill { mem: MemId(0), dst: ValId(0), val: ValId(1), len: ValId(1) }),
        Stmt::Yield(vec![]),
    ]);
    assert_eq!(eval_region(&gm, &reg, &fill_len0_oob, &[], gh), Err(TrapCode::OutOfBoundsMem));
}
