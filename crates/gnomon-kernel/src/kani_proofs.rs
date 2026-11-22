//! Kani formal verification harnesses for the `gnomon-kernel` TCB.

use alloc::{boxed::Box, string::String, vec, vec::Vec};

use crate::eval::{HeapState, MemoryState, eval_binop, eval_region};
use crate::ir::*;
use crate::registry::{Law, LawKind, RegistryError, Stratum, StratumOp, StratumRegistry};
use crate::vc::{
    VcError, VcEvalResult, VcKind, VcObligation, eval_vc, split_invariant_loop, validate_read_only,
    validate_read_only_with_registry,
};

fn empty_module() -> Module {
    Module {
        memories: Vec::new(),
        globals: Vec::new(),
        funcs: Vec::new(),
        host_contracts: Vec::new(),
        memory_exports: Vec::new(),
        global_exports: Vec::new(),
    }
}

fn empty_heap(fuel: u64) -> HeapState {
    HeapState { memories: Vec::new(), globals: Vec::new(), fuel_remaining: fuel }
}

fn empty_op(id: u32, name: String, layer: u16) -> StratumOp {
    StratumOp {
        id: StratumId(id),
        name,
        layer,
        params: Vec::new(),
        results: Vec::new(),
        body: Region::Block(Vec::new()),
        docstring: String::new(),
    }
}

#[kani::proof]
#[kani::solver(bitwuzla)]
fn proof_div_rem_trap_determinism() {
    let a32: i32 = kani::any();
    let b32: i32 = kani::any();
    let w32: u8 = kani::any();
    kani::assume(w32 < 4);

    let op32 = match w32 {
        0 => BinOp::I32DivS,
        1 => BinOp::I32DivU,
        2 => BinOp::I32RemS,
        _ => BinOp::I32RemU,
    };
    let r1 = eval_binop(op32, Val::I32(a32), Val::I32(b32));
    let r2 = eval_binop(op32, Val::I32(a32), Val::I32(b32));
    let ok32 = match op32 {
        BinOp::I32DivS => {
            if b32 == 0 {
                r1 == Err(TrapCode::DivByZero)
            } else if a32 == i32::MIN && b32 == -1 {
                r1 == Err(TrapCode::IntOverflow)
            } else {
                r1 == Ok(Val::I32(a32.wrapping_div(b32)))
            }
        }
        BinOp::I32DivU => {
            if b32 == 0 {
                r1 == Err(TrapCode::DivByZero)
            } else {
                r1 == Ok(Val::I32(((a32 as u32) / (b32 as u32)) as i32))
            }
        }
        BinOp::I32RemS => {
            if b32 == 0 {
                r1 == Err(TrapCode::DivByZero)
            } else if a32 == i32::MIN && b32 == -1 {
                r1 == Ok(Val::I32(0))
            } else {
                r1 == Ok(Val::I32(a32.wrapping_rem(b32)))
            }
        }
        BinOp::I32RemU => {
            if b32 == 0 {
                r1 == Err(TrapCode::DivByZero)
            } else {
                r1 == Ok(Val::I32(((a32 as u32) % (b32 as u32)) as i32))
            }
        }
        _ => false,
    };

    let a64: i64 = kani::any();
    let b64: i64 = kani::any();
    let w64: u8 = kani::any();
    kani::assume(w64 < 4);

    let op64 = match w64 {
        0 => BinOp::I64DivS,
        1 => BinOp::I64DivU,
        2 => BinOp::I64RemS,
        _ => BinOp::I64RemU,
    };
    let q1 = eval_binop(op64, Val::I64(a64), Val::I64(b64));
    let q2 = eval_binop(op64, Val::I64(a64), Val::I64(b64));
    let ok64 = match op64 {
        BinOp::I64DivS => {
            if b64 == 0 {
                q1 == Err(TrapCode::DivByZero)
            } else if a64 == i64::MIN && b64 == -1 {
                q1 == Err(TrapCode::IntOverflow)
            } else {
                q1 == Ok(Val::I64(a64.wrapping_div(b64)))
            }
        }
        BinOp::I64DivU => {
            if b64 == 0 {
                q1 == Err(TrapCode::DivByZero)
            } else {
                q1 == Ok(Val::I64(((a64 as u64) / (b64 as u64)) as i64))
            }
        }
        BinOp::I64RemS => {
            if b64 == 0 {
                q1 == Err(TrapCode::DivByZero)
            } else if a64 == i64::MIN && b64 == -1 {
                q1 == Ok(Val::I64(0))
            } else {
                q1 == Ok(Val::I64(a64.wrapping_rem(b64)))
            }
        }
        BinOp::I64RemU => {
            if b64 == 0 {
                q1 == Err(TrapCode::DivByZero)
            } else {
                q1 == Ok(Val::I64(((a64 as u64) % (b64 as u64)) as i64))
            }
        }
        _ => false,
    };

    assert!(r1 == r2 && ok32 && q1 == q2 && ok64);
}

#[kani::proof]
#[kani::unwind(18)]
fn proof_memory_ea_overflow_traps() {
    let len: usize = kani::any();
    kani::assume(len <= 16);
    let mut mem = MemoryState { id: MemId(0), bytes: vec![0x5Au8; len], max_pages: Some(1) };

    let addr: u32 = kani::any();
    let offset: u32 = kani::any();
    let w_idx: u8 = kani::any();
    kani::assume(w_idx < 4);
    let width = match w_idx {
        0 => MemWidth::B1,
        1 => MemWidth::B2,
        2 => MemWidth::B4,
        _ => MemWidth::B8,
    };
    let signed: bool = kani::any();
    let ty = if width == MemWidth::B8 || kani::any() { ValType::I64 } else { ValType::I32 };
    let val = match ty {
        ValType::I32 => Val::I32(kani::any()),
        ValType::I64 => Val::I64(kani::any()),
    };

    let expected_oob = (addr as u64) + (offset as u64) + width.bytes() > (mem.bytes.len() as u64);

    let load_res = mem.load(addr, offset, width, signed, ty);
    assert!((load_res == Err(TrapCode::OutOfBoundsMem)) == expected_oob);
    assert!(load_res.is_ok() == !expected_oob);

    let store_res = mem.store(addr, offset, width, val);
    assert!((store_res == Err(TrapCode::OutOfBoundsMem)) == expected_oob);
    assert!(store_res.is_ok() == !expected_oob);

    if ((addr as u64) + (offset as u64)) >= (1u64 << 32)
        && ((addr.wrapping_add(offset) as u64) + width.bytes()) <= (mem.bytes.len() as u64)
    {
        assert!(load_res == Err(TrapCode::OutOfBoundsMem));
        assert!(store_res == Err(TrapCode::OutOfBoundsMem));
    }

    assert!((mem.fill(addr, 0x11, 0) == Err(TrapCode::OutOfBoundsMem)) == ((addr as usize) > len));
}

#[kani::proof]
#[kani::unwind(10)]
fn proof_multi_memory_non_interference() {
    let m0_init: [u8; 8] = kani::any();
    let m1_init: [u8; 8] = kani::any();
    let mut heap = HeapState {
        memories: vec![
            MemoryState { id: MemId(0), bytes: m0_init.to_vec(), max_pages: Some(1) },
            MemoryState { id: MemId(1), bytes: m1_init.to_vec(), max_pages: Some(1) },
        ],
        globals: Vec::new(),
        fuel_remaining: 32,
    };

    let addr: u32 = kani::any();
    let offset: u32 = kani::any();
    let w = match kani::any::<u8>() & 3 {
        0 => MemWidth::B1,
        1 => MemWidth::B2,
        2 => MemWidth::B4,
        _ => MemWidth::B8,
    };
    let val = Val::I64(kani::any());
    let Some(m0) = heap.memory_mut(MemId(0)).ok() else { assert!(false); return; };
    let _ = m0.store(addr, offset, w, val);
    assert!(heap.memories[1].bytes.as_slice() == &m1_init);

    let fill_dst: u32 = kani::any();
    let fill_byte: u8 = kani::any();
    let fill_len: u32 = kani::any();
    let Some(m0) = heap.memory_mut(MemId(0)).ok() else { assert!(false); return; };
    let _ = m0.fill(fill_dst, fill_byte, fill_len);
    assert!(heap.memories[1].bytes.as_slice() == &m1_init);

    let src_mem = if kani::any() { MemId(1) } else { MemId(0) };
    let cp_dst: u32 = kani::any();
    let cp_src: u32 = kani::any();
    let cp_len: u32 = kani::any();
    let _ = heap.memory_copy(MemId(0), src_mem, cp_dst, cp_src, cp_len);
    assert!(heap.memories[1].bytes.as_slice() == &m1_init);
}

#[kani::proof]
#[kani::unwind(1)]
fn proof_registry_missing_law_and_layer_zero() {
    let mut reg = StratumRegistry::new();
    let layer: u16 = kani::any();
    assert!(
        reg.promote_stratum(Stratum { op: empty_op(10, String::new(), layer), laws: Vec::new() })
            == Err(RegistryError::MissingProvedLaw)
    );
    assert!(reg.register_candidate_op(empty_op(9, String::new(), 0)) == Err(RegistryError::InvalidLayerZero));
}

#[kani::proof]
#[kani::unwind(1)]
fn proof_registry_admission_gates() {
    let mut reg = StratumRegistry::new();
    let caller_layer: u16 = kani::any();
    let digest: [u8; 32] = kani::any();
    let nz = (digest[0] | digest[1] | digest[2] | digest[3] | digest[4] | digest[5] | digest[6] | digest[7])
        | (digest[8] | digest[9] | digest[10] | digest[11] | digest[12] | digest[13] | digest[14] | digest[15])
        | (digest[16] | digest[17] | digest[18] | digest[19] | digest[20] | digest[21] | digest[22] | digest[23])
        | (digest[24] | digest[25] | digest[26] | digest[27] | digest[28] | digest[29] | digest[30] | digest[31]);
    let res = reg.promote_stratum(Stratum {
        op: empty_op(2, String::new(), caller_layer),
        laws: vec![Law {
            name: String::new(),
            kind: LawKind::Algebraic,
            params: Vec::new(),
            precondition: None,
            lhs: Region::Block(Vec::new()),
            rhs: Region::Block(Vec::new()),
            proof_digest: digest,
        }],
    });
    if caller_layer == 0 {
        assert!(res == Err(RegistryError::InvalidLayerZero));
        return;
    }
    if nz == 0 {
        assert!(res == Err(RegistryError::EmptyProofDigest));
        return;
    }
    assert!(res == Ok(StratumId(2)) && reg.get_stratum(StratumId(2)).is_some());
}

#[kani::proof]
#[kani::unwind(1)]
fn proof_registry_self_callee_rejected() {
    let mut reg = StratumRegistry::new();
    let l1: u16 = kani::any();
    kani::assume(l1 >= 1);
    let self_rec = StratumOp {
        id: StratumId(9),
        name: String::new(),
        layer: l1,
        params: Vec::new(),
        results: Vec::new(),
        body: Region::Block(vec![Stmt::Call {
            results: Vec::new(),
            target: CallTarget::Stratum(StratumId(9)),
            args: Vec::new(),
        }]),
        docstring: String::new(),
    };
    assert!(reg.register_candidate_op(self_rec) == Err(RegistryError::UnknownStratum(StratumId(9))));
}

#[kani::proof]
#[kani::unwind(1)]
fn proof_registry_unpromoted_callee_rejected() {
    let mut reg = StratumRegistry::new();
    let l_cand: u16 = kani::any();
    kani::assume(l_cand >= 1 && l_cand < u16::MAX);
    let caller_layer: u16 = kani::any();
    assert!(reg.register_candidate_op(empty_op(1, String::new(), l_cand)) == Ok(StratumId(1)));
    let res = reg.promote_stratum(Stratum {
        op: StratumOp {
            id: StratumId(2),
            name: String::from("p"),
            layer: caller_layer,
            params: Vec::new(),
            results: Vec::new(),
            body: Region::Block(vec![Stmt::Call {
                results: Vec::new(),
                target: CallTarget::Stratum(StratumId(1)),
                args: Vec::new(),
            }]),
            docstring: String::new(),
        },
        laws: vec![Law {
            name: String::new(),
            kind: LawKind::Algebraic,
            params: Vec::new(),
            precondition: None,
            lhs: Region::Block(Vec::new()),
            rhs: Region::Block(Vec::new()),
            proof_digest: [1u8; 32],
        }],
    });
    if caller_layer == 0 {
        assert!(res == Err(RegistryError::InvalidLayerZero));
    } else {
        assert!(res == Err(RegistryError::UnknownStratum(StratumId(1))));
    }
}

#[kani::proof]
#[kani::unwind(1)]
fn proof_registry_dag_acyclicity() {
    let l1: u16 = kani::any();
    kani::assume(l1 >= 1);
    let l2: u16 = kani::any();

    let mut reg = StratumRegistry::new();
    let base_res = reg.promote_stratum(Stratum {
        op: empty_op(1, String::new(), l1),
        laws: vec![Law {
            name: String::new(),
            kind: LawKind::Algebraic,
            params: Vec::new(),
            precondition: None,
            lhs: Region::Block(Vec::new()),
            rhs: Region::Block(Vec::new()),
            proof_digest: [1u8; 32],
        }],
    });
    assert!(base_res == Ok(StratumId(1)));

    let caller_res = reg.promote_stratum(Stratum {
        op: StratumOp {
            id: StratumId(2),
            name: String::from("c"),
            layer: l2,
            params: Vec::new(),
            results: Vec::new(),
            body: Region::Block(vec![Stmt::Call {
                results: Vec::new(),
                target: CallTarget::Stratum(StratumId(1)),
                args: Vec::new(),
            }]),
            docstring: String::new(),
        },
        laws: vec![Law {
            name: String::new(),
            kind: LawKind::Algebraic,
            params: Vec::new(),
            precondition: None,
            lhs: Region::Block(Vec::new()),
            rhs: Region::Block(Vec::new()),
            proof_digest: [1u8; 32],
        }],
    });
    if l2 == 0 {
        assert!(caller_res == Err(RegistryError::InvalidLayerZero));
        return;
    }
    if l2 <= l1 {
        assert!(
            caller_res
                == Err(RegistryError::NonAcyclicLayer {
                    caller_layer: l2,
                    callee: StratumId(1),
                    callee_layer: l1,
                })
        );
        return;
    }
    assert!(caller_res == Ok(StratumId(2)) && reg.promoted().len() == 2);
}

#[kani::proof]
#[kani::unwind(1)]
fn proof_vc_read_only_ops() {
    let kind: u8 = kani::any();
    kani::assume(kind < 5);
    let stmt = match kind {
        0 => Stmt::Effect(EffectOp::Store {
            mem: MemId(0),
            addr: ValId(1),
            offset: 0,
            width: MemWidth::B4,
            val: ValId(2),
        }),
        1 => Stmt::Let {
            dst: ValId(2),
            ty: ValType::I32,
            op: Op::MemoryGrow { mem: MemId(0), delta: ValId(1) },
        },
        2 => Stmt::Effect(EffectOp::GlobalSet { id: GlobalId(0), val: ValId(1) }),
        3 => Stmt::Let {
            dst: ValId(2),
            ty: ValType::I32,
            op: Op::Load {
                mem: MemId(0),
                addr: ValId(1),
                offset: 0,
                width: MemWidth::B4,
                signed: false,
                result_ty: ValType::I32,
            },
        },
        _ => Stmt::Effect(EffectOp::Trap(TrapCode::Unreachable)),
    };
    let p = Region::Block(vec![stmt]);
    let reg = StratumRegistry::new();
    let expected_ro = kind >= 3;
    assert!(validate_read_only(&p) == expected_ro);
    assert!(validate_read_only_with_registry(&p, &reg) == expected_ro);
}

#[kani::proof]
#[kani::unwind(1)]
fn proof_vc_read_only_stratum_ro() {
    let mut reg = StratumRegistry::new();
    assert!(reg.register_candidate_op(empty_op(1, String::new(), 1)) == Ok(StratumId(1)));
    let p = Region::Block(vec![Stmt::Call {
        results: Vec::new(),
        target: CallTarget::Stratum(StratumId(1)),
        args: Vec::new(),
    }]);
    assert!(!validate_read_only(&p) && validate_read_only_with_registry(&p, &reg));
}

#[kani::proof]
#[kani::unwind(1)]
fn proof_vc_read_only_stratum_mut() {
    let mut reg = StratumRegistry::new();
    let op = StratumOp {
        id: StratumId(1),
        name: String::new(),
        layer: 1,
        params: vec![(ValId(0), ValType::I32)],
        results: Vec::new(),
        body: Region::Block(vec![Stmt::Effect(EffectOp::GlobalSet { id: GlobalId(0), val: ValId(0) })]),
        docstring: String::new(),
    };
    assert!(reg.register_candidate_op(op) == Ok(StratumId(1)));
    let p = Region::Block(vec![Stmt::Call {
        results: Vec::new(),
        target: CallTarget::Stratum(StratumId(1)),
        args: vec![ValId(1)],
    }]);
    assert!(!validate_read_only(&p) && !validate_read_only_with_registry(&p, &reg));
}

#[kani::proof]
#[kani::unwind(1)]
fn proof_vc_splitter_rejection_gates() {
    let mk_empty = || Box::new(Region::Block(Vec::new()));

    let non_loop = Region::Block(Vec::new());
    assert!(
        split_invariant_loop(Vec::new(), None, &non_loop, Region::Block(Vec::new()))
            == Err(VcError::NotAnInvariantLoop)
    );

    let arity_lp = Region::InvariantLoop {
        init_vars: Vec::new(),
        state_vars: vec![(ValId(1), ValType::I32)],
        cond: mk_empty(),
        invariant_pred: mk_empty(),
        fuel_measure: mk_empty(),
        body: mk_empty(),
    };
    assert!(
        split_invariant_loop(vec![(ValId(0), ValType::I32)], None, &arity_lp, Region::Block(Vec::new()))
            == Err(VcError::ArityMismatch)
    );
}

#[kani::proof]
#[kani::unwind(1)]
fn proof_vc_splitter_impure_rejected() {
    let mk_empty = || Box::new(Region::Block(Vec::new()));
    let lp = Region::InvariantLoop {
        init_vars: vec![ValId(0)],
        state_vars: vec![(ValId(1), ValType::I32)],
        cond: mk_empty(),
        invariant_pred: Box::new(Region::Block(vec![Stmt::Effect(EffectOp::GlobalSet {
            id: GlobalId(0),
            val: ValId(1),
        })])),
        fuel_measure: mk_empty(),
        body: mk_empty(),
    };
    assert!(
        split_invariant_loop(vec![(ValId(0), ValType::I32)], None, &lp, Region::Block(Vec::new()))
            == Err(VcError::ImpureSpecificationRegion)
    );
}

#[kani::proof]
#[kani::unwind(1)]
fn proof_vc_splitter_escape_rejected() {
    let mk_empty = || Box::new(Region::Block(Vec::new()));
    let lp = Region::InvariantLoop {
        init_vars: vec![ValId(0)],
        state_vars: vec![(ValId(1), ValType::I32)],
        cond: mk_empty(),
        invariant_pred: mk_empty(),
        fuel_measure: mk_empty(),
        body: Box::new(Region::Block(vec![Stmt::Return(vec![ValId(1)])])),
    };
    assert!(
        split_invariant_loop(vec![(ValId(0), ValType::I32)], None, &lp, Region::Block(Vec::new()))
            == Err(VcError::UnstructuredControlFlow)
    );
}

#[kani::proof]
#[kani::unwind(3)]
fn proof_vc_splitter_soundness_concrete_split() {
    let lp = Region::InvariantLoop {
        init_vars: vec![ValId(0)],
        state_vars: vec![(ValId(1), ValType::I32)],
        cond: Box::new(Region::Block(Vec::new())),
        invariant_pred: Box::new(Region::Block(vec![Stmt::Yield(vec![ValId(1)])])),
        fuel_measure: Box::new(Region::Block(Vec::new())),
        body: Box::new(Region::Block(Vec::new())),
    };
    let Ok(vcs) = split_invariant_loop(
        vec![(ValId(0), ValType::I32)],
        Some(Region::Block(Vec::new())),
        &lp,
        Region::Block(Vec::new()),
    ) else {
        assert!(false);
        return;
    };
    assert!(vcs.init.kind == VcKind::Init && vcs.init.assumptions.len() == 1);
    let init_goal_remapped = matches!(
        &vcs.init.goal,
        Region::Block(s) if matches!(s.as_slice(), [Stmt::Yield(vs)] if matches!(vs.as_slice(), [ValId(0)]))
    );
    assert!(init_goal_remapped);
    assert!(vcs.preservation.kind == VcKind::Preservation && vcs.preservation.assumptions.len() == 1);
    assert!(vcs.exit.kind == VcKind::Exit && vcs.exit.assumptions.len() == 2);
}

#[kani::proof]
#[kani::unwind(1)]
fn proof_vc_induction_obligations() {
    let sym_i: i32 = kani::any();

    let module = empty_module();
    let reg = StratumRegistry::new();

    let vc = VcObligation {
        kind: VcKind::Exit,
        params: vec![(ValId(0), ValType::I32), (ValId(1), ValType::I32)],
        assumptions: vec![Region::Block(vec![Stmt::Yield(vec![ValId(0)])])],
        goal: Region::Block(vec![
            Stmt::Let { dst: ValId(2), ty: ValType::I32, op: Op::Bin(BinOp::I32GtS, ValId(0), ValId(1)) },
            Stmt::Yield(vec![ValId(2)]),
        ]),
    };
    let expected = if sym_i == 0 {
        VcEvalResult::Vacuous
    } else if sym_i > 0 {
        VcEvalResult::Holds
    } else {
        VcEvalResult::Violated(None)
    };
    assert!(eval_vc(&module, &reg, &vc, &[Val::I32(sym_i), Val::I32(0)], empty_heap(32)) == expected);
}

#[kani::proof]
#[kani::unwind(2)]
fn proof_vc_induction_bounded_soundness() {
    let n: i32 = kani::any();
    kani::assume((0..=1).contains(&n));

    let module = empty_module();
    let reg = StratumRegistry::new();

    let loop_region = Region::InvariantLoop {
        init_vars: vec![ValId(0)],
        state_vars: vec![(ValId(1), ValType::I32)],
        cond: Box::new(Region::Block(vec![Stmt::Yield(vec![ValId(1)])])),
        invariant_pred: Box::new(Region::Block(Vec::new())),
        fuel_measure: Box::new(Region::Block(Vec::new())),
        body: Box::new(Region::Block(vec![Stmt::Continue {
            depth: 0,
            cond: None,
            values: vec![ValId(2)],
        }])),
    };

    assert!(
        eval_region(
            &module,
            &reg,
            &loop_region,
            &[(ValId(0), Val::I32(n)), (ValId(2), Val::I32(0))],
            empty_heap(0),
        ) == Err(TrapCode::OutOfFuel)
    );

    let Ok((vals, _)) = eval_region(
        &module,
        &reg,
        &loop_region,
        &[(ValId(0), Val::I32(n)), (ValId(2), Val::I32(0))],
        empty_heap(32),
    ) else {
        assert!(false);
        return;
    };
    assert!(vals.len() == 1 && vals[0] == Val::I32(0));
}
