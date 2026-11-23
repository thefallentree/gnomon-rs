//! Kani formal verification harnesses for the `gnomon-kernel` TCB.
//!
//! Verifies real production TCB entrypoints directly (`eval_binop`, `MemoryState`,
//! `HeapState`, `eval_region`, `StratumRegistry`, `validate_read_only`,
//! `validate_read_only_with_registry`, `split_invariant_loop`, and `eval_vc`)
//! with zero `#[kani::stub]` overrides, zero `ManuallyDrop` / `mem::forget`,
//! and full unwinding assertions enabled.

use alloc::{string::String, vec, vec::Vec};

use crate::eval::{HeapState, MemoryState, eval_binop, eval_region};
use crate::ir::*;
use crate::registry::{Law, LawKind, LawList, RegistryError, Stratum, StratumOp, StratumRegistry};
use crate::vc::{
    RegionList, VcError, VcEvalResult, VcKind, VcObligation, eval_vc, split_invariant_loop,
    validate_read_only, validate_read_only_with_registry,
};

static EMPTY_MODULE: Module = Module {
    memories: Vec::new(),
    globals: Vec::new(),
    funcs: Vec::new(),
    host_contracts: Vec::new(),
    memory_exports: Vec::new(),
    global_exports: Vec::new(),
};

static EMPTY_REG: StratumRegistry = StratumRegistry::new();

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
        body: Region::empty(),
        docstring: String::new(),
    }
}

fn empty_law(digest: [u8; 32]) -> Law {
    Law {
        name: String::new(),
        kind: LawKind::Algebraic,
        params: Vec::new(),
        precondition: Region::empty(),
        lhs: Region::empty(),
        rhs: Region::empty(),
        proof_digest: digest,
    }
}

// ---------------------------------------------------------------------------
// 1. Exact Arithmetic, Shifts/Rotates, EA Bounds, and Multi-Memory Isolation
// ---------------------------------------------------------------------------

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
#[kani::solver(bitwuzla)]
fn proof_shifts_and_rotates_masked() {
    let a32: i32 = kani::any();
    let b32: i32 = kani::any();
    let s32 = (b32 as u32) & 31;
    assert!(eval_binop(BinOp::I32Shl, Val::I32(a32), Val::I32(b32)) == Ok(Val::I32(a32.wrapping_shl(s32))));
    assert!(eval_binop(BinOp::I32ShrS, Val::I32(a32), Val::I32(b32)) == Ok(Val::I32(a32.wrapping_shr(s32))));
    assert!(eval_binop(BinOp::I32ShrU, Val::I32(a32), Val::I32(b32)) == Ok(Val::I32(((a32 as u32) >> s32) as i32)));
    assert!(eval_binop(BinOp::I32Rotl, Val::I32(a32), Val::I32(b32)) == Ok(Val::I32((a32 as u32).rotate_left(s32) as i32)));
    assert!(eval_binop(BinOp::I32Rotr, Val::I32(a32), Val::I32(b32)) == Ok(Val::I32((a32 as u32).rotate_right(s32) as i32)));

    let a64: i64 = kani::any();
    let b64: i64 = kani::any();
    let s64 = (b64 as u32) & 63;
    assert!(eval_binop(BinOp::I64Shl, Val::I64(a64), Val::I64(b64)) == Ok(Val::I64(a64.wrapping_shl(s64))));
    assert!(eval_binop(BinOp::I64ShrS, Val::I64(a64), Val::I64(b64)) == Ok(Val::I64(a64.wrapping_shr(s64))));
    assert!(eval_binop(BinOp::I64ShrU, Val::I64(a64), Val::I64(b64)) == Ok(Val::I64(((a64 as u64) >> s64) as i64)));
    assert!(eval_binop(BinOp::I64Rotl, Val::I64(a64), Val::I64(b64)) == Ok(Val::I64((a64 as u64).rotate_left(s64) as i64)));
    assert!(eval_binop(BinOp::I64Rotr, Val::I64(a64), Val::I64(b64)) == Ok(Val::I64((a64 as u64).rotate_right(s64) as i64)));
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
    let Ok(m0) = heap.memory_mut(MemId(0)) else { unreachable!() };
    let _ = m0.store(addr, offset, w, val);
    assert!(heap.memories[1].bytes.as_slice() == &m1_init);

    let fill_dst: u32 = kani::any();
    let fill_byte: u8 = kani::any();
    let fill_len: u32 = kani::any();
    let Ok(m0) = heap.memory_mut(MemId(0)) else { unreachable!() };
    let _ = m0.fill(fill_dst, fill_byte, fill_len);
    assert!(heap.memories[1].bytes.as_slice() == &m1_init);

    let src_mem = if kani::any() { MemId(1) } else { MemId(0) };
    let cp_dst: u32 = kani::any();
    let cp_src: u32 = kani::any();
    let cp_len: u32 = kani::any();
    let _ = heap.memory_copy(MemId(0), src_mem, cp_dst, cp_src, cp_len);
    assert!(heap.memories[1].bytes.as_slice() == &m1_init);
}

// ---------------------------------------------------------------------------
// 2. StratumRegistry Admission Gates & Layer DAG Acyclicity Proofs
// ---------------------------------------------------------------------------

#[kani::proof]
#[kani::unwind(3)]
fn proof_registry_admission_gates() {
    let mut reg = StratumRegistry::new();
    let caller_layer: u16 = kani::any();

    // Gate 1: Empty law list is unconditionally rejected.
    assert!(
        reg.promote_stratum(Stratum { op: empty_op(10, String::new(), caller_layer), laws: LawList::empty() })
            == Err(RegistryError::MissingProvedLaw)
    );

    // Gate 2: Candidate registration at Layer 0 is rejected.
    assert!(
        reg.register_candidate_op(empty_op(9, String::new(), 0))
            == Err(RegistryError::InvalidLayerZero)
    );

    // Gate 3: Symbolic 256-bit proof_digest & symbolic layer admission.
    let digest: [u8; 32] = kani::any();
    let [
        b0, b1, b2, b3, b4, b5, b6, b7,
        b8, b9, b10, b11, b12, b13, b14, b15,
        b16, b17, b18, b19, b20, b21, b22, b23,
        b24, b25, b26, b27, b28, b29, b30, b31,
    ] = digest;
    let nz = (b0 | b1 | b2 | b3 | b4 | b5 | b6 | b7)
        | (b8 | b9 | b10 | b11 | b12 | b13 | b14 | b15)
        | (b16 | b17 | b18 | b19 | b20 | b21 | b22 | b23)
        | (b24 | b25 | b26 | b27 | b28 | b29 | b30 | b31);
    let res = reg.promote_stratum(Stratum {
        op: empty_op(2, String::new(), caller_layer),
        laws: LawList::single(empty_law(digest)),
    });
    if caller_layer == 0 {
        assert!(res == Err(RegistryError::InvalidLayerZero));
    } else if nz == 0 {
        assert!(res == Err(RegistryError::EmptyProofDigest));
    } else {
        assert!(res == Ok(StratumId(2)) && reg.get_stratum(StratumId(2)).is_some());
    }
}

#[kani::proof]
#[kani::unwind(3)]
fn proof_registry_self_and_unpromoted_callee_rejected() {
    let mut reg = StratumRegistry::new();
    let l1: u16 = kani::any();
    kani::assume(l1 >= 1 && l1 < u16::MAX);

    // Self-recursive candidate op is rejected.
    let self_body = Region::call_stmt(&[], CallTarget::Stratum(StratumId(9)), &[]);
    assert!(
        reg.register_candidate_op(StratumOp {
            id: StratumId(9),
            name: String::new(),
            layer: l1,
            params: Vec::new(),
            results: Vec::new(),
            body: self_body,
            docstring: String::new(),
        }) == Err(RegistryError::UnknownStratum(StratumId(9)))
    );

    // Register an unpromoted candidate op(1), then verify promote_stratum rejects calling it.
    assert!(reg.register_candidate_op(empty_op(1, String::new(), l1)) == Ok(StratumId(1)));
    let caller_layer: u16 = kani::any();
    let call_cand = Region::call_stmt(&[], CallTarget::Stratum(StratumId(1)), &[]);
    let res = reg.promote_stratum(Stratum {
        op: StratumOp {
            id: StratumId(2),
            name: String::from("p"),
            layer: caller_layer,
            params: Vec::new(),
            results: Vec::new(),
            body: call_cand,
            docstring: String::new(),
        },
        laws: LawList::single(empty_law([1u8; 32])),
    });
    if caller_layer == 0 {
        assert!(res == Err(RegistryError::InvalidLayerZero));
    } else {
        assert!(res == Err(RegistryError::UnknownStratum(StratumId(1))));
    }
}

#[kani::proof]
#[kani::unwind(3)]
fn proof_registry_dag_acyclicity() {
    let l1: u16 = kani::any();
    let l2: u16 = kani::any();
    kani::assume(l1 >= 1);

    let mut reg = StratumRegistry::new();
    assert!(
        reg.promote_stratum(Stratum { op: empty_op(1, String::new(), l1), laws: LawList::single(empty_law([1u8; 32])) })
            == Ok(StratumId(1))
    );

    let call_s1 = Region::call_stmt(&[], CallTarget::Stratum(StratumId(1)), &[]);
    let res = reg.promote_stratum(Stratum {
        op: StratumOp {
            id: StratumId(2),
            name: String::from("c"),
            layer: l2,
            params: Vec::new(),
            results: Vec::new(),
            body: call_s1,
            docstring: String::new(),
        },
        laws: LawList::single(empty_law([1u8; 32])),
    });
    if l2 == 0 {
        assert!(res == Err(RegistryError::InvalidLayerZero));
    } else if l2 <= l1 {
        assert!(
            res == Err(RegistryError::NonAcyclicLayer {
                caller_layer: l2,
                callee: StratumId(1),
                callee_layer: l1,
            })
        );
    } else {
        assert!(res == Ok(StratumId(2)) && reg.promoted().len() == 2);
    }
}

// ---------------------------------------------------------------------------
// 3. VC Read-Only Validation, Loop Splitter, and Induction Soundness Proofs
// ---------------------------------------------------------------------------

#[kani::proof]
#[kani::unwind(3)]
fn proof_vc_read_only_validation() {
    let kind: u8 = kani::any();
    kani::assume(kind < 5);
    let slot = match kind {
        0 => IrSlot::effect(EffectOp::Store {
            mem: MemId(0),
            addr: ValId(1),
            offset: 0,
            width: MemWidth::B4,
            val: ValId(2),
        }),
        1 => IrSlot::let_op(
            ValId(2),
            ValType::I32,
            Op::MemoryGrow { mem: MemId(0), delta: ValId(1) },
        ),
        2 => IrSlot::effect(EffectOp::GlobalSet { id: GlobalId(0), val: ValId(1) }),
        3 => IrSlot::let_op(
            ValId(2),
            ValType::I32,
            Op::Load {
                mem: MemId(0),
                addr: ValId(1),
                offset: 0,
                width: MemWidth::B4,
                signed: false,
                result_ty: ValType::I32,
            },
        ),
        _ => IrSlot::effect(EffectOp::Trap(TrapCode::Unreachable)),
    };
    let p = Region::single_slot(slot);
    let expected_ro = kind >= 3;
    assert!(validate_read_only(&p) == expected_ro);
    assert!(validate_read_only_with_registry(&p, &EMPTY_REG) == expected_ro);

    // Verify read-only vs mutating Stratum callee tracking in StratumRegistry.
    let mut reg = StratumRegistry::new();
    assert!(reg.register_candidate_op(empty_op(1, String::from("ro"), 1)) == Ok(StratumId(1)));
    assert!(
        reg.register_candidate_op(StratumOp {
            id: StratumId(2),
            name: String::from("mut"),
            layer: 1,
            params: vec![(ValId(0), ValType::I32)],
            results: Vec::new(),
            body: Region::single_slot(IrSlot::effect(EffectOp::GlobalSet {
                id: GlobalId(0),
                val: ValId(0),
            })),
            docstring: String::new(),
        }) == Ok(StratumId(2))
    );

    let call_ro = Region::call_stmt(&[], CallTarget::Stratum(StratumId(1)), &[]);
    let call_mut = Region::call_stmt(&[], CallTarget::Stratum(StratumId(2)), &[ValId(1)]);
    assert!(!validate_read_only(&call_ro) && validate_read_only_with_registry(&call_ro, &reg));
    assert!(!validate_read_only(&call_mut) && !validate_read_only_with_registry(&call_mut, &reg));
}

#[kani::proof]
#[kani::unwind(7)]
fn proof_vc_splitter_rejects_invalid_loops() {
    let empty = Region::empty();

    // 1. Non-loop rejected.
    assert!(
        split_invariant_loop(Vec::new(), None, &empty, Region::empty())
            == Err(VcError::NotAnInvariantLoop)
    );

    // 2. Arity mismatch rejected.
    let arity_lp = Region::invariant_loop(&[], &[(ValId(1), ValType::I32)], &empty, &empty, &empty, &empty);
    assert!(
        split_invariant_loop(vec![(ValId(0), ValType::I32)], None, &arity_lp, Region::empty())
            == Err(VcError::ArityMismatch)
    );

    // 3. Impure specification region rejected.
    let impure_inv = Region::single_slot(IrSlot::effect(EffectOp::GlobalSet {
        id: GlobalId(0),
        val: ValId(1),
    }));
    let impure_lp = Region::invariant_loop(
        &[ValId(0)],
        &[(ValId(1), ValType::I32)],
        &empty,
        &impure_inv,
        &empty,
        &empty,
    );
    assert!(
        split_invariant_loop(vec![(ValId(0), ValType::I32)], None, &impure_lp, Region::empty())
            == Err(VcError::ImpureSpecificationRegion)
    );

    // 4. Escaping Return inside loop body rejected.
    let ret_body = Region::build(|b| b.push_return(&[ValId(1)]));
    let esc_lp = Region::invariant_loop(
        &[ValId(0)],
        &[(ValId(1), ValType::I32)],
        &empty,
        &empty,
        &empty,
        &ret_body,
    );
    assert!(
        split_invariant_loop(vec![(ValId(0), ValType::I32)], None, &esc_lp, Region::empty())
            == Err(VcError::UnstructuredControlFlow)
    );
}

#[kani::proof]
#[kani::unwind(7)]
fn proof_vc_splitter_soundness_concrete_split() {
    let empty = Region::empty();

    // 5. Valid concrete split produces Init, Preservation, and Exit VCs with state_var -> init_var remapping.
    let inv_pred = Region::yield_vals(&[ValId(1)]);
    let valid_lp = Region::invariant_loop(
        &[ValId(0)],
        &[(ValId(1), ValType::I32)],
        &empty,
        &inv_pred,
        &empty,
        &empty,
    );
    let Ok(vcs) = split_invariant_loop(
        vec![(ValId(0), ValType::I32)],
        Some(Region::empty()),
        &valid_lp,
        Region::empty(),
    ) else {
        kani::assert(false, "valid InvariantLoop split must succeed");
        unreachable!()
    };
    assert!(vcs.init.kind == VcKind::Init && vcs.init.assumptions.len() == 1);
    assert!(vcs.init.goal == Region::yield_vals(&[ValId(0)]));
    assert!(vcs.preservation.kind == VcKind::Preservation && vcs.preservation.assumptions.len() == 1);
    assert!(vcs.exit.kind == VcKind::Exit && vcs.exit.assumptions.len() == 2);
}

#[kani::proof]
#[kani::unwind(6)]
fn proof_vc_eval_obligations() {
    let sym_i: i32 = kani::any();
    let vc = VcObligation {
        kind: VcKind::Exit,
        params: vec![(ValId(0), ValType::I32)],
        assumptions: RegionList::single(Region::yield_vals(&[ValId(0)])),
        goal: Region::build(|b| {
            b.push_let(ValId(1), ValType::I32, Op::Un(UnOp::I32Clz, ValId(0)));
            b.push_yield(&[ValId(1)]);
        }),
    };
    let expected = if sym_i == 0 {
        VcEvalResult::Vacuous
    } else if sym_i > 0 {
        VcEvalResult::Holds
    } else {
        VcEvalResult::Violated(None)
    };
    assert!(eval_vc(&EMPTY_MODULE, &EMPTY_REG, &vc, &[Val::I32(sym_i)], empty_heap(32)) == expected);

    let trap_vc = VcObligation {
        kind: VcKind::Preservation,
        params: vec![(ValId(0), ValType::I32)],
        assumptions: RegionList::single(Region::yield_vals(&[ValId(0)])),
        goal: Region::single_slot(IrSlot::effect(EffectOp::Trap(TrapCode::DivByZero))),
    };
    let expected_trap = if sym_i == 0 {
        VcEvalResult::Vacuous
    } else {
        VcEvalResult::Violated(Some(TrapCode::DivByZero))
    };
    assert!(
        eval_vc(&EMPTY_MODULE, &EMPTY_REG, &trap_vc, &[Val::I32(sym_i)], empty_heap(32))
            == expected_trap
    );
}

#[kani::proof]
#[kani::unwind(3)]
fn proof_vc_induction_bounded_soundness() {
    let sym_i: i32 = kani::any();
    let cond = Region::yield_vals(&[ValId(1)]);
    let empty = Region::empty();
    let body = Region::build(|b| b.push_continue(0, None, &[ValId(2)]));
    let loop_region = Region::invariant_loop(
        &[ValId(0)],
        &[(ValId(1), ValType::I32)],
        &cond,
        &empty,
        &empty,
        &body,
    );

    assert!(
        eval_region(
            &EMPTY_MODULE,
            &EMPTY_REG,
            &loop_region,
            &[(ValId(0), Val::I32(sym_i)), (ValId(2), Val::I32(0))],
            empty_heap(0),
        ) == Err(TrapCode::OutOfFuel)
    );

    let Ok((vals, _)) = eval_region(
        &EMPTY_MODULE,
        &EMPTY_REG,
        &loop_region,
        &[(ValId(0), Val::I32(sym_i)), (ValId(2), Val::I32(0))],
        empty_heap(32),
    ) else {
        kani::assert(false, "bounded InvariantLoop with 32 fuel must terminate cleanly");
        unreachable!()
    };
    assert!(vals.len() == 1 && vals[0] == Val::I32(0));
}
