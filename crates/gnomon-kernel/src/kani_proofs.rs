//! Kani formal verification harnesses for the `gnomon-kernel` TCB.
//!
//! Verifies real production TCB entrypoints directly (`eval_binop`, `MemoryState`,
//! `HeapState`, `eval_region`, `StratumRegistry`, `validate_read_only`,
//! `validate_read_only_with_registry`, `split_invariant_loop`, and `eval_vc`)
//! with zero `#[kani::stub]` overrides, zero `ManuallyDrop` / `mem::forget`,
//! and full unwinding assertions enabled.

use alloc::{string::String, vec, vec::Vec};

use crate::eval::{HeapState, MemoryState, eval_binop, eval_region, eval_unop};
use crate::fp::{F32_CANON_NAN, f32_is_nan};
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
        _ => unreachable!(),
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

// ---------------------------------------------------------------------------
// 4. TCB v2: Deterministic IEEE-754 f32/f64, v128 SIMD, MemWidth::B16 & IrSlot v2
// ---------------------------------------------------------------------------

#[kani::proof]
fn kani_fp_semantics_deterministic() {
    let a: u32 = kani::any();
    let b: u32 = kani::any();
    let va = Val::F32(a);
    let vb = Val::F32(b);

    // 1. Bitwise sign ops: trap-free, deterministic, preserve NaN payloads verbatim.
    let abs1 = eval_unop(UnOp::F32Abs, va);
    let abs2 = eval_unop(UnOp::F32Abs, va);
    assert!(abs1 == abs2 && abs1 == Ok(Val::F32(a & 0x7fff_ffff)));

    let neg1 = eval_unop(UnOp::F32Neg, va);
    let neg2 = eval_unop(UnOp::F32Neg, va);
    assert!(neg1 == neg2 && neg1 == Ok(Val::F32(a ^ 0x8000_0000)));

    let cs1 = eval_binop(BinOp::F32Copysign, va, vb);
    let cs2 = eval_binop(BinOp::F32Copysign, va, vb);
    assert!(cs1 == cs2 && cs1 == Ok(Val::F32((a & 0x7fff_ffff) | (b & 0x8000_0000))));

    // 2. Min / Max: trap-free, deterministic, canonical NaN on any NaN, -0.0 < +0.0.
    let min1 = eval_binop(BinOp::F32Min, va, vb);
    let min2 = eval_binop(BinOp::F32Min, va, vb);
    let max1 = eval_binop(BinOp::F32Max, va, vb);
    let max2 = eval_binop(BinOp::F32Max, va, vb);
    assert!(min1 == min2 && max1 == max2);
    let Ok(Val::F32(min_b)) = min1 else { unreachable!() };
    let Ok(Val::F32(max_b)) = max1 else { unreachable!() };
    if f32_is_nan(a) || f32_is_nan(b) {
        assert!(min_b == F32_CANON_NAN && max_b == F32_CANON_NAN);
    } else if ((a | b) & 0x7fff_ffff) == 0 {
        assert!(min_b == (a | b) && max_b == (a & b));
    }

    // 3. Rounding ops: trap-free, deterministic, canonical NaN on NaN.
    let r_kind: u8 = kani::any();
    kani::assume(r_kind < 4);
    let rop = match r_kind {
        0 => UnOp::F32Ceil,
        1 => UnOp::F32Floor,
        2 => UnOp::F32Trunc,
        _ => UnOp::F32Nearest,
    };
    let r1 = eval_unop(rop, va);
    let r2 = eval_unop(rop, va);
    assert!(r1 == r2);
    let Ok(Val::F32(rb)) = r1 else { unreachable!() };
    if f32_is_nan(a) {
        assert!(rb == F32_CANON_NAN);
    }

    // 4. Saturating truncations: 100% trap-free, deterministic, NaN -> 0.
    let ts_s1 = eval_unop(UnOp::I32TruncSatF32S, va);
    let ts_s2 = eval_unop(UnOp::I32TruncSatF32S, va);
    let ts_u1 = eval_unop(UnOp::I32TruncSatF32U, va);
    let ts_u2 = eval_unop(UnOp::I32TruncSatF32U, va);
    assert!(ts_s1 == ts_s2 && ts_s1.is_ok());
    assert!(ts_u1 == ts_u2 && ts_u1.is_ok());
    if f32_is_nan(a) {
        assert!(ts_s1 == Ok(Val::I32(0)) && ts_u1 == Ok(Val::I32(0)));
    }
}

#[kani::proof]
#[kani::unwind(20)]
fn kani_v128_lane_and_mem16() {
    let v: u128 = kani::any();
    let other: u128 = kani::any();
    let mask: u128 = kani::any();

    // 1. Replace-lane + extract-lane round-trip for symbolic LaneKind and lane index.
    let kind_idx: u8 = kani::any();
    kani::assume(kind_idx < 6);
    let (kind, scalar_ty, scalar_val) = match kind_idx {
        0 => (LaneKind::I8x16U, ValType::I32, Val::I32((kani::any::<u8>()) as i32)),
        1 => (LaneKind::I16x8U, ValType::I32, Val::I32((kani::any::<u16>()) as i32)),
        2 => (LaneKind::I32x4, ValType::I32, Val::I32(kani::any())),
        3 => (LaneKind::I64x2, ValType::I64, Val::I64(kani::any())),
        4 => (LaneKind::F32x4, ValType::F32, Val::F32(kani::any())),
        _ => (LaneKind::F64x2, ValType::F64, Val::F64(kani::any())),
    };
    let lane: u8 = kani::any();
    kani::assume(lane < kind.num_lanes());

    let reg = Region::build(|b| {
        b.push_let(ValId(4), ValType::V128, Op::SimdReplaceLane { kind, lane, vec: ValId(0), val: ValId(3) });
        b.push_let(ValId(5), scalar_ty, Op::SimdExtractLane { kind, lane, vec: ValId(4) });
        b.push_let(ValId(6), ValType::V128, Op::SimdBitselect { a: ValId(0), b: ValId(1), mask: ValId(2) });
        b.push_yield(&[ValId(5), ValId(6)]);
    });
    let Ok((out, _)) = eval_region(
        &EMPTY_MODULE,
        &EMPTY_REG,
        &reg,
        &[
            (ValId(0), Val::V128(v)),
            (ValId(1), Val::V128(other)),
            (ValId(2), Val::V128(mask)),
            (ValId(3), scalar_val),
        ],
        empty_heap(32),
    ) else {
        kani::assert(false, "valid v128 lane/bitselect region must succeed");
        unreachable!()
    };
    assert!(out.len() == 2);
    assert!(out[0] == scalar_val);
    assert!(out[1] == Val::V128((v & mask) | (other & !mask)));

    // 2. MemWidth::B16 store/load exact round-trip and EA overflow trapping.
    let len: usize = kani::any();
    kani::assume(len <= 18);
    let mut mem = MemoryState { id: MemId(0), bytes: vec![0u8; len], max_pages: Some(1) };
    let addr: u32 = kani::any();
    let offset: u32 = kani::any();
    let expected_oob = (addr as u64) + (offset as u64) + 16 > (len as u64);

    let st = mem.store(addr, offset, MemWidth::B16, Val::V128(v));
    let ld = mem.load(addr, offset, MemWidth::B16, false, ValType::V128);
    if expected_oob {
        assert!(st == Err(TrapCode::OutOfBoundsMem) && ld == Err(TrapCode::OutOfBoundsMem));
    } else {
        assert!(st == Ok(()) && ld == Ok(Val::V128(v)));
    }
}

#[kani::proof]
#[kani::unwind(18)]
fn kani_ir_slot_v2_roundtrip() {
    assert!(core::mem::size_of::<IrSlot>() == 24);
    assert!(!core::mem::needs_drop::<IrSlot>());

    // Dense u8 round-trip for UnOp and BinOp.
    let u_raw: u8 = kani::any();
    if u_raw < UnOp::COUNT {
        let Some(u) = UnOp::from_u8(u_raw) else { unreachable!() };
        assert!(u.to_u8() == u_raw);
    } else {
        assert!(UnOp::from_u8(u_raw).is_none());
    }
    let b_raw: u8 = kani::any();
    if b_raw < BinOp::COUNT {
        let Some(b) = BinOp::from_u8(b_raw) else { unreachable!() };
        assert!(b.to_u8() == b_raw);
    } else {
        assert!(BinOp::from_u8(b_raw).is_none());
    }

    // Lossless pool encoding for all new v2 Op variants including aux-backed SimdShuffle.
    let f32_bits: u32 = kani::any();
    let f64_bits: u64 = kani::any();
    let v128_bits: u128 = kani::any();
    let kind_raw: u8 = kani::any();
    kani::assume(kind_raw < 8);
    let Some(kind) = LaneKind::from_u8(kind_raw) else { unreachable!() };
    let lane: u8 = kani::any();
    let lanes: [u8; 16] = kani::any();

    let op0 = Op::ConstF32(f32_bits);
    let op1 = Op::ConstF64(f64_bits);
    let op2 = Op::ConstV128(v128_bits);
    let op3 = Op::SimdExtractLane { kind, lane, vec: ValId(2) };
    let op4 = Op::SimdReplaceLane { kind, lane, vec: ValId(2), val: ValId(3) };
    let op5 = Op::SimdBitselect { a: ValId(2), b: ValId(4), mask: ValId(2) };
    let op6 = Op::SimdShuffle { lhs: ValId(2), rhs: ValId(4), lanes };

    let reg = Region::build(|b| {
        b.push_let(ValId(0), ValType::F32, op0);
        b.push_let(ValId(1), ValType::F64, op1);
        b.push_let(ValId(2), ValType::V128, op2);
        b.push_let(ValId(3), kind.scalar_ty(), op3);
        b.push_let(ValId(4), ValType::V128, op4);
        b.push_let(ValId(5), ValType::V128, op5);
        b.push_let(ValId(6), ValType::V128, op6);
    });
    let RegionNode::Block(span) = reg.root else { unreachable!() };
    assert!(span.len == 7);
    assert!(reg.try_stmt(span, 0) == Some(Stmt::Let { dst: ValId(0), ty: ValType::F32, op: op0 }));
    assert!(reg.try_stmt(span, 1) == Some(Stmt::Let { dst: ValId(1), ty: ValType::F64, op: op1 }));
    assert!(reg.try_stmt(span, 2) == Some(Stmt::Let { dst: ValId(2), ty: ValType::V128, op: op2 }));
    assert!(reg.try_stmt(span, 3) == Some(Stmt::Let { dst: ValId(3), ty: kind.scalar_ty(), op: op3 }));
    assert!(reg.try_stmt(span, 4) == Some(Stmt::Let { dst: ValId(4), ty: ValType::V128, op: op4 }));
    assert!(reg.try_stmt(span, 5) == Some(Stmt::Let { dst: ValId(5), ty: ValType::V128, op: op5 }));
    assert!(reg.try_stmt(span, 6) == Some(Stmt::Let { dst: ValId(6), ty: ValType::V128, op: op6 }));

    // Verify shift preservation when embedding SimdShuffle inside another Region.
    let single = Region::single_stmt(Stmt::Let { dst: ValId(9), ty: ValType::V128, op: op6 });
    let wrapped = Region::if_else(ValId(0), &single, &Region::empty(), &[]);
    let RegionNode::IfElse { then_region, .. } = wrapped.root else { unreachable!() };
    let Some(RegionNode::Block(t_span)) = wrapped.try_node(then_region) else { unreachable!() };
    assert!(
        wrapped.try_stmt(t_span, 0)
            == Some(Stmt::Let { dst: ValId(9), ty: ValType::V128, op: op6 })
    );
}
