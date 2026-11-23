use gnomon_kernel::{
    BinOp, CallTarget, Law, LawKind, LawList, Op, Region, Stratum, StratumId, StratumOp,
    StratumRegistry, ValId, ValType,
};
use gnomon_sieve::{
    ConsolidationConfig, consolidate_registry, discover_candidate_inventions,
    encode_region_as_stitch_expr,
};

fn make_wrap_inc_op(id: u32) -> StratumOp {
    // wrap_inc(x, mask) = (x + 1) & mask
    let body = Region::build(|b| {
        b.push_let(ValId(2), ValType::I32, Op::ConstI32(1));
        b.push_let(ValId(3), ValType::I32, Op::Bin(BinOp::I32Add, ValId(0), ValId(2)));
        b.push_let(ValId(4), ValType::I32, Op::Bin(BinOp::I32And, ValId(3), ValId(1)));
        b.push_yield(&[ValId(4)]);
    });
    StratumOp {
        id: StratumId(id),
        name: "wrap_inc".into(),
        layer: 1,
        params: vec![(ValId(0), ValType::I32), (ValId(1), ValType::I32)],
        results: vec![ValType::I32],
        body,
        docstring: "Increment ring index modulo power-of-two mask".into(),
    }
}

fn make_unused_op(id: u32) -> StratumOp {
    // mix_xor(x, y) = (x ^ y) + x
    let body = Region::build(|b| {
        b.push_let(ValId(2), ValType::I32, Op::Bin(BinOp::I32Xor, ValId(0), ValId(1)));
        b.push_let(ValId(3), ValType::I32, Op::Bin(BinOp::I32Add, ValId(2), ValId(0)));
        b.push_yield(&[ValId(3)]);
    });
    StratumOp {
        id: StratumId(id),
        name: "mix_xor".into(),
        layer: 1,
        params: vec![(ValId(0), ValType::I32), (ValId(1), ValType::I32)],
        results: vec![ValType::I32],
        body,
        docstring: "Single-use op that should be pruned by MDL".into(),
    }
}

#[test]
fn test_consolidate_mdl_retains_multiuse_and_prunes_low_mdl_and_redundant_laws() {
    let mut reg = StratumRegistry::new();

    // Stratum 1: wrap_inc with 2 laws:
    //   - law_primary: wrap_inc(wrap_inc(x, m), m) -> wrap_inc_2_shortcut: here use an
    //     non-builtin algebraic law: wrap_inc(x, m) & m == wrap_inc(x, m)
    //   - law_redundant: (wrap_inc(x, m) & m) & m == wrap_inc(x, m)  (derivable in <= 3 egglog steps!)
    let lhs_primary = Region::build(|b| {
        b.push_call(
            &[(ValId(2), ValType::I32)],
            CallTarget::Stratum(StratumId(1)),
            &[ValId(0), ValId(1)],
        );
        b.push_let(ValId(3), ValType::I32, Op::Bin(BinOp::I32And, ValId(2), ValId(1)));
        b.push_yield(&[ValId(3)]);
    });
    let rhs_primary = Region::build(|b| {
        b.push_call(
            &[(ValId(2), ValType::I32)],
            CallTarget::Stratum(StratumId(1)),
            &[ValId(0), ValId(1)],
        );
        b.push_yield(&[ValId(2)]);
    });
    let lhs_redundant = Region::build(|b| {
        b.push_call(
            &[(ValId(2), ValType::I32)],
            CallTarget::Stratum(StratumId(1)),
            &[ValId(0), ValId(1)],
        );
        b.push_let(ValId(3), ValType::I32, Op::Bin(BinOp::I32And, ValId(2), ValId(1)));
        b.push_let(ValId(4), ValType::I32, Op::Bin(BinOp::I32And, ValId(3), ValId(1)));
        b.push_yield(&[ValId(4)]);
    });
    let rhs_redundant = rhs_primary.clone();

    reg.promote_stratum(Stratum {
        op: make_wrap_inc_op(1),
        laws: LawList::from_vec(vec![
            Law {
                name: "wrap_inc_idempotent_mask".into(),
                kind: LawKind::Algebraic,
                params: vec![(ValId(0), ValType::I32), (ValId(1), ValType::I32)],
                precondition: Region::empty(),
                lhs: lhs_primary,
                rhs: rhs_primary,
                proof_digest: [0x11; 32],
            },
            Law {
                name: "wrap_inc_double_mask_redundant".into(),
                kind: LawKind::Algebraic,
                params: vec![(ValId(0), ValType::I32), (ValId(1), ValType::I32)],
                precondition: Region::empty(),
                lhs: lhs_redundant,
                rhs: rhs_redundant,
                proof_digest: [0x22; 32],
            },
        ]),
    })
    .unwrap();

    // Stratum 2: mix_xor used in only 1 solution -> must be pruned by MDL (< 2 solutions).
    let mix_lhs = Region::build(|b| {
        b.push_call(
            &[(ValId(2), ValType::I32)],
            CallTarget::Stratum(StratumId(2)),
            &[ValId(0), ValId(1)],
        );
        b.push_let(ValId(3), ValType::I32, Op::ConstI32(0));
        b.push_let(ValId(4), ValType::I32, Op::Bin(BinOp::I32Or, ValId(2), ValId(3)));
        b.push_yield(&[ValId(4)]);
    });
    let mix_rhs = Region::build(|b| {
        b.push_call(
            &[(ValId(2), ValType::I32)],
            CallTarget::Stratum(StratumId(2)),
            &[ValId(0), ValId(1)],
        );
        b.push_yield(&[ValId(2)]);
    });
    reg.promote_stratum(Stratum {
        op: make_unused_op(2),
        laws: LawList::single(Law {
            name: "mix_or_zero".into(),
            kind: LawKind::Algebraic,
            params: vec![(ValId(0), ValType::I32), (ValId(1), ValType::I32)],
            precondition: Region::empty(),
            lhs: mix_lhs,
            rhs: mix_rhs,
            proof_digest: [0x33; 32],
        }),
    })
    .unwrap();

    // Three verified solutions:
    // - sol1 & sol2 contain raw inlined `((a + 1) & m)` with DIFFERENT ValIds (tests stitch_core matching!)
    // - sol3 calls wrap_inc directly AND uses mix_xor once
    let sol1 = Region::build(|b| {
        b.push_let(ValId(10), ValType::I32, Op::ConstI32(1));
        b.push_let(ValId(11), ValType::I32, Op::Bin(BinOp::I32Add, ValId(0), ValId(10)));
        b.push_let(ValId(12), ValType::I32, Op::Bin(BinOp::I32And, ValId(11), ValId(1)));
        b.push_let(ValId(13), ValType::I32, Op::ConstI32(1));
        b.push_let(ValId(14), ValType::I32, Op::Bin(BinOp::I32Add, ValId(12), ValId(13)));
        b.push_let(ValId(15), ValType::I32, Op::Bin(BinOp::I32And, ValId(14), ValId(1)));
        b.push_yield(&[ValId(15)]);
    });
    let sol2 = Region::build(|b| {
        b.push_let(ValId(20), ValType::I32, Op::ConstI32(1));
        b.push_let(ValId(21), ValType::I32, Op::Bin(BinOp::I32Add, ValId(2), ValId(20)));
        b.push_let(ValId(22), ValType::I32, Op::Bin(BinOp::I32And, ValId(21), ValId(3)));
        b.push_yield(&[ValId(22)]);
    });
    let sol3 = Region::build(|b| {
        b.push_call(
            &[(ValId(5), ValType::I32)],
            CallTarget::Stratum(StratumId(1)),
            &[ValId(0), ValId(1)],
        );
        b.push_call(
            &[(ValId(6), ValType::I32)],
            CallTarget::Stratum(StratumId(2)),
            &[ValId(5), ValId(1)],
        );
        b.push_yield(&[ValId(6)]);
    });

    let (rebuilt, report) =
        consolidate_registry(&reg, &[sol1.clone(), sol2.clone(), sol3], &ConsolidationConfig::default())
            .unwrap();

    // Stratum 1 kept (3 solutions, 4 uses, positive MDL savings); Stratum 2 pruned (only 1 solution).
    assert_eq!(report.kept_strata, vec![1]);
    assert_eq!(report.pruned_strata, vec![2]);
    assert!(rebuilt.get_stratum(StratumId(1)).is_some());
    assert!(rebuilt.get_stratum(StratumId(2)).is_none());

    // Redundant double-mask law was derived in <= 3 egglog steps and pruned!
    let s1 = rebuilt.get_stratum(StratumId(1)).unwrap();
    assert_eq!(s1.laws.len(), 1);
    assert_eq!(s1.laws.first().unwrap().name, "wrap_inc_idempotent_mask");
    assert_eq!(report.kept_laws, 1);
    assert!(report.pruned_laws >= 2);
    assert!(report.autodoc_markdown.contains("wrap_inc"));
    assert!(!report.autodoc_markdown.contains("mix_xor"));

    // Verify alpha-normalized encoding matches across different ValIds.
    let e_body = encode_region_as_stitch_expr(
        &make_wrap_inc_op(1).body,
        &[(ValId(0), ValType::I32), (ValId(1), ValType::I32)],
    )
    .unwrap();
    let e_sol2 = encode_region_as_stitch_expr(
        &sol2,
        &[(ValId(2), ValType::I32), (ValId(3), ValType::I32)],
    )
    .unwrap();
    assert_eq!(e_body.to_string_curried(None), e_sol2.to_string_curried(None));

    // Exercise offline stitch_core::compression discovery on sol1 & sol2.
    let discovered = discover_candidate_inventions(&[sol1, sol2], 2, 1).unwrap();
    assert!(!discovered.is_empty());
    assert!(discovered[0].uses >= 2);
}

#[test]
fn test_consolidate_preserves_transitive_dag_dependencies() {
    let mut reg = StratumRegistry::new();

    // Layer 1 base op: add1(x) = x + 1 (not directly used in solutions, only called by Layer 2!)
    let add1_body = Region::build(|b| {
        b.push_let(ValId(1), ValType::I32, Op::ConstI32(1));
        b.push_let(ValId(2), ValType::I32, Op::Bin(BinOp::I32Add, ValId(0), ValId(1)));
        b.push_yield(&[ValId(2)]);
    });
    let add1_lhs = Region::build(|b| {
        b.push_call(&[(ValId(1), ValType::I32)], CallTarget::Stratum(StratumId(1)), &[ValId(0)]);
        b.push_let(ValId(2), ValType::I32, Op::ConstI32(1));
        b.push_let(ValId(3), ValType::I32, Op::Bin(BinOp::I32Sub, ValId(1), ValId(2)));
        b.push_yield(&[ValId(3)]);
    });
    reg.promote_stratum(Stratum {
        op: StratumOp {
            id: StratumId(1),
            name: "add1".into(),
            layer: 1,
            params: vec![(ValId(0), ValType::I32)],
            results: vec![ValType::I32],
            body: add1_body,
            docstring: "Increment by 1".into(),
        },
        laws: LawList::single(Law {
            name: "add1_sub1_cancel".into(),
            kind: LawKind::Algebraic,
            params: vec![(ValId(0), ValType::I32)],
            precondition: Region::empty(),
            lhs: add1_lhs,
            rhs: Region::yield_vals(&[ValId(0)]),
            proof_digest: [0x44; 32],
        }),
    })
    .unwrap();

    // Layer 2 op: add2_mask(x, m) = (add1(add1(x))) & m
    let add2_mask_body = Region::build(|b| {
        b.push_call(&[(ValId(2), ValType::I32)], CallTarget::Stratum(StratumId(1)), &[ValId(0)]);
        b.push_call(&[(ValId(3), ValType::I32)], CallTarget::Stratum(StratumId(1)), &[ValId(2)]);
        b.push_let(ValId(4), ValType::I32, Op::Bin(BinOp::I32And, ValId(3), ValId(1)));
        b.push_yield(&[ValId(4)]);
    });
    let l2_lhs = Region::build(|b| {
        b.push_call(
            &[(ValId(2), ValType::I32)],
            CallTarget::Stratum(StratumId(2)),
            &[ValId(0), ValId(1)],
        );
        b.push_let(ValId(3), ValType::I32, Op::Bin(BinOp::I32And, ValId(2), ValId(1)));
        b.push_yield(&[ValId(3)]);
    });
    let l2_rhs = Region::build(|b| {
        b.push_call(
            &[(ValId(2), ValType::I32)],
            CallTarget::Stratum(StratumId(2)),
            &[ValId(0), ValId(1)],
        );
        b.push_yield(&[ValId(2)]);
    });
    reg.promote_stratum(Stratum {
        op: StratumOp {
            id: StratumId(2),
            name: "add2_mask".into(),
            layer: 2,
            params: vec![(ValId(0), ValType::I32), (ValId(1), ValType::I32)],
            results: vec![ValType::I32],
            body: add2_mask_body,
            docstring: "Increment twice and mask".into(),
        },
        laws: LawList::single(Law {
            name: "add2_mask_idem".into(),
            kind: LawKind::Algebraic,
            params: vec![(ValId(0), ValType::I32), (ValId(1), ValType::I32)],
            precondition: Region::empty(),
            lhs: l2_lhs,
            rhs: l2_rhs,
            proof_digest: [0x55; 32],
        }),
    })
    .unwrap();

    // Two solutions both calling Layer-2 op (id=2). Even if add1 were not kept on its own,
    // DAG closure must retain id=1 so rebuilt registry passes TCB promote_stratum!
    let sol = Region::build(|b| {
        b.push_call(
            &[(ValId(2), ValType::I32)],
            CallTarget::Stratum(StratumId(2)),
            &[ValId(0), ValId(1)],
        );
        b.push_yield(&[ValId(2)]);
    });
    let (rebuilt, report) =
        consolidate_registry(&reg, &[sol.clone(), sol], &ConsolidationConfig::default()).unwrap();
    assert!(report.kept_strata.contains(&2));
    assert!(report.kept_strata.contains(&1));
    assert!(rebuilt.get_stratum(StratumId(1)).is_some());
    assert!(rebuilt.get_stratum(StratumId(2)).is_some());
}

#[test]
fn test_consolidate_does_not_erase_dead_trapping_ops_in_law_redundancy() {
    // Regression test: `let _ = a / b; yield(0)` MUST NOT be considered canonically equal
    // to `yield(0)` during law non-redundancy checking because `a / b` can trap DivByZero/IntOverflow!
    let traps = Region::build(|b| {
        b.push_let(ValId(2), ValType::I32, Op::Bin(BinOp::I32DivS, ValId(0), ValId(1)));
        b.push_let(ValId(3), ValType::I32, Op::ConstI32(0));
        b.push_yield(&[ValId(3)]);
    });
    let pure_zero = Region::build(|b| {
        b.push_let(ValId(3), ValType::I32, Op::ConstI32(0));
        b.push_yield(&[ValId(3)]);
    });
    let params = [(ValId(0), ValType::I32), (ValId(1), ValType::I32)];
    let e_traps = encode_region_as_stitch_expr(&traps, &params).unwrap();
    let e_pure = encode_region_as_stitch_expr(&pure_zero, &params).unwrap();
    assert_ne!(
        e_traps.to_string_curried(None),
        e_pure.to_string_curried(None),
        "dead trapping DivS must remain distinguishable in canonical stitch Expr"
    );
}

