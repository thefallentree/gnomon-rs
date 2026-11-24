//! Static SMT-cliff complexity estimator for `GnomonIR` regions and modules.
//!
//! Analyzes structural patterns known to cause bit-blasting or array-theory cliffs
//! in `QF_ABV` solvers (deep 64-bit nonlinear arithmetic chains, conditional memory
//! stores inside `IfElse` branches, nested or unbounded loops, and large SSA graphs)
//! and emits concrete remediation advice (such as Stratum extraction for UF CEGAR or
//! straight-line store flattening).

use std::collections::BTreeMap;

use gnomon_kernel::{
    BinOp, CallTarget, EffectOp, MAX_CALL_DEPTH, Module, Op, Region, RegionNode, RegionRef, Span,
    Stmt, StratumRegistry, ValId,
};
use serde::{Deserialize, Serialize};

use crate::smt_ir::{MAX_SMT_LOOP_UNROLL, is_pure_total_stratum};

/// Qualitative SMT solver cliff risk level.
#[derive(
    Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize,
)]
pub enum CliffLevel {
    #[default]
    Low,
    Medium,
    High,
}

/// Static SMT complexity metrics and diagnostics for a single `Region`.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct RegionCliffMetrics {
    pub ssa_nodes: usize,
    pub nonlinear_ops: usize,
    pub nonlinear64_ops: usize,
    pub max_nonlinear_chain_depth: u32,
    pub max_nonlinear64_chain_depth: u32,
    pub mem_stores: usize,
    pub conditional_mem_stores: usize,
    pub max_branch_depth: u32,
    pub bounded_loops: usize,
    pub max_bounded_loop_iters: u32,
    pub invariant_loops: usize,
    pub has_unbounded_loop: bool,
    pub max_loop_depth: u32,
    pub stratum_calls: usize,
    pub level: CliffLevel,
    pub warnings: Vec<String>,
}

/// Per-function SMT-cliff report within a `CliffReport`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FuncCliffReport {
    pub func_id: u32,
    pub name: String,
    pub export_name: Option<String>,
    pub metrics: RegionCliffMetrics,
}

/// Module-wide static SMT-cliff complexity report.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct CliffReport {
    pub level: CliffLevel,
    pub total_ssa_nodes: usize,
    pub total_nonlinear_ops: usize,
    pub total_nonlinear64_ops: usize,
    pub max_nonlinear_chain_depth: u32,
    pub max_nonlinear64_chain_depth: u32,
    pub total_mem_stores: usize,
    pub total_conditional_mem_stores: usize,
    pub max_loop_depth: u32,
    pub has_unbounded_loop: bool,
    pub functions: Vec<FuncCliffReport>,
    pub warnings: Vec<String>,
}

#[derive(Clone, Copy, Debug, Default)]
struct DepthPair {
    any: u32,
    bits64: u32,
}

impl DepthPair {
    const ZERO: Self = Self { any: 0, bits64: 0 };

    fn max(self, other: Self) -> Self {
        Self { any: self.any.max(other.any), bits64: self.bits64.max(other.bits64) }
    }
}

#[derive(Default)]
struct WalkOutcome {
    exits: Vec<DepthPair>,
    continues0: Vec<DepthPair>,
}

fn merge_depth_vecs(dst: &mut Vec<DepthPair>, src: &[DepthPair]) {
    if src.len() > dst.len() {
        dst.resize(src.len(), DepthPair::ZERO);
    }
    for (d, &s) in dst.iter_mut().zip(src) {
        *d = d.max(s);
    }
}

fn is_nonlinear_64(op: BinOp) -> bool {
    matches!(
        op,
        BinOp::I64Mul | BinOp::I64DivS | BinOp::I64DivU | BinOp::I64RemS | BinOp::I64RemU
    )
}

fn is_nonlinear_32(op: BinOp) -> bool {
    matches!(
        op,
        BinOp::I32Mul | BinOp::I32DivS | BinOp::I32DivU | BinOp::I32RemS | BinOp::I32RemU
    )
}

struct CliffWalker<'a> {
    registry: &'a StratumRegistry,
    metrics: RegionCliffMetrics,
}

impl<'a> CliffWalker<'a> {
    fn new(registry: &'a StratumRegistry) -> Self {
        Self { registry, metrics: RegionCliffMetrics::default() }
    }

    fn record_depth(&mut self, d: DepthPair) {
        self.metrics.max_nonlinear_chain_depth =
            self.metrics.max_nonlinear_chain_depth.max(d.any);
        self.metrics.max_nonlinear64_chain_depth =
            self.metrics.max_nonlinear64_chain_depth.max(d.bits64);
    }

    fn walk_region(
        &mut self,
        r: RegionRef<'_>,
        val_depths: &mut BTreeMap<ValId, DepthPair>,
        branch_depth: u32,
        loop_depth: u32,
        call_depth: u32,
    ) -> WalkOutcome {
        match r.node {
            RegionNode::Block(stmts) => {
                self.walk_block(r, stmts, val_depths, branch_depth, loop_depth, call_depth)
            }
            RegionNode::IfElse { cond: _, then_region, else_region, .. } => {
                self.metrics.ssa_nodes += 1;
                let next_branch = branch_depth.saturating_add(1);
                self.metrics.max_branch_depth = self.metrics.max_branch_depth.max(next_branch);

                let mut outcome = WalkOutcome::default();
                if let Some(then_r) = r.child(then_region) {
                    let mut then_depths = val_depths.clone();
                    let t_out = self.walk_region(
                        then_r,
                        &mut then_depths,
                        next_branch,
                        loop_depth,
                        call_depth,
                    );
                    merge_depth_vecs(&mut outcome.exits, &t_out.exits);
                    merge_depth_vecs(&mut outcome.continues0, &t_out.continues0);
                }
                if let Some(else_r) = r.child(else_region) {
                    let mut else_depths = val_depths.clone();
                    let e_out = self.walk_region(
                        else_r,
                        &mut else_depths,
                        next_branch,
                        loop_depth,
                        call_depth,
                    );
                    merge_depth_vecs(&mut outcome.exits, &e_out.exits);
                    merge_depth_vecs(&mut outcome.continues0, &e_out.continues0);
                }
                outcome
            }
            RegionNode::BoundedLoop { max_iters, init_vars, state_vars, body } => {
                self.metrics.ssa_nodes += 1;
                self.metrics.bounded_loops += 1;
                self.metrics.max_bounded_loop_iters =
                    self.metrics.max_bounded_loop_iters.max(max_iters);
                let next_loop = loop_depth.saturating_add(1);
                self.metrics.max_loop_depth = self.metrics.max_loop_depth.max(next_loop);

                let init_depths: Vec<DepthPair> = r
                    .vals(init_vars)
                    .map(|v| val_depths.get(&v).copied().unwrap_or(DepthPair::ZERO))
                    .collect();
                let mut body_depths = val_depths.clone();
                for ((sv, _), &d) in r.vars(state_vars).zip(&init_depths) {
                    body_depths.insert(sv, d);
                }
                let mut outcome = WalkOutcome::default();
                if let Some(body_r) = r.child(body) {
                    let body_out = self.walk_region(
                        body_r,
                        &mut body_depths,
                        branch_depth,
                        next_loop,
                        call_depth,
                    );
                    // Estimate loop-carried nonlinear chain amplification across unrolled iters.
                    let unroll_factor = max_iters.min(MAX_SMT_LOOP_UNROLL);
                    let mut max_amp = DepthPair::ZERO;
                    for (init_d, cont_d) in init_depths.iter().zip(&body_out.continues0) {
                        let delta_any = cont_d.any.saturating_sub(init_d.any);
                        let delta_64 = cont_d.bits64.saturating_sub(init_d.bits64);
                        if delta_any > 0 || delta_64 > 0 {
                            let amplified = DepthPair {
                                any: init_d.any.saturating_add(delta_any.saturating_mul(unroll_factor)),
                                bits64: init_d
                                    .bits64
                                    .saturating_add(delta_64.saturating_mul(unroll_factor)),
                            };
                            self.record_depth(amplified);
                            max_amp = max_amp.max(amplified);
                        }
                    }
                    outcome.exits = body_out
                        .exits
                        .into_iter()
                        .map(|d| d.max(max_amp))
                        .collect();
                }
                outcome
            }
            RegionNode::InvariantLoop {
                init_vars,
                state_vars,
                cond,
                invariant_pred,
                fuel_measure,
                body,
            } => {
                self.metrics.ssa_nodes += 1;
                self.metrics.invariant_loops += 1;
                self.metrics.has_unbounded_loop = true;
                let next_loop = loop_depth.saturating_add(1);
                self.metrics.max_loop_depth = self.metrics.max_loop_depth.max(next_loop);

                let init_depths: Vec<DepthPair> = r
                    .vals(init_vars)
                    .map(|v| val_depths.get(&v).copied().unwrap_or(DepthPair::ZERO))
                    .collect();
                let mut loop_depths = val_depths.clone();
                for ((sv, _), &d) in r.vars(state_vars).zip(&init_depths) {
                    loop_depths.insert(sv, d);
                }
                for sub_id in [cond, invariant_pred, fuel_measure] {
                    if let Some(sub_r) = r.child(sub_id) {
                        let mut sub_env = loop_depths.clone();
                        let _ = self.walk_region(
                            sub_r,
                            &mut sub_env,
                            branch_depth,
                            next_loop,
                            call_depth,
                        );
                    }
                }
                let mut outcome = WalkOutcome::default();
                if let Some(body_r) = r.child(body) {
                    let mut body_env = loop_depths;
                    let body_out = self.walk_region(
                        body_r,
                        &mut body_env,
                        branch_depth,
                        next_loop,
                        call_depth,
                    );
                    outcome.exits = body_out.exits;
                }
                outcome
            }
        }
    }

    fn walk_block(
        &mut self,
        r: RegionRef<'_>,
        stmts: Span,
        val_depths: &mut BTreeMap<ValId, DepthPair>,
        branch_depth: u32,
        loop_depth: u32,
        call_depth: u32,
    ) -> WalkOutcome {
        let mut outcome = WalkOutcome::default();
        for stmt in r.stmts(stmts) {
            self.metrics.ssa_nodes += 1;
            match stmt {
                Stmt::Let { dst, op, .. } => {
                    let d = match op {
                        Op::ConstI32(_)
                        | Op::ConstI64(_)
                        | Op::GlobalGet(_)
                        | Op::MemorySize(_)
                        | Op::Load { .. }
                        | Op::MemoryGrow { .. } => DepthPair::ZERO,
                        Op::Copy(a) | Op::Un(_, a) => {
                            val_depths.get(&a).copied().unwrap_or(DepthPair::ZERO)
                        }
                        Op::Select { cond, true_val, false_val } => {
                            let c = val_depths.get(&cond).copied().unwrap_or(DepthPair::ZERO);
                            let t = val_depths.get(&true_val).copied().unwrap_or(DepthPair::ZERO);
                            let f = val_depths.get(&false_val).copied().unwrap_or(DepthPair::ZERO);
                            c.max(t).max(f)
                        }
                        Op::Bin(bin, l, r_val) => {
                            let ld = val_depths.get(&l).copied().unwrap_or(DepthPair::ZERO);
                            let rd = val_depths.get(&r_val).copied().unwrap_or(DepthPair::ZERO);
                            let base = ld.max(rd);
                            if is_nonlinear_64(bin) {
                                self.metrics.nonlinear_ops += 1;
                                self.metrics.nonlinear64_ops += 1;
                                DepthPair {
                                    any: base.any.saturating_add(1),
                                    bits64: base.bits64.saturating_add(1),
                                }
                            } else if is_nonlinear_32(bin) {
                                self.metrics.nonlinear_ops += 1;
                                DepthPair { any: base.any.saturating_add(1), bits64: base.bits64 }
                            } else {
                                base
                            }
                        }
                    };
                    self.record_depth(d);
                    val_depths.insert(dst, d);
                }
                Stmt::Effect(eff) => match eff {
                    EffectOp::Store { .. }
                    | EffectOp::MemoryCopy { .. }
                    | EffectOp::MemoryFill { .. } => {
                        self.metrics.mem_stores += 1;
                        if branch_depth > 0 {
                            self.metrics.conditional_mem_stores += 1;
                        }
                    }
                    EffectOp::GlobalSet { .. } | EffectOp::Trap(_) | EffectOp::Nop => {}
                },
                Stmt::Region { results, region } => {
                    let sub_out = if let Some(sub_r) = r.child(region) {
                        let mut sub_env = val_depths.clone();
                        self.walk_region(sub_r, &mut sub_env, branch_depth, loop_depth, call_depth)
                    } else {
                        WalkOutcome::default()
                    };
                    for (i, (res_id, _)) in r.vars(results).enumerate() {
                        let d = sub_out.exits.get(i).copied().unwrap_or(DepthPair::ZERO);
                        val_depths.insert(res_id, d);
                    }
                }
                Stmt::Call { results, target, args } => {
                    let arg_depths: Vec<DepthPair> = r
                        .vals(args)
                        .map(|v| val_depths.get(&v).copied().unwrap_or(DepthPair::ZERO))
                        .collect();
                    let max_arg = arg_depths
                        .iter()
                        .copied()
                        .fold(DepthPair::ZERO, DepthPair::max);

                    let res_depths = match target {
                        CallTarget::Stratum(sid) => {
                            self.metrics.stratum_calls += 1;
                            // Pure-total Strata are UF-abstracted by CEGAR; only inline metrics
                            // for impure/partial Strata that the SMT encoder must bit-blast.
                            if !is_pure_total_stratum(sid, self.registry, 0)
                                && call_depth < MAX_CALL_DEPTH
                                && let Some(op) = self.registry.get_op(sid)
                            {
                                let mut sub_env = BTreeMap::new();
                                for (&(pid, _), &ad) in op.params.iter().zip(&arg_depths) {
                                    sub_env.insert(pid, ad);
                                }
                                let sub_out = self.walk_region(
                                    op.body.as_ref(),
                                    &mut sub_env,
                                    branch_depth,
                                    loop_depth,
                                    call_depth + 1,
                                );
                                sub_out.exits
                            } else {
                                vec![max_arg; results.len_usize()]
                            }
                        }
                        CallTarget::Func(_) | CallTarget::Host(_) => {
                            vec![max_arg; results.len_usize()]
                        }
                    };
                    for (i, (res_id, _)) in r.vars(results).enumerate() {
                        let d = res_depths.get(i).copied().unwrap_or(max_arg);
                        val_depths.insert(res_id, d);
                    }
                }
                Stmt::Yield(vs) | Stmt::Return(vs) => {
                    let ds: Vec<DepthPair> = r
                        .vals(vs)
                        .map(|v| val_depths.get(&v).copied().unwrap_or(DepthPair::ZERO))
                        .collect();
                    merge_depth_vecs(&mut outcome.exits, &ds);
                }
                Stmt::Break { depth, values, .. } => {
                    if depth == 0 {
                        let ds: Vec<DepthPair> = r
                            .vals(values)
                            .map(|v| val_depths.get(&v).copied().unwrap_or(DepthPair::ZERO))
                            .collect();
                        merge_depth_vecs(&mut outcome.exits, &ds);
                    }
                }
                Stmt::Continue { depth, values, .. } => {
                    if depth == 0 {
                        let ds: Vec<DepthPair> = r
                            .vals(values)
                            .map(|v| val_depths.get(&v).copied().unwrap_or(DepthPair::ZERO))
                            .collect();
                        merge_depth_vecs(&mut outcome.continues0, &ds);
                    }
                }
            }
        }
        outcome
    }
}

fn classify_metrics(m: &mut RegionCliffMetrics) {
    let mut level = CliffLevel::Low;
    let mut warnings = Vec::new();

    if m.max_nonlinear64_chain_depth >= 3 || m.nonlinear64_ops >= 6 {
        level = level.max(CliffLevel::High);
        warnings.push(format!(
            "high 64-bit nonlinear chain depth ({}, {} 64-bit nonlinear ops): extract pure inner mixer as a Layer-k Stratum for UF CEGAR",
            m.max_nonlinear64_chain_depth, m.nonlinear64_ops
        ));
    } else if m.max_nonlinear64_chain_depth == 2 || m.nonlinear64_ops >= 2 {
        level = level.max(CliffLevel::Medium);
        warnings.push(format!(
            "moderate 64-bit nonlinear arithmetic (chain depth {}, {} ops): consider extracting pure nonlinear sub-expressions into a Layer-k Stratum",
            m.max_nonlinear64_chain_depth, m.nonlinear64_ops
        ));
    } else if m.max_nonlinear_chain_depth >= 5 {
        level = level.max(CliffLevel::High);
        warnings.push(format!(
            "deep nonlinear arithmetic chain (depth {}, {} total nonlinear ops): extract pure arithmetic sub-region as a Layer-k Stratum for UF CEGAR",
            m.max_nonlinear_chain_depth, m.nonlinear_ops
        ));
    } else if m.max_nonlinear_chain_depth >= 3 {
        level = level.max(CliffLevel::Medium);
        warnings.push(format!(
            "moderate nonlinear arithmetic chain (depth {}, {} total nonlinear ops): consider factoring into a Layer-k Stratum",
            m.max_nonlinear_chain_depth, m.nonlinear_ops
        ));
    }

    if m.conditional_mem_stores >= 4 {
        level = level.max(CliffLevel::High);
        warnings.push(format!(
            "conditional memory stores ({}): flatten into straight-line constant-address stores to keep QF_ABV read-over-write O(1)",
            m.conditional_mem_stores
        ));
    } else if m.conditional_mem_stores >= 1 {
        level = level.max(CliffLevel::Medium);
        warnings.push(format!(
            "conditional memory stores ({}): flatten into straight-line constant-address stores to keep QF_ABV read-over-write O(1)",
            m.conditional_mem_stores
        ));
    }

    if m.has_unbounded_loop {
        level = level.max(CliffLevel::High);
        warnings.push(format!(
            "unbounded InvariantLoop present ({}): split via split_invariant_loop into base/step/exit VCs before SMT encoding",
            m.invariant_loops
        ));
    }

    if m.max_bounded_loop_iters > MAX_SMT_LOOP_UNROLL {
        level = level.max(CliffLevel::High);
        warnings.push(format!(
            "bounded loop max_iters ({}) exceeds SMT unroll limit ({}): tighten loop bound or replace with an InvariantLoop",
            m.max_bounded_loop_iters, MAX_SMT_LOOP_UNROLL
        ));
    }

    if m.max_loop_depth >= 3 {
        level = level.max(CliffLevel::High);
        warnings.push(format!(
            "deep nested loops (depth {}): unrolling multiplies path and array-store terms exponentially; factor inner loops into verified Strata",
            m.max_loop_depth
        ));
    } else if m.max_loop_depth >= 2 {
        level = level.max(CliffLevel::Medium);
        warnings.push(format!(
            "nested loops (depth {}): consider factoring inner loop into a verified Stratum",
            m.max_loop_depth
        ));
    }

    if m.ssa_nodes >= 2000 {
        level = level.max(CliffLevel::High);
        warnings.push(format!(
            "very large SSA region ({} nodes): decompose into smaller Strata or contract-verified helper functions",
            m.ssa_nodes
        ));
    } else if m.ssa_nodes >= 500 {
        level = level.max(CliffLevel::Medium);
        warnings.push(format!(
            "large SSA region ({} nodes): consider decomposing into smaller Strata for faster SMT solving",
            m.ssa_nodes
        ));
    }

    m.level = level;
    m.warnings = warnings;
}

/// Estimates static SMT-cliff complexity metrics and risk level for a single `Region`.
pub fn estimate_region_cliff(region: &Region, registry: &StratumRegistry) -> RegionCliffMetrics {
    let mut walker = CliffWalker::new(registry);
    let mut val_depths = BTreeMap::new();
    let _ = walker.walk_region(region.as_ref(), &mut val_depths, 0, 0, 0);
    classify_metrics(&mut walker.metrics);
    walker.metrics
}

/// Estimates static SMT-cliff complexity across every function in a `Module`.
pub fn estimate_smt_cliff(module: &Module, registry: &StratumRegistry) -> CliffReport {
    let mut report = CliffReport::default();

    for func in &module.funcs {
        let metrics = estimate_region_cliff(&func.body, registry);
        report.level = report.level.max(metrics.level);
        report.total_ssa_nodes += metrics.ssa_nodes;
        report.total_nonlinear_ops += metrics.nonlinear_ops;
        report.total_nonlinear64_ops += metrics.nonlinear64_ops;
        report.max_nonlinear_chain_depth =
            report.max_nonlinear_chain_depth.max(metrics.max_nonlinear_chain_depth);
        report.max_nonlinear64_chain_depth =
            report.max_nonlinear64_chain_depth.max(metrics.max_nonlinear64_chain_depth);
        report.total_mem_stores += metrics.mem_stores;
        report.total_conditional_mem_stores += metrics.conditional_mem_stores;
        report.max_loop_depth = report.max_loop_depth.max(metrics.max_loop_depth);
        report.has_unbounded_loop |= metrics.has_unbounded_loop;

        let label = func.export_name.as_deref().unwrap_or(&func.name);
        for w in &metrics.warnings {
            report.warnings.push(format!("[fn {label}] {w}"));
        }

        report.functions.push(FuncCliffReport {
            func_id: func.id.0,
            name: func.name.clone(),
            export_name: func.export_name.clone(),
            metrics,
        });
    }

    report
}
