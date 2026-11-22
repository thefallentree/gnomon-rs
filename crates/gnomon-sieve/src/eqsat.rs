//! Step-capped `egglog` v3.0 regional simplifier for `GnomonIR`.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::time::Instant;

use egglog::ast::{Action, Command, Literal};
use egglog::prelude::{EGraph, exprs};
use egglog::{Term, TermDag, TermId, Value, add_primitive};
use gnomon_kernel::{
    BinOp, CallTarget, EffectOp, GlobalId, LawKind, MemId, MemWidth, Op, Region, Stmt, StratumId,
    StratumRegistry, UnOp, ValId, ValType, validate_read_only_with_registry,
};

use crate::{EqSatConfig, EqSatReport, SieveError};

const MAX_ALLOWED_ITERS: usize = 5;
const MAX_ALLOWED_NODES: usize = 5_000;

/// Step-capped `egglog` v3.0 equality-saturation simplifier over `GnomonIR` regions.
#[derive(Clone, Debug)]
pub struct EgglogSimplifier {
    config: EqSatConfig,
}

impl Default for EgglogSimplifier {
    fn default() -> Self {
        Self::new(EqSatConfig::default())
    }
}

impl EgglogSimplifier {
    pub fn new(config: EqSatConfig) -> Self {
        Self { config }
    }

    pub fn config(&self) -> EqSatConfig {
        self.config
    }

    /// Simplifies `region` using built-in sound Wasm BV/algebraic rules, disjoint
    /// memory-frame rules, and proved laws from `registry`, enforcing `EqSatConfig` caps.
    pub fn simplify_region(
        &self,
        region: &Region,
        registry: &StratumRegistry,
    ) -> Result<(Region, EqSatReport), SieveError> {
        let nodes_before = count_region_nodes(region);
        let max_iters = self.config.max_iters.min(MAX_ALLOWED_ITERS);
        let max_nodes = self.config.max_nodes.min(MAX_ALLOWED_NODES);
        let deadline = Instant::now();

        let mut next_fresh = max_val_id_in_region(region) + 1;
        let inferred_outer = infer_free_var_types(region, registry);
        let mut agg = ReportAcc::default();
        let simplified = self.simplify_inner(
            region,
            registry,
            &inferred_outer,
            &mut next_fresh,
            max_iters,
            max_nodes,
            deadline,
            &mut agg,
        )?;
        let nodes_after = count_region_nodes(&simplified);

        Ok((
            simplified,
            EqSatReport {
                iters_run: agg.iters_run,
                laws_fired: agg.laws_fired.into_iter().collect(),
                nodes_before,
                nodes_after,
            },
        ))
    }

    #[allow(clippy::too_many_arguments)]
    fn simplify_inner(
        &self,
        region: &Region,
        registry: &StratumRegistry,
        outer_types: &BTreeMap<ValId, ValType>,
        next_fresh: &mut u32,
        max_iters: usize,
        max_nodes: usize,
        start: Instant,
        agg: &mut ReportAcc,
    ) -> Result<Region, SieveError> {
        match region {
            Region::Block(stmts) => self.simplify_block(
                stmts,
                registry,
                outer_types,
                next_fresh,
                max_iters,
                max_nodes,
                start,
                agg,
            ),
            Region::IfElse { cond, then_region, else_region, results } => {
                let mut child_types = outer_types.clone();
                child_types.entry(*cond).or_insert(ValType::I32);
                let then_s = self.simplify_inner(
                    then_region,
                    registry,
                    &child_types,
                    next_fresh,
                    max_iters,
                    max_nodes,
                    start,
                    agg,
                )?;
                let else_s = self.simplify_inner(
                    else_region,
                    registry,
                    &child_types,
                    next_fresh,
                    max_iters,
                    max_nodes,
                    start,
                    agg,
                )?;
                Ok(Region::IfElse {
                    cond: *cond,
                    then_region: Box::new(then_s),
                    else_region: Box::new(else_s),
                    results: results.clone(),
                })
            }
            Region::BoundedLoop { max_iters: loop_iters, init_vars, state_vars, body } => {
                let mut child_types = outer_types.clone();
                for &(id, ty) in state_vars {
                    child_types.insert(id, ty);
                }
                let body_s = self.simplify_inner(
                    body,
                    registry,
                    &child_types,
                    next_fresh,
                    max_iters,
                    max_nodes,
                    start,
                    agg,
                )?;
                Ok(Region::BoundedLoop {
                    max_iters: *loop_iters,
                    init_vars: init_vars.clone(),
                    state_vars: state_vars.clone(),
                    body: Box::new(body_s),
                })
            }
            Region::InvariantLoop {
                init_vars,
                state_vars,
                cond,
                invariant_pred,
                fuel_measure,
                body,
            } => {
                let mut child_types = outer_types.clone();
                for &(id, ty) in state_vars {
                    child_types.insert(id, ty);
                }
                Ok(Region::InvariantLoop {
                    init_vars: init_vars.clone(),
                    state_vars: state_vars.clone(),
                    cond: Box::new(self.simplify_inner(
                        cond,
                        registry,
                        &child_types,
                        next_fresh,
                        max_iters,
                        max_nodes,
                        start,
                        agg,
                    )?),
                    invariant_pred: Box::new(self.simplify_inner(
                        invariant_pred,
                        registry,
                        &child_types,
                        next_fresh,
                        max_iters,
                        max_nodes,
                        start,
                        agg,
                    )?),
                    fuel_measure: Box::new(self.simplify_inner(
                        fuel_measure,
                        registry,
                        &child_types,
                        next_fresh,
                        max_iters,
                        max_nodes,
                        start,
                        agg,
                    )?),
                    body: Box::new(self.simplify_inner(
                        body,
                        registry,
                        &child_types,
                        next_fresh,
                        max_iters,
                        max_nodes,
                        start,
                        agg,
                    )?),
                })
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn simplify_block(
        &self,
        stmts: &[Stmt],
        registry: &StratumRegistry,
        outer_types: &BTreeMap<ValId, ValType>,
        next_fresh: &mut u32,
        max_iters: usize,
        max_nodes: usize,
        start: Instant,
        agg: &mut ReportAcc,
    ) -> Result<Region, SieveError> {
        if stmts.is_empty() {
            return Ok(Region::Block(Vec::new()));
        }

        let mut egraph = build_egraph(registry)?;
        let mut program = String::new();
        let mut val_env: HashMap<ValId, (ValType, String)> = HashMap::new();
        for (&id, &ty) in outer_types {
            val_env.insert(id, (ty, format!("(Var {} {})", id.0, ty_tag(ty))));
        }

        let mut heap_sym = "$h0".to_string();
        program.push_str("(let $h0 (InitHeap))\n");
        let mut heap_seq = 1usize;
        let mut global_epoch = 0usize;
        let mut let_seq = 0usize;

        let mut plans = Vec::with_capacity(stmts.len());
        let mut child_types = outer_types.clone();

        for stmt in stmts {
            match stmt {
                Stmt::Let { dst, ty, op } => {
                    if let Op::MemoryGrow { mem, delta } = op {
                        let delta_expr = lookup_egg(&val_env, *delta, ValType::I32);
                        heap_seq += 1;
                        let new_h = format!("$h{heap_seq}");
                        program.push_str(&format!("(let {new_h} (OpaqueHeap {heap_seq}))\n"));
                        heap_sym = new_h;
                        val_env.insert(*dst, (*ty, format!("(Var {} {})", dst.0, ty_tag(*ty))));
                        child_types.insert(*dst, *ty);
                        plans.push(StmtPlan::MemoryGrow {
                            dst: *dst,
                            mem: *mem,
                            delta_expr,
                        });
                        continue;
                    }
                    let sym = format!("$v{let_seq}");
                    let_seq += 1;
                    let expr_str = encode_op(
                        op,
                        *ty,
                        &val_env,
                        &heap_sym,
                        global_epoch,
                    );
                    program.push_str(&format!("(let {sym} {expr_str})\n"));
                    val_env.insert(*dst, (*ty, sym.clone()));
                    child_types.insert(*dst, *ty);
                    plans.push(StmtPlan::Let {
                        dst: *dst,
                        ty: *ty,
                        op: *op,
                        egglog_sym: sym,
                    });
                }
                Stmt::Effect(eff) => match eff {
                    EffectOp::Nop => plans.push(StmtPlan::Nop),
                    EffectOp::Store { mem, addr, offset, width, val } => {
                        let addr_e = lookup_egg(&val_env, *addr, ValType::I32);
                        let v_ty = val_env
                            .get(val)
                            .map(|&(t, _)| t)
                            .unwrap_or(if *width == MemWidth::B8 { ValType::I64 } else { ValType::I32 });
                        let val_e = lookup_egg(&val_env, *val, v_ty);
                        let new_h = format!("$h{heap_seq}");
                        heap_seq += 1;
                        program.push_str(&format!(
                            "(let {new_h} (StoreHeap {} {heap_sym} {addr_e} {} {} {val_e} {}))\n",
                            mem.0,
                            offset,
                            width.bytes(),
                            ty_tag(v_ty)
                        ));
                        heap_sym = new_h;
                        plans.push(StmtPlan::Effect(
                            *eff,
                            vec![(addr_e, ValType::I32), (val_e, v_ty)],
                        ));
                    }
                    EffectOp::MemoryCopy { dst_mem, src_mem, dst, src, len } => {
                        let _ = (dst_mem, src_mem);
                        let dst_e = lookup_egg(&val_env, *dst, ValType::I32);
                        let src_e = lookup_egg(&val_env, *src, ValType::I32);
                        let len_e = lookup_egg(&val_env, *len, ValType::I32);
                        let new_h = format!("$h{heap_seq}");
                        heap_seq += 1;
                        program.push_str(&format!("(let {new_h} (OpaqueHeap {heap_seq}))\n"));
                        heap_sym = new_h;
                        plans.push(StmtPlan::Effect(
                            *eff,
                            vec![
                                (dst_e, ValType::I32),
                                (src_e, ValType::I32),
                                (len_e, ValType::I32),
                            ],
                        ));
                    }
                    EffectOp::MemoryFill { mem: _, dst, val, len } => {
                        let dst_e = lookup_egg(&val_env, *dst, ValType::I32);
                        let val_e = lookup_egg(&val_env, *val, ValType::I32);
                        let len_e = lookup_egg(&val_env, *len, ValType::I32);
                        let new_h = format!("$h{heap_seq}");
                        heap_seq += 1;
                        program.push_str(&format!("(let {new_h} (OpaqueHeap {heap_seq}))\n"));
                        heap_sym = new_h;
                        plans.push(StmtPlan::Effect(
                            *eff,
                            vec![
                                (dst_e, ValType::I32),
                                (val_e, ValType::I32),
                                (len_e, ValType::I32),
                            ],
                        ));
                    }
                    EffectOp::GlobalSet { id: _, val } => {
                        let (v_ty, val_e) = lookup_egg_typed(&val_env, *val, ValType::I32);
                        global_epoch += 1;
                        plans.push(StmtPlan::Effect(*eff, vec![(val_e, v_ty)]));
                    }
                    EffectOp::Trap(_) => {
                        plans.push(StmtPlan::Effect(*eff, Vec::new()));
                    }
                },
                Stmt::Call { results, target, args } => {
                    let typed_args: Vec<(String, ValType)> = args
                        .iter()
                        .map(|id| {
                            let (ty, s) = lookup_egg_typed(&val_env, *id, ValType::I32);
                            (s, ty)
                        })
                        .collect();
                    let arg_exprs_only: Vec<String> =
                        typed_args.iter().map(|(s, _)| s.clone()).collect();
                    let arg_list = encode_expr_list(&arg_exprs_only);
                    let is_ro = match target {
                        CallTarget::Stratum(sid) => registry
                            .get_op(*sid)
                            .is_some_and(|op| validate_read_only_with_registry(&op.body, registry)),
                        _ => false,
                    };
                    if let CallTarget::Stratum(sid) = target {
                        let reads_state = registry
                            .get_op(*sid)
                            .is_none_or(|op| region_reads_heap_or_global(&op.body, registry));
                        let (call_heap, call_epoch) = if reads_state {
                            (heap_sym.clone(), global_epoch)
                        } else {
                            ("(InitHeap)".to_string(), 0usize)
                        };
                        if !is_ro {
                            let new_h = format!("$h{heap_seq}");
                            heap_seq += 1;
                            program.push_str(&format!(
                                "(let {new_h} (CallHeap {} {arg_list} {heap_sym}))\n",
                                sid.0
                            ));
                            heap_sym = new_h;
                            global_epoch += 1;
                        }
                        if results.len() == 1 {
                            let (dst, ty) = results[0];
                            let sym = format!("$v{let_seq}");
                            let_seq += 1;
                            program.push_str(&format!(
                                "(let {sym} (StratumCall {} {call_heap} {call_epoch} {arg_list}))\n",
                                sid.0
                            ));
                            val_env.insert(dst, (ty, sym.clone()));
                            child_types.insert(dst, ty);
                            plans.push(StmtPlan::StratumCallSingle {
                                dst,
                                ty,
                                sid: *sid,
                                is_ro,
                                arg_exprs: typed_args,
                                egglog_sym: sym,
                            });
                            continue;
                        }
                    } else {
                        let new_h = format!("$h{heap_seq}");
                        heap_seq += 1;
                        program.push_str(&format!("(let {new_h} (OpaqueHeap {heap_seq}))\n"));
                        heap_sym = new_h;
                        global_epoch += 1;
                    }
                    for &(id, ty) in results {
                        val_env.insert(id, (ty, format!("(Var {} {})", id.0, ty_tag(ty))));
                        child_types.insert(id, ty);
                    }
                    plans.push(StmtPlan::CallOpaque {
                        results: results.clone(),
                        target: *target,
                        arg_exprs: typed_args,
                    });
                }
                Stmt::Region { results, region } => {
                    let sub_simplified = self.simplify_inner(
                        region,
                        registry,
                        &child_types,
                        next_fresh,
                        max_iters,
                        max_nodes,
                        start,
                        agg,
                    )?;
                    let outer_refs: Vec<(ValId, ValType, String)> =
                        collect_free_vars_in_region(&sub_simplified)
                            .into_iter()
                            .filter_map(|fid| {
                                val_env
                                    .get(&fid)
                                    .map(|(ty, expr_s)| (fid, *ty, expr_s.clone()))
                            })
                            .collect();
                    if !validate_read_only_with_registry(&sub_simplified, registry) {
                        let new_h = format!("$h{heap_seq}");
                        heap_seq += 1;
                        program.push_str(&format!("(let {new_h} (OpaqueHeap {heap_seq}))\n"));
                        heap_sym = new_h;
                        global_epoch += 1;
                    }
                    for &(id, ty) in results {
                        val_env.insert(id, (ty, format!("(Var {} {})", id.0, ty_tag(ty))));
                        child_types.insert(id, ty);
                    }
                    plans.push(StmtPlan::SubRegion {
                        results: results.clone(),
                        region: sub_simplified,
                        outer_refs,
                    });
                }
                Stmt::Yield(vs) => {
                    let es = vs
                        .iter()
                        .map(|id| {
                            let (ty, s) = lookup_egg_typed(&val_env, *id, ValType::I32);
                            (s, ty)
                        })
                        .collect();
                    plans.push(StmtPlan::Yield(es));
                }
                Stmt::Return(vs) => {
                    let es = vs
                        .iter()
                        .map(|id| {
                            let (ty, s) = lookup_egg_typed(&val_env, *id, ValType::I32);
                            (s, ty)
                        })
                        .collect();
                    plans.push(StmtPlan::Return(es));
                }
                Stmt::Break { depth, cond, values } => {
                    let ce = cond.map(|c| lookup_egg(&val_env, c, ValType::I32));
                    let es = values
                        .iter()
                        .map(|id| {
                            let (ty, s) = lookup_egg_typed(&val_env, *id, ValType::I32);
                            (s, ty)
                        })
                        .collect();
                    plans.push(StmtPlan::Break { depth: *depth, cond: ce, values: es });
                }
                Stmt::Continue { depth, cond, values } => {
                    let ce = cond.map(|c| lookup_egg(&val_env, c, ValType::I32));
                    let es = values
                        .iter()
                        .map(|id| {
                            let (ty, s) = lookup_egg_typed(&val_env, *id, ValType::I32);
                            (s, ty)
                        })
                        .collect();
                    plans.push(StmtPlan::Continue { depth: *depth, cond: ce, values: es });
                }
            }
        }

        egraph
            .parse_and_run_program(None, &program)
            .map_err(|e| SieveError::EqSatError(e.to_string()))?;

        // Step-capped saturation loop respecting max_iters, max_nodes, and timeout_ms.
        let mut block_iters = 0usize;
        for _ in 0..max_iters {
            if egraph.num_tuples() >= max_nodes {
                break;
            }
            if start.elapsed().as_millis() as u64 >= self.config.timeout_ms {
                break;
            }
            let report = egraph
                .step_rules("")
                .map_err(|e| SieveError::EqSatError(e.to_string()))?;
            block_iters += 1;
            for (rule_name, matches) in &report.num_matches_per_rule {
                if *matches > 0 {
                    agg.laws_fired.insert(rule_name.to_string());
                }
            }
            if !report.updated || egraph.num_tuples() >= max_nodes {
                break;
            }
        }
        agg.iters_run = agg.iters_run.max(block_iters);

        // Reconstruct simplified GnomonIR block preserving all potential traps and side effects.
        reconstruct_block(&mut egraph, &plans, registry, next_fresh)
    }
}

#[derive(Default)]
struct ReportAcc {
    iters_run: usize,
    laws_fired: BTreeSet<String>,
}

enum StmtPlan {
    Let {
        dst: ValId,
        ty: ValType,
        op: Op,
        egglog_sym: String,
    },
    MemoryGrow {
        dst: ValId,
        mem: MemId,
        delta_expr: String,
    },
    StratumCallSingle {
        dst: ValId,
        ty: ValType,
        sid: StratumId,
        is_ro: bool,
        arg_exprs: Vec<(String, ValType)>,
        egglog_sym: String,
    },
    CallOpaque {
        results: Vec<(ValId, ValType)>,
        target: CallTarget,
        arg_exprs: Vec<(String, ValType)>,
    },
    Effect(EffectOp, Vec<(String, ValType)>),
    SubRegion {
        results: Vec<(ValId, ValType)>,
        region: Region,
        outer_refs: Vec<(ValId, ValType, String)>,
    },
    Yield(Vec<(String, ValType)>),
    Return(Vec<(String, ValType)>),
    Break {
        depth: u32,
        cond: Option<String>,
        values: Vec<(String, ValType)>,
    },
    Continue {
        depth: u32,
        cond: Option<String>,
        values: Vec<(String, ValType)>,
    },
    Nop,
}

fn ty_tag(ty: ValType) -> i64 {
    match ty {
        ValType::I32 => 0,
        ValType::I64 => 1,
    }
}

fn width_bytes(w: MemWidth) -> i64 {
    w.bytes() as i64
}

fn bytes_to_width(bytes: i64) -> Option<MemWidth> {
    match bytes {
        1 => Some(MemWidth::B1),
        2 => Some(MemWidth::B2),
        4 => Some(MemWidth::B4),
        8 => Some(MemWidth::B8),
        _ => None,
    }
}

fn lookup_egg(env: &HashMap<ValId, (ValType, String)>, id: ValId, default_ty: ValType) -> String {
    lookup_egg_typed(env, id, default_ty).1
}

fn lookup_egg_typed(
    env: &HashMap<ValId, (ValType, String)>,
    id: ValId,
    default_ty: ValType,
) -> (ValType, String) {
    env.get(&id)
        .cloned()
        .unwrap_or_else(|| (default_ty, format!("(Var {} {})", id.0, ty_tag(default_ty))))
}

fn region_reads_heap_or_global(region: &Region, registry: &StratumRegistry) -> bool {
    match region {
        Region::Block(stmts) => stmts.iter().any(|s| match s {
            Stmt::Let { op, .. } => matches!(
                op,
                Op::Load { .. }
                    | Op::MemorySize(_)
                    | Op::MemoryGrow { .. }
                    | Op::GlobalGet(_)
            ),
            Stmt::Effect(eff) => !matches!(eff, EffectOp::Nop | EffectOp::Trap(_)),
            Stmt::Region { region: sub, .. } => region_reads_heap_or_global(sub, registry),
            Stmt::Call { target: CallTarget::Stratum(sid), .. } => registry
                .get_op(*sid)
                .is_none_or(|op| region_reads_heap_or_global(&op.body, registry)),
            Stmt::Call { .. } => true,
            Stmt::Yield(_) | Stmt::Break { .. } | Stmt::Continue { .. } | Stmt::Return(_) => false,
        }),
        Region::IfElse { then_region, else_region, .. } => {
            region_reads_heap_or_global(then_region, registry)
                || region_reads_heap_or_global(else_region, registry)
        }
        Region::BoundedLoop { body, .. } => region_reads_heap_or_global(body, registry),
        Region::InvariantLoop { cond, invariant_pred, fuel_measure, body, .. } => {
            region_reads_heap_or_global(cond, registry)
                || region_reads_heap_or_global(invariant_pred, registry)
                || region_reads_heap_or_global(fuel_measure, registry)
                || region_reads_heap_or_global(body, registry)
        }
    }
}

fn encode_expr_list(items: &[String]) -> String {
    let mut acc = "(ENil)".to_string();
    for item in items.iter().rev() {
        acc = format!("(ECons {item} {acc})");
    }
    acc
}

fn encode_op(
    op: &Op,
    ty: ValType,
    val_env: &HashMap<ValId, (ValType, String)>,
    heap_sym: &str,
    global_epoch: usize,
) -> String {
    match op {
        Op::ConstI32(v) => format!("(ConstI32 {})", *v as i64),
        Op::ConstI64(v) => format!("(ConstI64 {v})"),
        Op::Copy(id) => lookup_egg(val_env, *id, ty),
        Op::Select { cond, true_val, false_val } => format!(
            "(Select {} {} {})",
            lookup_egg(val_env, *cond, ValType::I32),
            lookup_egg(val_env, *true_val, ty),
            lookup_egg(val_env, *false_val, ty),
        ),
        Op::GlobalGet(gid) => format!("(GlobalGet {} {})", gid.0, (global_epoch * 2) + ty_tag(ty) as usize),
        Op::Un(u, a) => format!("(Un {} {})", unop_tag(*u), lookup_egg(val_env, *a, u.input_ty())),
        Op::Bin(b, l, r) => format!(
            "(Bin {} {} {})",
            binop_tag(*b),
            lookup_egg(val_env, *l, b.operand_ty()),
            lookup_egg(val_env, *r, b.operand_ty())
        ),
        Op::Load { mem, addr, offset, width, signed, result_ty } => format!(
            "(Load {} {heap_sym} {} {} {} {} {})",
            mem.0,
            lookup_egg(val_env, *addr, ValType::I32),
            offset,
            width_bytes(*width),
            i64::from(*signed),
            ty_tag(*result_ty)
        ),
        Op::MemorySize(mem) => format!("(MemSize {} {heap_sym})", mem.0),
        Op::MemoryGrow { .. } => unreachable!("MemoryGrow handled directly"),
    }
}

fn op_can_trap(op: &Op) -> bool {
    match op {
        Op::Load { .. } | Op::MemoryGrow { .. } => true,
        Op::Bin(b, _, _) => matches!(
            b,
            BinOp::I32DivS
                | BinOp::I32DivU
                | BinOp::I32RemS
                | BinOp::I32RemU
                | BinOp::I64DivS
                | BinOp::I64DivU
                | BinOp::I64RemS
                | BinOp::I64RemU
        ),
        _ => false,
    }
}

fn term_contains_trap_op(termdag: &TermDag, tid: TermId) -> bool {
    match termdag.get(tid) {
        Term::App(head, children) => {
            let root_traps = match head.as_str() {
                "Load" | "StratumCall" => true,
                "Bin" => children
                    .first()
                    .and_then(|&c| match termdag.get(c) {
                        Term::Lit(Literal::Int(tag)) => binop_from_tag(*tag),
                        _ => None,
                    })
                    .is_some_and(|b| {
                        matches!(
                            b,
                            BinOp::I32DivS
                                | BinOp::I32DivU
                                | BinOp::I32RemS
                                | BinOp::I32RemU
                                | BinOp::I64DivS
                                | BinOp::I64DivU
                                | BinOp::I64RemS
                                | BinOp::I64RemU
                        )
                    }),
                _ => false,
            };
            root_traps || children.iter().any(|&c| term_contains_trap_op(termdag, c))
        }
        _ => false,
    }
}

fn term_is_stratum_call(termdag: &TermDag, tid: TermId) -> bool {
    matches!(termdag.get(tid), Term::App(head, _) if head == "StratumCall")
}

fn extract_str(egraph: &mut EGraph, expr_str: &str) -> Result<(Value, TermDag, TermId), SieveError> {
    let expr = if expr_str.starts_with('$') {
        exprs::var(expr_str)
    } else {
        let parsed = egraph
            .parse_program(None, &format!("(extract {expr_str})"))
            .map_err(|e| SieveError::EqSatError(e.to_string()))?;
        match parsed.into_iter().next() {
            Some(Command::Extract(_, e, _)) => e,
            Some(Command::Action(Action::Expr(_, e))) => e,
            _ => return Err(SieveError::EqSatError(format!("failed to parse egglog expr: {expr_str}"))),
        }
    };
    let (sort, val) = egraph
        .eval_expr(&expr)
        .map_err(|e| SieveError::EqSatError(e.to_string()))?;
    let (dag, tid, _cost) = egraph
        .extract_value(&sort, val)
        .map_err(|e| SieveError::EqSatError(e.to_string()))?;
    Ok((val, dag, tid))
}

struct ReconstructCtx<'a> {
    registry: &'a StratumRegistry,
    out_stmts: Vec<Stmt>,
    next_fresh: &'a mut u32,
    eclass_to_val: HashMap<Value, (ValId, ValType)>,
    term_to_val: HashMap<String, (ValId, ValType)>,
    orig_to_val: HashMap<ValId, ValId>,
}

impl ReconstructCtx<'_> {
    fn fresh_id(&mut self) -> ValId {
        let id = ValId(*self.next_fresh);
        *self.next_fresh += 1;
        id
    }

    fn emit_term(
        &mut self,
        dag: &TermDag,
        tid: TermId,
        ty_hint: ValType,
    ) -> Result<(ValId, ValType), SieveError> {
        let key = dag.to_string(tid);
        if let Some(&(v, ty)) = self.term_to_val.get(&key) {
            return Ok((v, ty));
        }

        let (val_id, val_ty) = match dag.get(tid) {
            Term::App(head, children) => match head.as_str() {
                "Var" => {
                    let id = expect_int(dag, children[0])? as u32;
                    let ty = expect_ty(dag, children[1])?;
                    let mapped = self.orig_to_val.get(&ValId(id)).copied().unwrap_or(ValId(id));
                    return Ok((mapped, ty));
                }
                "ConstI32" => {
                    let v = expect_int(dag, children[0])? as i32;
                    let dst = self.fresh_id();
                    self.out_stmts.push(Stmt::Let { dst, ty: ValType::I32, op: Op::ConstI32(v) });
                    (dst, ValType::I32)
                }
                "ConstI64" => {
                    let v = expect_int(dag, children[0])?;
                    let dst = self.fresh_id();
                    self.out_stmts.push(Stmt::Let { dst, ty: ValType::I64, op: Op::ConstI64(v) });
                    (dst, ValType::I64)
                }
                "GlobalGet" => {
                    let gid = expect_int(dag, children[0])? as u32;
                    let epoch_ty = expect_int(dag, children[1])?;
                    let ty = if epoch_ty % 2 == 0 { ValType::I32 } else { ValType::I64 };
                    let dst = self.fresh_id();
                    self.out_stmts.push(Stmt::Let { dst, ty, op: Op::GlobalGet(GlobalId(gid)) });
                    (dst, ty)
                }
                "Select" => {
                    let (c, _) = self.emit_term(dag, children[0], ValType::I32)?;
                    let (t, t_ty) = self.emit_term(dag, children[1], ty_hint)?;
                    let (f, _) = self.emit_term(dag, children[2], t_ty)?;
                    let dst = self.fresh_id();
                    self.out_stmts.push(Stmt::Let {
                        dst,
                        ty: t_ty,
                        op: Op::Select { cond: c, true_val: t, false_val: f },
                    });
                    (dst, t_ty)
                }
                "Un" => {
                    let u_tag = expect_int(dag, children[0])?;
                    let u = unop_from_tag(u_tag)
                        .ok_or_else(|| SieveError::EqSatError(format!("bad UnOp tag {u_tag}")))?;
                    let (a, _) = self.emit_term(dag, children[1], u.input_ty())?;
                    let dst = self.fresh_id();
                    let out_ty = u.output_ty();
                    self.out_stmts.push(Stmt::Let { dst, ty: out_ty, op: Op::Un(u, a) });
                    (dst, out_ty)
                }
                "Bin" => {
                    let b_tag = expect_int(dag, children[0])?;
                    let b = binop_from_tag(b_tag)
                        .ok_or_else(|| SieveError::EqSatError(format!("bad BinOp tag {b_tag}")))?;
                    let (l, _) = self.emit_term(dag, children[1], b.operand_ty())?;
                    let (r, _) = self.emit_term(dag, children[2], b.operand_ty())?;
                    let dst = self.fresh_id();
                    let out_ty = b.output_ty();
                    self.out_stmts.push(Stmt::Let { dst, ty: out_ty, op: Op::Bin(b, l, r) });
                    (dst, out_ty)
                }
                "Load" => {
                    let mem = MemId(expect_int(dag, children[0])? as u16);
                    // children[1] is Heap (used for e-graph alias soundness, not an IR operand)
                    let (addr, _) = self.emit_term(dag, children[2], ValType::I32)?;
                    let offset = expect_int(dag, children[3])? as u32;
                    let w_b = expect_int(dag, children[4])?;
                    let width = bytes_to_width(w_b)
                        .ok_or_else(|| SieveError::EqSatError(format!("bad MemWidth {w_b}")))?;
                    let signed = expect_int(dag, children[5])? != 0;
                    let result_ty = expect_ty(dag, children[6])?;
                    let dst = self.fresh_id();
                    self.out_stmts.push(Stmt::Let {
                        dst,
                        ty: result_ty,
                        op: Op::Load { mem, addr, offset, width, signed, result_ty },
                    });
                    (dst, result_ty)
                }
                "MemSize" => {
                    let mem = MemId(expect_int(dag, children[0])? as u16);
                    let dst = self.fresh_id();
                    self.out_stmts.push(Stmt::Let {
                        dst,
                        ty: ValType::I32,
                        op: Op::MemorySize(mem),
                    });
                    (dst, ValType::I32)
                }
                "StratumCall" => {
                    let sid = StratumId(expect_int(dag, children[0])? as u32);
                    // children[1] is Heap, children[2] is global_epoch, children[3] is ExprList
                    let op = self
                        .registry
                        .get_op(sid)
                        .ok_or_else(|| SieveError::EqSatError(format!("unknown Stratum {sid:?}")))?;
                    let args = decode_expr_list(dag, children[3])?;
                    let mut arg_vals = Vec::with_capacity(args.len());
                    for (i, tid) in args.into_iter().enumerate() {
                        let pt = op.params.get(i).map(|&(_, t)| t).unwrap_or(ValType::I32);
                        arg_vals.push(self.emit_term(dag, tid, pt)?.0);
                    }
                    let res_ty = op.results.first().copied().unwrap_or(ty_hint);
                    let dst = self.fresh_id();
                    self.out_stmts.push(Stmt::Call {
                        results: vec![(dst, res_ty)],
                        target: CallTarget::Stratum(sid),
                        args: arg_vals,
                    });
                    (dst, res_ty)
                }
                other => {
                    return Err(SieveError::EqSatError(format!(
                        "unexpected egglog node '{other}' during extraction"
                    )));
                }
            },
            _ => return Err(SieveError::EqSatError("unexpected literal/var root in Expr".into())),
        };
        self.term_to_val.insert(key, (val_id, val_ty));
        Ok((val_id, val_ty))
    }

    fn emit_from_expr_str(
        &mut self,
        egraph: &mut EGraph,
        expr_str: &str,
        ty_hint: ValType,
    ) -> Result<ValId, SieveError> {
        let (val, dag, tid) = extract_str(egraph, expr_str)?;
        if let Some(&(existing, _)) = self.eclass_to_val.get(&val) {
            return Ok(existing);
        }
        let (id, ty) = self.emit_term(&dag, tid, ty_hint)?;
        self.eclass_to_val.insert(val, (id, ty));
        Ok(id)
    }
}

fn expect_int(dag: &TermDag, tid: TermId) -> Result<i64, SieveError> {
    match dag.get(tid) {
        Term::Lit(Literal::Int(v)) => Ok(*v),
        other => Err(SieveError::EqSatError(format!("expected int literal in egglog term, got {other:?}"))),
    }
}

fn expect_ty(dag: &TermDag, tid: TermId) -> Result<ValType, SieveError> {
    match expect_int(dag, tid)? {
        0 => Ok(ValType::I32),
        1 => Ok(ValType::I64),
        other => Err(SieveError::EqSatError(format!("invalid type tag {other}"))),
    }
}

fn decode_expr_list(dag: &TermDag, mut tid: TermId) -> Result<Vec<TermId>, SieveError> {
    let mut out = Vec::new();
    loop {
        match dag.get(tid) {
            Term::App(head, children) if head == "ENil" => return Ok(out),
            Term::App(head, children) if head == "ECons" => {
                out.push(children[0]);
                tid = children[1];
            }
            other => {
                return Err(SieveError::EqSatError(format!(
                    "malformed ExprList node in egglog extraction: {other:?}"
                )));
            }
        }
    }
}

fn reconstruct_block(
    egraph: &mut EGraph,
    plans: &[StmtPlan],
    registry: &StratumRegistry,
    next_fresh: &mut u32,
) -> Result<Region, SieveError> {
    let mut ctx = ReconstructCtx {
        registry,
        out_stmts: Vec::new(),
        next_fresh,
        eclass_to_val: HashMap::new(),
        term_to_val: HashMap::new(),
        orig_to_val: HashMap::new(),
    };

    for plan in plans {
        match plan {
            StmtPlan::Nop => {}
            StmtPlan::MemoryGrow { dst, mem, delta_expr } => {
                let delta_id = ctx.emit_from_expr_str(egraph, delta_expr, ValType::I32)?;
                let new_dst = ctx.fresh_id();
                ctx.out_stmts.push(Stmt::Let {
                    dst: new_dst,
                    ty: ValType::I32,
                    op: Op::MemoryGrow { mem: *mem, delta: delta_id },
                });
                ctx.orig_to_val.insert(*dst, new_dst);
            }
            StmtPlan::Let { dst, ty, op, egglog_sym } => {
                let (val, dag, tid) = extract_str(egraph, egglog_sym)?;
                if let Some(&(already, _)) = ctx.eclass_to_val.get(&val) {
                    ctx.orig_to_val.insert(*dst, already);
                    continue;
                }
                if op_can_trap(op) && term_contains_trap_op(&dag, tid) {
                    // Emit immediately in chronological order so potential trap semantics are preserved.
                    let (emitted, emitted_ty) = ctx.emit_term(&dag, tid, *ty)?;
                    ctx.eclass_to_val.insert(val, (emitted, emitted_ty));
                    ctx.orig_to_val.insert(*dst, emitted);
                } else {
                    // Pure non-trapping (or safely proven trap-free) binding: lazily emitted if used!
                    if let Term::App(h, ch) = dag.get(tid)
                        && h == "Var"
                    {
                        let orig = ValId(expect_int(&dag, ch[0])? as u32);
                        let mapped = ctx.orig_to_val.get(&orig).copied().unwrap_or(orig);
                        ctx.orig_to_val.insert(*dst, mapped);
                    }
                }
            }
            StmtPlan::StratumCallSingle { dst, ty, sid, is_ro, arg_exprs, egglog_sym } => {
                let (val, dag, tid) = extract_str(egraph, egglog_sym)?;
                if *is_ro {
                    if let Some(&(already, _)) = ctx.eclass_to_val.get(&val) {
                        ctx.orig_to_val.insert(*dst, already);
                        continue;
                    }
                    if term_contains_trap_op(&dag, tid) {
                        // Emit immediately in chronological order so StratumCall or any
                        // lowered trapping op (e.g. I32DivS / Load) is never dropped when unused.
                        let (emitted, emitted_ty) = ctx.emit_term(&dag, tid, *ty)?;
                        ctx.eclass_to_val.insert(val, (emitted, emitted_ty));
                        ctx.orig_to_val.insert(*dst, emitted);
                    } else if let Term::App(h, ch) = dag.get(tid)
                        && h == "Var"
                    {
                        let orig = ValId(expect_int(&dag, ch[0])? as u32);
                        let mapped = ctx.orig_to_val.get(&orig).copied().unwrap_or(orig);
                        ctx.orig_to_val.insert(*dst, mapped);
                    }
                } else if term_is_stratum_call(&dag, tid) {
                    let (emitted, _) = ctx.emit_term(&dag, tid, *ty)?;
                    ctx.orig_to_val.insert(*dst, emitted);
                } else {
                    // Impure stratum call whose return value simplified: evaluate simplified
                    // pre-call expression/args, keep the Call effect, and map/cache result cleanly.
                    let mut arg_ids = Vec::with_capacity(arg_exprs.len());
                    for (ae, aty) in arg_exprs {
                        arg_ids.push(ctx.emit_from_expr_str(egraph, ae, *aty)?);
                    }
                    let simplified_res = if let Term::App(h, ch) = dag.get(tid)
                        && h == "Var"
                    {
                        let orig = ValId(expect_int(&dag, ch[0])? as u32);
                        let mapped = ctx.orig_to_val.get(&orig).copied().unwrap_or(orig);
                        (mapped, None)
                    } else {
                        let (emitted, emitted_ty) = ctx.emit_term(&dag, tid, *ty)?;
                        (emitted, Some(emitted_ty))
                    };
                    let call_dst = ctx.fresh_id();
                    ctx.out_stmts.push(Stmt::Call {
                        results: vec![(call_dst, *ty)],
                        target: CallTarget::Stratum(*sid),
                        args: arg_ids,
                    });
                    if let Some(emitted_ty) = simplified_res.1 {
                        ctx.eclass_to_val.insert(val, (simplified_res.0, emitted_ty));
                    }
                    ctx.orig_to_val.insert(*dst, simplified_res.0);
                }
            }
            StmtPlan::CallOpaque { results, target, arg_exprs } => {
                let mut arg_ids = Vec::with_capacity(arg_exprs.len());
                for (ae, aty) in arg_exprs {
                    arg_ids.push(ctx.emit_from_expr_str(egraph, ae, *aty)?);
                }
                for &(id, _) in results {
                    ctx.orig_to_val.insert(id, id);
                }
                ctx.out_stmts.push(Stmt::Call {
                    results: results.clone(),
                    target: *target,
                    args: arg_ids,
                });
            }
            StmtPlan::Effect(eff, arg_exprs) => {
                let emitted_eff = match eff {
                    EffectOp::Store { mem, offset, width, .. } => {
                        let addr = ctx.emit_from_expr_str(egraph, &arg_exprs[0].0, arg_exprs[0].1)?;
                        let val = ctx.emit_from_expr_str(egraph, &arg_exprs[1].0, arg_exprs[1].1)?;
                        EffectOp::Store { mem: *mem, addr, offset: *offset, width: *width, val }
                    }
                    EffectOp::MemoryCopy { dst_mem, src_mem, .. } => {
                        let dst = ctx.emit_from_expr_str(egraph, &arg_exprs[0].0, ValType::I32)?;
                        let src = ctx.emit_from_expr_str(egraph, &arg_exprs[1].0, ValType::I32)?;
                        let len = ctx.emit_from_expr_str(egraph, &arg_exprs[2].0, ValType::I32)?;
                        EffectOp::MemoryCopy { dst_mem: *dst_mem, src_mem: *src_mem, dst, src, len }
                    }
                    EffectOp::MemoryFill { mem, .. } => {
                        let dst = ctx.emit_from_expr_str(egraph, &arg_exprs[0].0, ValType::I32)?;
                        let val = ctx.emit_from_expr_str(egraph, &arg_exprs[1].0, ValType::I32)?;
                        let len = ctx.emit_from_expr_str(egraph, &arg_exprs[2].0, ValType::I32)?;
                        EffectOp::MemoryFill { mem: *mem, dst, val, len }
                    }
                    EffectOp::GlobalSet { id, .. } => {
                        let val = ctx.emit_from_expr_str(egraph, &arg_exprs[0].0, arg_exprs[0].1)?;
                        EffectOp::GlobalSet { id: *id, val }
                    }
                    other => *other,
                };
                ctx.out_stmts.push(Stmt::Effect(emitted_eff));
            }
            StmtPlan::SubRegion { results, region, outer_refs } => {
                for &(fid, ty, ref expr_s) in outer_refs {
                    let emitted = ctx.emit_from_expr_str(egraph, expr_s, ty)?;
                    ctx.orig_to_val.insert(fid, emitted);
                }
                let remapped = remap_free_uses(region, &ctx.orig_to_val);
                for &(id, _) in results {
                    ctx.orig_to_val.insert(id, id);
                }
                ctx.out_stmts.push(Stmt::Region { results: results.clone(), region: remapped });
            }
            StmtPlan::Yield(es) => {
                let mut ids = Vec::with_capacity(es.len());
                for (e, ty) in es {
                    ids.push(ctx.emit_from_expr_str(egraph, e, *ty)?);
                }
                ctx.out_stmts.push(Stmt::Yield(ids));
            }
            StmtPlan::Return(es) => {
                let mut ids = Vec::with_capacity(es.len());
                for (e, ty) in es {
                    ids.push(ctx.emit_from_expr_str(egraph, e, *ty)?);
                }
                ctx.out_stmts.push(Stmt::Return(ids));
            }
            StmtPlan::Break { depth, cond, values } => {
                let c_id = match cond {
                    Some(ce) => Some(ctx.emit_from_expr_str(egraph, ce, ValType::I32)?),
                    None => None,
                };
                let mut ids = Vec::with_capacity(values.len());
                for (e, ty) in values {
                    ids.push(ctx.emit_from_expr_str(egraph, e, *ty)?);
                }
                ctx.out_stmts.push(Stmt::Break { depth: *depth, cond: c_id, values: ids });
            }
            StmtPlan::Continue { depth, cond, values } => {
                let c_id = match cond {
                    Some(ce) => Some(ctx.emit_from_expr_str(egraph, ce, ValType::I32)?),
                    None => None,
                };
                let mut ids = Vec::with_capacity(values.len());
                for (e, ty) in values {
                    ids.push(ctx.emit_from_expr_str(egraph, e, *ty)?);
                }
                ctx.out_stmts.push(Stmt::Continue { depth: *depth, cond: c_id, values: ids });
            }
        }
    }

    Ok(Region::Block(ctx.out_stmts))
}

fn collect_free_vars_in_region(region: &Region) -> BTreeSet<ValId> {
    fn walk(r: &Region, bound: &mut Vec<ValId>, free: &mut BTreeSet<ValId>) {
        let rec = |v: ValId, b: &[ValId], f: &mut BTreeSet<ValId>| {
            if !b.contains(&v) {
                f.insert(v);
            }
        };
        match r {
            Region::Block(stmts) => {
                let saved = bound.len();
                for s in stmts {
                    match s {
                        Stmt::Let { dst, op, .. } => {
                            match op {
                                Op::Copy(v) | Op::Un(_, v) | Op::Load { addr: v, .. } | Op::MemoryGrow { delta: v, .. } => {
                                    rec(*v, bound, free);
                                }
                                Op::Select { cond, true_val, false_val } => {
                                    rec(*cond, bound, free);
                                    rec(*true_val, bound, free);
                                    rec(*false_val, bound, free);
                                }
                                Op::Bin(_, l, r) => {
                                    rec(*l, bound, free);
                                    rec(*r, bound, free);
                                }
                                _ => {}
                            }
                            bound.push(*dst);
                        }
                        Stmt::Effect(eff) => match eff {
                            EffectOp::Store { addr, val, .. } => {
                                rec(*addr, bound, free);
                                rec(*val, bound, free);
                            }
                            EffectOp::MemoryCopy { dst, src, len, .. }
                            | EffectOp::MemoryFill { dst, val: src, len, .. } => {
                                rec(*dst, bound, free);
                                rec(*src, bound, free);
                                rec(*len, bound, free);
                            }
                            EffectOp::GlobalSet { val, .. } => rec(*val, bound, free),
                            EffectOp::Trap(_) | EffectOp::Nop => {}
                        },
                        Stmt::Region { results, region } => {
                            walk(region, bound, free);
                            for &(id, _) in results {
                                bound.push(id);
                            }
                        }
                        Stmt::Call { results, args, .. } => {
                            for &a in args {
                                rec(a, bound, free);
                            }
                            for &(id, _) in results {
                                bound.push(id);
                            }
                        }
                        Stmt::Yield(vs) | Stmt::Return(vs) => {
                            for &v in vs {
                                rec(v, bound, free);
                            }
                        }
                        Stmt::Break { cond, values, .. } | Stmt::Continue { cond, values, .. } => {
                            if let Some(c) = cond {
                                rec(*c, bound, free);
                            }
                            for &v in values {
                                rec(v, bound, free);
                            }
                        }
                    }
                }
                bound.truncate(saved);
            }
            Region::IfElse { cond, then_region, else_region, .. } => {
                rec(*cond, bound, free);
                walk(then_region, bound, free);
                walk(else_region, bound, free);
            }
            Region::BoundedLoop { init_vars, state_vars, body, .. } => {
                for &iv in init_vars {
                    rec(iv, bound, free);
                }
                let saved = bound.len();
                for &(sv, _) in state_vars {
                    bound.push(sv);
                }
                walk(body, bound, free);
                bound.truncate(saved);
            }
            Region::InvariantLoop {
                init_vars,
                state_vars,
                cond,
                invariant_pred,
                fuel_measure,
                body,
            } => {
                for &iv in init_vars {
                    rec(iv, bound, free);
                }
                let saved = bound.len();
                for &(sv, _) in state_vars {
                    bound.push(sv);
                }
                walk(cond, bound, free);
                walk(invariant_pred, bound, free);
                walk(fuel_measure, bound, free);
                walk(body, bound, free);
                bound.truncate(saved);
            }
        }
    }
    let mut free = BTreeSet::new();
    walk(region, &mut Vec::new(), &mut free);
    free
}

fn infer_free_var_types(region: &Region, registry: &StratumRegistry) -> BTreeMap<ValId, ValType> {
    fn rec(v: ValId, ty: ValType, b: &[ValId], out: &mut BTreeMap<ValId, ValType>) {
        if !b.contains(&v) {
            out.entry(v).or_insert(ty);
        }
    }
    fn walk(
        r: &Region,
        registry: &StratumRegistry,
        bound: &mut Vec<ValId>,
        out: &mut BTreeMap<ValId, ValType>,
    ) {
        match r {
            Region::Block(stmts) => {
                let saved = bound.len();
                for s in stmts {
                    match s {
                        Stmt::Let { dst, ty, op } => {
                            match op {
                                Op::Copy(v) => rec(*v, *ty, bound, out),
                                Op::Select { cond, true_val, false_val } => {
                                    rec(*cond, ValType::I32, bound, out);
                                    rec(*true_val, *ty, bound, out);
                                    rec(*false_val, *ty, bound, out);
                                }
                                Op::Un(u, v) => rec(*v, u.input_ty(), bound, out),
                                Op::Bin(bin, l, r) => {
                                    rec(*l, bin.operand_ty(), bound, out);
                                    rec(*r, bin.operand_ty(), bound, out);
                                }
                                Op::Load { addr, .. } => rec(*addr, ValType::I32, bound, out),
                                Op::MemoryGrow { delta, .. } => rec(*delta, ValType::I32, bound, out),
                                Op::ConstI32(_)
                                | Op::ConstI64(_)
                                | Op::GlobalGet(_)
                                | Op::MemorySize(_) => {}
                            }
                            bound.push(*dst);
                        }
                        Stmt::Effect(eff) => match eff {
                            EffectOp::Store { addr, width, val, .. } => {
                                rec(*addr, ValType::I32, bound, out);
                                if *width == MemWidth::B8 {
                                    rec(*val, ValType::I64, bound, out);
                                }
                            }
                            EffectOp::MemoryCopy { dst, src, len, .. }
                            | EffectOp::MemoryFill { dst, val: src, len, .. } => {
                                rec(*dst, ValType::I32, bound, out);
                                rec(*src, ValType::I32, bound, out);
                                rec(*len, ValType::I32, bound, out);
                            }
                            EffectOp::GlobalSet { .. } | EffectOp::Trap(_) | EffectOp::Nop => {}
                        },
                        Stmt::Region { results, region: sub } => {
                            walk(sub, registry, bound, out);
                            for &(id, _) in results {
                                bound.push(id);
                            }
                        }
                        Stmt::Call { results, target, args } => {
                            if let CallTarget::Stratum(sid) = target
                                && let Some(op) = registry.get_op(*sid)
                            {
                                for (&a, &(_, pt)) in args.iter().zip(&op.params) {
                                    rec(a, pt, bound, out);
                                }
                            }
                            for &(id, _) in results {
                                bound.push(id);
                            }
                        }
                        Stmt::Break { cond, .. } | Stmt::Continue { cond, .. } => {
                            if let Some(c) = cond {
                                rec(*c, ValType::I32, bound, out);
                            }
                        }
                        Stmt::Yield(_) | Stmt::Return(_) => {}
                    }
                }
                bound.truncate(saved);
            }
            Region::IfElse { cond, then_region, else_region, .. } => {
                rec(*cond, ValType::I32, bound, out);
                walk(then_region, registry, bound, out);
                walk(else_region, registry, bound, out);
            }
            Region::BoundedLoop { init_vars, state_vars, body, .. } => {
                for (&iv, &(_, st)) in init_vars.iter().zip(state_vars) {
                    rec(iv, st, bound, out);
                }
                let saved = bound.len();
                for &(sv, _) in state_vars {
                    bound.push(sv);
                }
                walk(body, registry, bound, out);
                bound.truncate(saved);
            }
            Region::InvariantLoop {
                init_vars,
                state_vars,
                cond,
                invariant_pred,
                fuel_measure,
                body,
            } => {
                for (&iv, &(_, st)) in init_vars.iter().zip(state_vars) {
                    rec(iv, st, bound, out);
                }
                let saved = bound.len();
                for &(sv, _) in state_vars {
                    bound.push(sv);
                }
                walk(cond, registry, bound, out);
                walk(invariant_pred, registry, bound, out);
                walk(fuel_measure, registry, bound, out);
                walk(body, registry, bound, out);
                bound.truncate(saved);
            }
        }
    }
    let mut out = BTreeMap::new();
    walk(region, registry, &mut Vec::new(), &mut out);
    out
}

fn remap_free_uses(region: &Region, map: &HashMap<ValId, ValId>) -> Region {
    fn walk(r: &Region, map: &HashMap<ValId, ValId>, shadowed: &mut Vec<ValId>) -> Region {
        let m = |v: ValId, sh: &[ValId]| -> ValId {
            if sh.contains(&v) { v } else { map.get(&v).copied().unwrap_or(v) }
        };
        match r {
            Region::Block(stmts) => {
                let saved = shadowed.len();
                let out = stmts
                    .iter()
                    .map(|s| match s {
                        Stmt::Let { dst, ty, op } => {
                            let new_op = match op {
                                Op::Copy(v) => Op::Copy(m(*v, shadowed)),
                                Op::Select { cond, true_val, false_val } => Op::Select {
                                    cond: m(*cond, shadowed),
                                    true_val: m(*true_val, shadowed),
                                    false_val: m(*false_val, shadowed),
                                },
                                Op::Un(u, v) => Op::Un(*u, m(*v, shadowed)),
                                Op::Bin(b, l, r) => Op::Bin(*b, m(*l, shadowed), m(*r, shadowed)),
                                Op::Load { mem, addr, offset, width, signed, result_ty } => Op::Load {
                                    mem: *mem,
                                    addr: m(*addr, shadowed),
                                    offset: *offset,
                                    width: *width,
                                    signed: *signed,
                                    result_ty: *result_ty,
                                },
                                Op::MemoryGrow { mem, delta } => {
                                    Op::MemoryGrow { mem: *mem, delta: m(*delta, shadowed) }
                                }
                                other => *other,
                            };
                            shadowed.push(*dst);
                            Stmt::Let { dst: *dst, ty: *ty, op: new_op }
                        }
                        Stmt::Effect(eff) => Stmt::Effect(match eff {
                            EffectOp::Store { mem, addr, offset, width, val } => EffectOp::Store {
                                mem: *mem,
                                addr: m(*addr, shadowed),
                                offset: *offset,
                                width: *width,
                                val: m(*val, shadowed),
                            },
                            EffectOp::MemoryCopy { dst_mem, src_mem, dst, src, len } => {
                                EffectOp::MemoryCopy {
                                    dst_mem: *dst_mem,
                                    src_mem: *src_mem,
                                    dst: m(*dst, shadowed),
                                    src: m(*src, shadowed),
                                    len: m(*len, shadowed),
                                }
                            }
                            EffectOp::MemoryFill { mem, dst, val, len } => EffectOp::MemoryFill {
                                mem: *mem,
                                dst: m(*dst, shadowed),
                                val: m(*val, shadowed),
                                len: m(*len, shadowed),
                            },
                            EffectOp::GlobalSet { id, val } => {
                                EffectOp::GlobalSet { id: *id, val: m(*val, shadowed) }
                            }
                            other => *other,
                        }),
                        Stmt::Region { results, region } => {
                            let new_reg = walk(region, map, shadowed);
                            for &(id, _) in results {
                                shadowed.push(id);
                            }
                            Stmt::Region { results: results.clone(), region: new_reg }
                        }
                        Stmt::Call { results, target, args } => {
                            let new_args = args.iter().copied().map(|a| m(a, shadowed)).collect();
                            for &(id, _) in results {
                                shadowed.push(id);
                            }
                            Stmt::Call { results: results.clone(), target: *target, args: new_args }
                        }
                        Stmt::Yield(vs) => Stmt::Yield(vs.iter().copied().map(|v| m(v, shadowed)).collect()),
                        Stmt::Return(vs) => Stmt::Return(vs.iter().copied().map(|v| m(v, shadowed)).collect()),
                        Stmt::Break { depth, cond, values } => Stmt::Break {
                            depth: *depth,
                            cond: cond.map(|c| m(c, shadowed)),
                            values: values.iter().copied().map(|v| m(v, shadowed)).collect(),
                        },
                        Stmt::Continue { depth, cond, values } => Stmt::Continue {
                            depth: *depth,
                            cond: cond.map(|c| m(c, shadowed)),
                            values: values.iter().copied().map(|v| m(v, shadowed)).collect(),
                        },
                    })
                    .collect();
                shadowed.truncate(saved);
                Region::Block(out)
            }
            Region::IfElse { cond, then_region, else_region, results } => Region::IfElse {
                cond: m(*cond, shadowed),
                then_region: Box::new(walk(then_region, map, shadowed)),
                else_region: Box::new(walk(else_region, map, shadowed)),
                results: results.clone(),
            },
            Region::BoundedLoop { max_iters, init_vars, state_vars, body } => {
                let init_vars = init_vars.iter().copied().map(|v| m(v, shadowed)).collect();
                let saved = shadowed.len();
                for &(sv, _) in state_vars {
                    shadowed.push(sv);
                }
                let body = Box::new(walk(body, map, shadowed));
                shadowed.truncate(saved);
                Region::BoundedLoop {
                    max_iters: *max_iters,
                    init_vars,
                    state_vars: state_vars.clone(),
                    body,
                }
            }
            Region::InvariantLoop {
                init_vars,
                state_vars,
                cond,
                invariant_pred,
                fuel_measure,
                body,
            } => {
                let init_vars = init_vars.iter().copied().map(|v| m(v, shadowed)).collect();
                let saved = shadowed.len();
                for &(sv, _) in state_vars {
                    shadowed.push(sv);
                }
                let res = Region::InvariantLoop {
                    init_vars,
                    state_vars: state_vars.clone(),
                    cond: Box::new(walk(cond, map, shadowed)),
                    invariant_pred: Box::new(walk(invariant_pred, map, shadowed)),
                    fuel_measure: Box::new(walk(fuel_measure, map, shadowed)),
                    body: Box::new(walk(body, map, shadowed)),
                };
                shadowed.truncate(saved);
                res
            }
        }
    }
    walk(region, map, &mut Vec::new())
}

fn build_egraph(registry: &StratumRegistry) -> Result<EGraph, SieveError> {
    let mut eg = EGraph::default();

    eg.parse_and_run_program(
        None,
        r#"
(datatype*
  (Expr
    (ConstI32 i64 :cost 1)
    (ConstI64 i64 :cost 1)
    (Var i64 i64 :cost 1)
    (GlobalGet i64 i64 :cost 4)
    (Select Expr Expr Expr :cost 3)
    (Un i64 Expr :cost 2)
    (Bin i64 Expr Expr :cost 3)
    (Load i64 Heap Expr i64 i64 i64 i64 :cost 15)
    (StratumCall i64 Heap i64 ExprList :cost 12)
    (MemSize i64 Heap :cost 4)
  )
  (ExprList
    (ENil :cost 1)
    (ECons Expr ExprList :cost 1)
  )
  (Heap
    (InitHeap :cost 1)
    (StoreHeap i64 Heap Expr i64 i64 Expr i64 :cost 2)
    (CallHeap i64 ExprList Heap :cost 2)
    (OpaqueHeap i64 :cost 1)
  )
)
"#,
    )
    .map_err(|e| SieveError::EqSatError(e.to_string()))?;

    // Register exact trap-preserving constant folding & bit-vector helpers.
    add_primitive!(&mut eg, "eval-bin-i32" = |op: i64, a: i64, b: i64| -?> i64 {
        prim_eval_bin_i32(op, a, b)
    });
    add_primitive!(&mut eg, "eval-bin-i64-val" = |op: i64, a: i64, b: i64| -?> i64 {
        prim_eval_bin_i64_val(op, a, b)
    });
    add_primitive!(&mut eg, "eval-bin-i64-cmp" = |op: i64, a: i64, b: i64| -?> i64 {
        prim_eval_bin_i64_cmp(op, a, b)
    });
    add_primitive!(&mut eg, "eval-un-i32" = |op: i64, a: i64| -?> i64 {
        prim_eval_un_i32(op, a)
    });
    add_primitive!(&mut eg, "eval-un-i64-val" = |op: i64, a: i64| -?> i64 {
        prim_eval_un_i64_val(op, a)
    });
    add_primitive!(&mut eg, "eval-un-i64-to-i32" = |op: i64, a: i64| -?> i64 {
        prim_eval_un_i64_to_i32(op, a)
    });
    add_primitive!(&mut eg, "eval-un-i32-to-i64" = |op: i64, a: i64| -?> i64 {
        prim_eval_un_i32_to_i64(op, a)
    });
    add_primitive!(&mut eg, "i32-add-wrap" = |a: i64, b: i64| -> i64 {
        ((a as i32).wrapping_add(b as i32)) as i64
    });
    add_primitive!(&mut eg, "i32-mul-wrap" = |a: i64, b: i64| -> i64 {
        ((a as i32).wrapping_mul(b as i32)) as i64
    });
    add_primitive!(&mut eg, "i64-add-wrap" = |a: i64, b: i64| -> i64 {
        a.wrapping_add(b)
    });
    add_primitive!(&mut eg, "i64-mul-wrap" = |a: i64, b: i64| -> i64 {
        a.wrapping_mul(b)
    });

    let rules = built_in_rules();
    eg.parse_and_run_program(None, &rules)
        .map_err(|e| SieveError::EqSatError(e.to_string()))?;

    // Register proved StratumRegistry laws.
    let mut reg_rules = String::new();
    for stratum in registry.promoted() {
        for law in &stratum.laws {
            match law.kind {
                LawKind::MemoryFrame { untouched_mem } => {
                    let rule_name = escape_str(&law.name);
                    reg_rules.push_str(&format!(
                        "(rewrite (Load {} (CallHeap {} ?args ?h) ?addr ?off ?w ?s ?ty) (Load {} ?h ?addr ?off ?w ?s ?ty) :name \"{rule_name}\")\n",
                        untouched_mem.0, stratum.op.id.0, untouched_mem.0
                    ));
                }
                LawKind::Algebraic => {
                    if law.precondition.is_some() {
                        continue;
                    }
                    if let (Some(lhs_pat), Some(rhs_pat)) = (
                        region_to_pattern(&law.lhs, &law.params, registry),
                        region_to_pattern(&law.rhs, &law.params, registry),
                    ) && !lhs_pat.starts_with('?')
                        && pattern_vars_covered(&lhs_pat, &rhs_pat)
                    {
                        let rule_name = escape_str(&law.name);
                        reg_rules.push_str(&format!(
                            "(rewrite {lhs_pat} {rhs_pat} :name \"{rule_name}\")\n"
                        ));
                    }
                }
            }
        }
    }
    if !reg_rules.is_empty() {
        eg.parse_and_run_program(None, &reg_rules)
            .map_err(|e| SieveError::EqSatError(e.to_string()))?;
    }

    Ok(eg)
}

fn escape_str(s: &str) -> String {
    s.replace('\\', "\\\\").replace('"', "\\\"")
}

fn built_in_rules() -> String {
    let i32_add = binop_tag(BinOp::I32Add);
    let i32_sub = binop_tag(BinOp::I32Sub);
    let i32_mul = binop_tag(BinOp::I32Mul);
    let i32_divs = binop_tag(BinOp::I32DivS);
    let i32_divu = binop_tag(BinOp::I32DivU);
    let i32_rems = binop_tag(BinOp::I32RemS);
    let i32_remu = binop_tag(BinOp::I32RemU);
    let i32_and = binop_tag(BinOp::I32And);
    let i32_or = binop_tag(BinOp::I32Or);
    let i32_xor = binop_tag(BinOp::I32Xor);
    let i32_shl = binop_tag(BinOp::I32Shl);
    let i32_shrs = binop_tag(BinOp::I32ShrS);
    let i32_shru = binop_tag(BinOp::I32ShrU);
    let i32_rotl = binop_tag(BinOp::I32Rotl);
    let i32_rotr = binop_tag(BinOp::I32Rotr);
    let i32_eq = binop_tag(BinOp::I32Eq);
    let i32_ne = binop_tag(BinOp::I32Ne);
    let i32_lts = binop_tag(BinOp::I32LtS);
    let i32_ltu = binop_tag(BinOp::I32LtU);
    let i32_gts = binop_tag(BinOp::I32GtS);
    let i32_gtu = binop_tag(BinOp::I32GtU);
    let i32_les = binop_tag(BinOp::I32LeS);
    let i32_leu = binop_tag(BinOp::I32LeU);
    let i32_ges = binop_tag(BinOp::I32GeS);
    let i32_geu = binop_tag(BinOp::I32GeU);

    let i64_add = binop_tag(BinOp::I64Add);
    let i64_sub = binop_tag(BinOp::I64Sub);
    let i64_mul = binop_tag(BinOp::I64Mul);
    let i64_divs = binop_tag(BinOp::I64DivS);
    let i64_divu = binop_tag(BinOp::I64DivU);
    let i64_rems = binop_tag(BinOp::I64RemS);
    let i64_remu = binop_tag(BinOp::I64RemU);
    let i64_and = binop_tag(BinOp::I64And);
    let i64_or = binop_tag(BinOp::I64Or);
    let i64_xor = binop_tag(BinOp::I64Xor);
    let i64_shl = binop_tag(BinOp::I64Shl);
    let i64_shrs = binop_tag(BinOp::I64ShrS);
    let i64_shru = binop_tag(BinOp::I64ShrU);
    let i64_rotl = binop_tag(BinOp::I64Rotl);
    let i64_rotr = binop_tag(BinOp::I64Rotr);
    let i64_eq = binop_tag(BinOp::I64Eq);
    let i64_ne = binop_tag(BinOp::I64Ne);
    let i64_lts = binop_tag(BinOp::I64LtS);
    let i64_ltu = binop_tag(BinOp::I64LtU);
    let i64_gts = binop_tag(BinOp::I64GtS);
    let i64_gtu = binop_tag(BinOp::I64GtU);
    let i64_les = binop_tag(BinOp::I64LeS);
    let i64_leu = binop_tag(BinOp::I64LeU);
    let i64_ges = binop_tag(BinOp::I64GeS);
    let i64_geu = binop_tag(BinOp::I64GeU);

    let u_i32_eqz = unop_tag(UnOp::I32Eqz);
    let u_wrap = unop_tag(UnOp::I32WrapI64);
    let u_ext_s = unop_tag(UnOp::I64ExtendI32S);
    let u_ext_u = unop_tag(UnOp::I64ExtendI32U);
    let u_32_8s = unop_tag(UnOp::I32Extend8S);
    let u_32_16s = unop_tag(UnOp::I32Extend16S);
    let u_64_8s = unop_tag(UnOp::I64Extend8S);
    let u_64_16s = unop_tag(UnOp::I64Extend16S);
    let u_64_32s = unop_tag(UnOp::I64Extend32S);

    format!(
        r#"
; Constant folding (fallible primitives refuse div/rem traps)
(rule ((= ?e (Bin ?op (ConstI32 ?a) (ConstI32 ?b))) (= ?res (eval-bin-i32 ?op ?a ?b)))
      ((union ?e (ConstI32 ?res))) :name "const-fold-bin-i32")
(rule ((= ?e (Bin ?op (ConstI64 ?a) (ConstI64 ?b))) (= ?res (eval-bin-i64-val ?op ?a ?b)))
      ((union ?e (ConstI64 ?res))) :name "const-fold-bin-i64")
(rule ((= ?e (Bin ?op (ConstI64 ?a) (ConstI64 ?b))) (= ?res (eval-bin-i64-cmp ?op ?a ?b)))
      ((union ?e (ConstI32 ?res))) :name "const-fold-cmp-i64")
(rule ((= ?e (Un ?op (ConstI32 ?a))) (= ?res (eval-un-i32 ?op ?a)))
      ((union ?e (ConstI32 ?res))) :name "const-fold-un-i32")
(rule ((= ?e (Un ?op (ConstI64 ?a))) (= ?res (eval-un-i64-val ?op ?a)))
      ((union ?e (ConstI64 ?res))) :name "const-fold-un-i64")
(rule ((= ?e (Un ?op (ConstI64 ?a))) (= ?res (eval-un-i64-to-i32 ?op ?a)))
      ((union ?e (ConstI32 ?res))) :name "const-fold-un-i64-to-i32")
(rule ((= ?e (Un ?op (ConstI32 ?a))) (= ?res (eval-un-i32-to-i64 ?op ?a)))
      ((union ?e (ConstI64 ?res))) :name "const-fold-un-i32-to-i64")

; Select simplifications
(rewrite (Select ?c ?x ?x) ?x :name "select-same")
(rewrite (Select (ConstI32 0) ?t ?f) ?f :name "select-const-zero")
(rewrite (Select (ConstI32 ?c) ?t ?f) ?t :when ((!= ?c 0)) :name "select-const-nonzero")
(rewrite (Select (Un {u_i32_eqz} ?c) ?t ?f) (Select ?c ?f ?t) :name "select-eqz-flip")

; I32 algebraic & BV identities
(rewrite (Bin {i32_add} ?x (ConstI32 0)) ?x :name "add-zero-r-i32")
(rewrite (Bin {i32_add} (ConstI32 0) ?x) ?x :name "add-zero-l-i32")
(rewrite (Bin {i32_sub} ?x (ConstI32 0)) ?x :name "sub-zero-i32")
(rewrite (Bin {i32_sub} ?x ?x) (ConstI32 0) :name "sub-self-i32")
(rewrite (Bin {i32_mul} ?x (ConstI32 0)) (ConstI32 0) :name "mul-zero-r-i32")
(rewrite (Bin {i32_mul} (ConstI32 0) ?x) (ConstI32 0) :name "mul-zero-l-i32")
(rewrite (Bin {i32_mul} ?x (ConstI32 1)) ?x :name "mul-one-r-i32")
(rewrite (Bin {i32_mul} (ConstI32 1) ?x) ?x :name "mul-one-l-i32")
(rewrite (Bin {i32_and} ?x (ConstI32 0)) (ConstI32 0) :name "and-zero-r-i32")
(rewrite (Bin {i32_and} (ConstI32 0) ?x) (ConstI32 0) :name "and-zero-l-i32")
(rewrite (Bin {i32_and} ?x (ConstI32 -1)) ?x :name "and-allones-r-i32")
(rewrite (Bin {i32_and} (ConstI32 -1) ?x) ?x :name "and-allones-l-i32")
(rewrite (Bin {i32_and} ?x ?x) ?x :name "and-self-i32")
(rewrite (Bin {i32_or} ?x (ConstI32 0)) ?x :name "or-zero-r-i32")
(rewrite (Bin {i32_or} (ConstI32 0) ?x) ?x :name "or-zero-l-i32")
(rewrite (Bin {i32_or} ?x (ConstI32 -1)) (ConstI32 -1) :name "or-allones-r-i32")
(rewrite (Bin {i32_or} (ConstI32 -1) ?x) (ConstI32 -1) :name "or-allones-l-i32")
(rewrite (Bin {i32_or} ?x ?x) ?x :name "or-self-i32")
(rewrite (Bin {i32_xor} ?x (ConstI32 0)) ?x :name "xor-zero-r-i32")
(rewrite (Bin {i32_xor} (ConstI32 0) ?x) ?x :name "xor-zero-l-i32")
(rewrite (Bin {i32_xor} ?x ?x) (ConstI32 0) :name "xor-self-i32")
(rewrite (Bin {i32_xor} (Bin {i32_xor} ?x ?y) ?y) ?x :name "xor-cancel-r-i32")
(rewrite (Bin {i32_shl} ?x (ConstI32 0)) ?x :name "shl-zero-i32")
(rewrite (Bin {i32_shrs} ?x (ConstI32 0)) ?x :name "shrs-zero-i32")
(rewrite (Bin {i32_shru} ?x (ConstI32 0)) ?x :name "shru-zero-i32")
(rewrite (Bin {i32_rotl} ?x (ConstI32 0)) ?x :name "rotl-zero-i32")
(rewrite (Bin {i32_rotr} ?x (ConstI32 0)) ?x :name "rotr-zero-i32")
(rewrite (Bin {i32_shl} (ConstI32 0) ?y) (ConstI32 0) :name "zero-shl-i32")
(rewrite (Bin {i32_shrs} (ConstI32 0) ?y) (ConstI32 0) :name "zero-shrs-i32")
(rewrite (Bin {i32_shru} (ConstI32 0) ?y) (ConstI32 0) :name "zero-shru-i32")

; Constant reassociation & commutativity (I32)
(rewrite (Bin {i32_add} (Bin {i32_add} ?x (ConstI32 ?a)) (ConstI32 ?b))
         (Bin {i32_add} ?x (ConstI32 (i32-add-wrap ?a ?b))) :name "reassoc-add-const-i32")
(rewrite (Bin {i32_mul} (Bin {i32_mul} ?x (ConstI32 ?a)) (ConstI32 ?b))
         (Bin {i32_mul} ?x (ConstI32 (i32-mul-wrap ?a ?b))) :name "reassoc-mul-const-i32")
(rewrite (Bin {i32_and} (Bin {i32_and} ?x (ConstI32 ?a)) (ConstI32 ?b))
         (Bin {i32_and} ?x (ConstI32 (& ?a ?b))) :name "reassoc-and-const-i32")
(rewrite (Bin {i32_or} (Bin {i32_or} ?x (ConstI32 ?a)) (ConstI32 ?b))
         (Bin {i32_or} ?x (ConstI32 (| ?a ?b))) :name "reassoc-or-const-i32")
(rewrite (Bin {i32_xor} (Bin {i32_xor} ?x (ConstI32 ?a)) (ConstI32 ?b))
         (Bin {i32_xor} ?x (ConstI32 (^ ?a ?b))) :name "reassoc-xor-const-i32")
(rewrite (Bin {i32_add} ?a ?b) (Bin {i32_add} ?b ?a) :name "comm-add-i32")
(rewrite (Bin {i32_mul} ?a ?b) (Bin {i32_mul} ?b ?a) :name "comm-mul-i32")
(rewrite (Bin {i32_and} ?a ?b) (Bin {i32_and} ?b ?a) :name "comm-and-i32")
(rewrite (Bin {i32_or} ?a ?b) (Bin {i32_or} ?b ?a) :name "comm-or-i32")
(rewrite (Bin {i32_xor} ?a ?b) (Bin {i32_xor} ?b ?a) :name "comm-xor-i32")

; Safe Div/Rem identities ONLY where trap is statically impossible
(rewrite (Bin {i32_divs} ?x (ConstI32 1)) ?x :name "divs-one-i32")
(rewrite (Bin {i32_divu} ?x (ConstI32 1)) ?x :name "divu-one-i32")
(rewrite (Bin {i32_rems} ?x (ConstI32 1)) (ConstI32 0) :name "rems-one-i32")
(rewrite (Bin {i32_rems} ?x (ConstI32 -1)) (ConstI32 0) :name "rems-neg1-i32")
(rewrite (Bin {i32_remu} ?x (ConstI32 1)) (ConstI32 0) :name "remu-one-i32")

; I32 comparison identities
(rewrite (Bin {i32_eq} ?x ?x) (ConstI32 1) :name "eq-self-i32")
(rewrite (Bin {i32_ne} ?x ?x) (ConstI32 0) :name "ne-self-i32")
(rewrite (Bin {i32_lts} ?x ?x) (ConstI32 0) :name "lts-self-i32")
(rewrite (Bin {i32_ltu} ?x ?x) (ConstI32 0) :name "ltu-self-i32")
(rewrite (Bin {i32_gts} ?x ?x) (ConstI32 0) :name "gts-self-i32")
(rewrite (Bin {i32_gtu} ?x ?x) (ConstI32 0) :name "gtu-self-i32")
(rewrite (Bin {i32_les} ?x ?x) (ConstI32 1) :name "les-self-i32")
(rewrite (Bin {i32_leu} ?x ?x) (ConstI32 1) :name "leu-self-i32")
(rewrite (Bin {i32_ges} ?x ?x) (ConstI32 1) :name "ges-self-i32")
(rewrite (Bin {i32_geu} ?x ?x) (ConstI32 1) :name "geu-self-i32")
(rewrite (Bin {i32_eq} ?x (ConstI32 0)) (Un {u_i32_eqz} ?x) :name "eq-zero-eqz-i32")
(rewrite (Un {u_i32_eqz} (Un {u_i32_eqz} (Un {u_i32_eqz} ?x))) (Un {u_i32_eqz} ?x) :name "triple-eqz-i32")

; I64 algebraic & BV identities
(rewrite (Bin {i64_add} ?x (ConstI64 0)) ?x :name "add-zero-r-i64")
(rewrite (Bin {i64_add} (ConstI64 0) ?x) ?x :name "add-zero-l-i64")
(rewrite (Bin {i64_sub} ?x (ConstI64 0)) ?x :name "sub-zero-i64")
(rewrite (Bin {i64_sub} ?x ?x) (ConstI64 0) :name "sub-self-i64")
(rewrite (Bin {i64_mul} ?x (ConstI64 0)) (ConstI64 0) :name "mul-zero-r-i64")
(rewrite (Bin {i64_mul} (ConstI64 0) ?x) (ConstI64 0) :name "mul-zero-l-i64")
(rewrite (Bin {i64_mul} ?x (ConstI64 1)) ?x :name "mul-one-r-i64")
(rewrite (Bin {i64_mul} (ConstI64 1) ?x) ?x :name "mul-one-l-i64")
(rewrite (Bin {i64_and} ?x (ConstI64 0)) (ConstI64 0) :name "and-zero-r-i64")
(rewrite (Bin {i64_and} (ConstI64 0) ?x) (ConstI64 0) :name "and-zero-l-i64")
(rewrite (Bin {i64_and} ?x (ConstI64 -1)) ?x :name "and-allones-r-i64")
(rewrite (Bin {i64_and} (ConstI64 -1) ?x) ?x :name "and-allones-l-i64")
(rewrite (Bin {i64_and} ?x ?x) ?x :name "and-self-i64")
(rewrite (Bin {i64_or} ?x (ConstI64 0)) ?x :name "or-zero-r-i64")
(rewrite (Bin {i64_or} (ConstI64 0) ?x) ?x :name "or-zero-l-i64")
(rewrite (Bin {i64_or} ?x (ConstI64 -1)) (ConstI64 -1) :name "or-allones-r-i64")
(rewrite (Bin {i64_or} (ConstI64 -1) ?x) (ConstI64 -1) :name "or-allones-l-i64")
(rewrite (Bin {i64_or} ?x ?x) ?x :name "or-self-i64")
(rewrite (Bin {i64_xor} ?x (ConstI64 0)) ?x :name "xor-zero-r-i64")
(rewrite (Bin {i64_xor} (ConstI64 0) ?x) ?x :name "xor-zero-l-i64")
(rewrite (Bin {i64_xor} ?x ?x) (ConstI64 0) :name "xor-self-i64")
(rewrite (Bin {i64_xor} (Bin {i64_xor} ?x ?y) ?y) ?x :name "xor-cancel-r-i64")
(rewrite (Bin {i64_shl} ?x (ConstI64 0)) ?x :name "shl-zero-i64")
(rewrite (Bin {i64_shrs} ?x (ConstI64 0)) ?x :name "shrs-zero-i64")
(rewrite (Bin {i64_shru} ?x (ConstI64 0)) ?x :name "shru-zero-i64")
(rewrite (Bin {i64_rotl} ?x (ConstI64 0)) ?x :name "rotl-zero-i64")
(rewrite (Bin {i64_rotr} ?x (ConstI64 0)) ?x :name "rotr-zero-i64")
(rewrite (Bin {i64_shl} (ConstI64 0) ?y) (ConstI64 0) :name "zero-shl-i64")
(rewrite (Bin {i64_shrs} (ConstI64 0) ?y) (ConstI64 0) :name "zero-shrs-i64")
(rewrite (Bin {i64_shru} (ConstI64 0) ?y) (ConstI64 0) :name "zero-shru-i64")

; Constant reassociation & commutativity (I64)
(rewrite (Bin {i64_add} (Bin {i64_add} ?x (ConstI64 ?a)) (ConstI64 ?b))
         (Bin {i64_add} ?x (ConstI64 (i64-add-wrap ?a ?b))) :name "reassoc-add-const-i64")
(rewrite (Bin {i64_mul} (Bin {i64_mul} ?x (ConstI64 ?a)) (ConstI64 ?b))
         (Bin {i64_mul} ?x (ConstI64 (i64-mul-wrap ?a ?b))) :name "reassoc-mul-const-i64")
(rewrite (Bin {i64_and} (Bin {i64_and} ?x (ConstI64 ?a)) (ConstI64 ?b))
         (Bin {i64_and} ?x (ConstI64 (& ?a ?b))) :name "reassoc-and-const-i64")
(rewrite (Bin {i64_or} (Bin {i64_or} ?x (ConstI64 ?a)) (ConstI64 ?b))
         (Bin {i64_or} ?x (ConstI64 (| ?a ?b))) :name "reassoc-or-const-i64")
(rewrite (Bin {i64_xor} (Bin {i64_xor} ?x (ConstI64 ?a)) (ConstI64 ?b))
         (Bin {i64_xor} ?x (ConstI64 (^ ?a ?b))) :name "reassoc-xor-const-i64")
(rewrite (Bin {i64_add} ?a ?b) (Bin {i64_add} ?b ?a) :name "comm-add-i64")
(rewrite (Bin {i64_mul} ?a ?b) (Bin {i64_mul} ?b ?a) :name "comm-mul-i64")
(rewrite (Bin {i64_and} ?a ?b) (Bin {i64_and} ?b ?a) :name "comm-and-i64")
(rewrite (Bin {i64_or} ?a ?b) (Bin {i64_or} ?b ?a) :name "comm-or-i64")
(rewrite (Bin {i64_xor} ?a ?b) (Bin {i64_xor} ?b ?a) :name "comm-xor-i64")

; Safe Div/Rem identities (I64)
(rewrite (Bin {i64_divs} ?x (ConstI64 1)) ?x :name "divs-one-i64")
(rewrite (Bin {i64_divu} ?x (ConstI64 1)) ?x :name "divu-one-i64")
(rewrite (Bin {i64_rems} ?x (ConstI64 1)) (ConstI64 0) :name "rems-one-i64")
(rewrite (Bin {i64_rems} ?x (ConstI64 -1)) (ConstI64 0) :name "rems-neg1-i64")
(rewrite (Bin {i64_remu} ?x (ConstI64 1)) (ConstI64 0) :name "remu-one-i64")

; I64 comparison identities
(rewrite (Bin {i64_eq} ?x ?x) (ConstI32 1) :name "eq-self-i64")
(rewrite (Bin {i64_ne} ?x ?x) (ConstI32 0) :name "ne-self-i64")
(rewrite (Bin {i64_lts} ?x ?x) (ConstI32 0) :name "lts-self-i64")
(rewrite (Bin {i64_ltu} ?x ?x) (ConstI32 0) :name "ltu-self-i64")
(rewrite (Bin {i64_gts} ?x ?x) (ConstI32 0) :name "gts-self-i64")
(rewrite (Bin {i64_gtu} ?x ?x) (ConstI32 0) :name "gtu-self-i64")
(rewrite (Bin {i64_les} ?x ?x) (ConstI32 1) :name "les-self-i64")
(rewrite (Bin {i64_leu} ?x ?x) (ConstI32 1) :name "leu-self-i64")
(rewrite (Bin {i64_ges} ?x ?x) (ConstI32 1) :name "ges-self-i64")
(rewrite (Bin {i64_geu} ?x ?x) (ConstI32 1) :name "geu-self-i64")

; Extend / Wrap identities
(rewrite (Un {u_wrap} (Un {u_ext_s} ?x)) ?x :name "wrap-extend-s")
(rewrite (Un {u_wrap} (Un {u_ext_u} ?x)) ?x :name "wrap-extend-u")
(rewrite (Un {u_32_8s} (Un {u_32_8s} ?x)) (Un {u_32_8s} ?x) :name "extend8s-idemp-i32")
(rewrite (Un {u_32_16s} (Un {u_32_16s} ?x)) (Un {u_32_16s} ?x) :name "extend16s-idemp-i32")
(rewrite (Un {u_32_16s} (Un {u_32_8s} ?x)) (Un {u_32_8s} ?x) :name "extend16s-8s-i32")
(rewrite (Un {u_64_8s} (Un {u_64_8s} ?x)) (Un {u_64_8s} ?x) :name "extend8s-idemp-i64")
(rewrite (Un {u_64_16s} (Un {u_64_16s} ?x)) (Un {u_64_16s} ?x) :name "extend16s-idemp-i64")
(rewrite (Un {u_64_32s} (Un {u_64_32s} ?x)) (Un {u_64_32s} ?x) :name "extend32s-idemp-i64")

; Disjoint memory-frame & store-to-load forwarding rules
(rewrite (Load ?m1 (StoreHeap ?m2 ?h ?addr ?off ?w ?val ?vty) ?laddr ?loff ?lw ?ls ?lty)
         (Load ?m1 ?h ?laddr ?loff ?lw ?ls ?lty)
         :when ((!= ?m1 ?m2))
         :name "disjoint-mem-load-store")
(rewrite (Load ?m (StoreHeap ?m ?h ?addr ?off 4 ?val 0) ?addr ?off 4 ?ls 0)
         ?val
         :name "store-load-forward-b4")
(rewrite (Load ?m (StoreHeap ?m ?h ?addr ?off 8 ?val 1) ?addr ?off 8 ?ls 1)
         ?val
         :name "store-load-forward-b8")
"#
    )
}

fn region_to_pattern(
    region: &Region,
    params: &[(ValId, ValType)],
    registry: &StratumRegistry,
) -> Option<String> {
    let Region::Block(stmts) = region else {
        return None;
    };
    let mut env: HashMap<ValId, (String, ValType)> = params
        .iter()
        .map(|&(id, ty)| (id, (format!("?p{}", id.0), ty)))
        .collect();
    let mut heap = "?h_law".to_string();
    let mut h_idx = 0usize;
    for stmt in stmts {
        match stmt {
            Stmt::Let { dst, ty, op } => {
                let expr = match op {
                    Op::ConstI32(v) => format!("(ConstI32 {})", *v as i64),
                    Op::ConstI64(v) => format!("(ConstI64 {v})"),
                    Op::Copy(v) => env.get(v)?.0.clone(),
                    Op::Select { cond, true_val, false_val } => format!(
                        "(Select {} {} {})",
                        env.get(cond)?.0,
                        env.get(true_val)?.0,
                        env.get(false_val)?.0
                    ),
                    Op::Un(u, a) => format!("(Un {} {})", unop_tag(*u), env.get(a)?.0),
                    Op::Bin(b, l, r) => format!(
                        "(Bin {} {} {})",
                        binop_tag(*b),
                        env.get(l)?.0,
                        env.get(r)?.0
                    ),
                    Op::Load { mem, addr, offset, width, signed, result_ty } => format!(
                        "(Load {} {heap} {} {} {} {} {})",
                        mem.0,
                        env.get(addr)?.0,
                        offset,
                        width_bytes(*width),
                        i64::from(*signed),
                        ty_tag(*result_ty)
                    ),
                    Op::GlobalGet(_) | Op::MemorySize(_) | Op::MemoryGrow { .. } => return None,
                };
                env.insert(*dst, (expr, *ty));
            }
            Stmt::Effect(EffectOp::Store { mem, addr, offset, width, val }) => {
                h_idx += 1;
                let _ = h_idx;
                let (val_s, val_ty) = env.get(val)?;
                heap = format!(
                    "(StoreHeap {} {heap} {} {} {} {} {})",
                    mem.0,
                    env.get(addr)?.0,
                    offset,
                    width_bytes(*width),
                    val_s,
                    ty_tag(*val_ty)
                );
            }
            Stmt::Effect(EffectOp::Nop) => {}
            Stmt::Call { results, target: CallTarget::Stratum(sid), args } if results.len() == 1 => {
                let arg_strs: Option<Vec<String>> =
                    args.iter().map(|a| env.get(a).map(|(s, _)| s.clone())).collect();
                let list = encode_expr_list(&arg_strs?);
                let reads_state = registry
                    .get_op(*sid)
                    .is_none_or(|op| region_reads_heap_or_global(&op.body, registry));
                let call_pat = if reads_state {
                    format!("(StratumCall {} {heap} ?ge_law {list})", sid.0)
                } else {
                    format!("(StratumCall {} (InitHeap) 0 {list})", sid.0)
                };
                let is_ro = registry
                    .get_op(*sid)
                    .is_some_and(|op| validate_read_only_with_registry(&op.body, registry));
                if !is_ro {
                    heap = format!("(CallHeap {} {list} {heap})", sid.0);
                }
                env.insert(results[0].0, (call_pat, results[0].1));
            }
            Stmt::Yield(vs) if vs.len() == 1 => return env.get(&vs[0]).map(|(s, _)| s.clone()),
            _ => return None,
        }
    }
    None
}

fn collect_pattern_vars(pat: &str) -> BTreeSet<String> {
    let mut vars = BTreeSet::new();
    for tok in pat.split(|c: char| c.is_whitespace() || c == '(' || c == ')') {
        if tok.starts_with('?') && tok.len() > 1 {
            vars.insert(tok.to_string());
        }
    }
    vars
}

fn pattern_vars_covered(lhs: &str, rhs: &str) -> bool {
    let lvars = collect_pattern_vars(lhs);
    let rvars = collect_pattern_vars(rhs);
    rvars.is_subset(&lvars)
}

pub fn count_region_nodes(region: &Region) -> usize {
    match region {
        Region::Block(stmts) => {
            1 + stmts
                .iter()
                .map(|s| match s {
                    Stmt::Let { .. } => 2,
                    Stmt::Effect(EffectOp::Nop) => 0,
                    Stmt::Effect(_) => 2,
                    Stmt::Region { region, .. } => 1 + count_region_nodes(region),
                    Stmt::Call { args, .. } => 1 + args.len(),
                    Stmt::Yield(vs) | Stmt::Return(vs) => 1 + vs.len(),
                    Stmt::Break { values, .. } | Stmt::Continue { values, .. } => 1 + values.len(),
                })
                .sum::<usize>()
        }
        Region::IfElse { then_region, else_region, .. } => {
            1 + count_region_nodes(then_region) + count_region_nodes(else_region)
        }
        Region::BoundedLoop { body, .. } => 1 + count_region_nodes(body),
        Region::InvariantLoop { cond, invariant_pred, fuel_measure, body, .. } => {
            1 + count_region_nodes(cond)
                + count_region_nodes(invariant_pred)
                + count_region_nodes(fuel_measure)
                + count_region_nodes(body)
        }
    }
}

fn max_val_id_in_region(region: &Region) -> u32 {
    let mut max = 0u32;
    let bump = |v: ValId, m: &mut u32| *m = (*m).max(v.0 + 1);
    match region {
        Region::Block(stmts) => {
            for s in stmts {
                match s {
                    Stmt::Let { dst, op, .. } => {
                        bump(*dst, &mut max);
                        match op {
                            Op::Copy(v) | Op::Un(_, v) | Op::Load { addr: v, .. } | Op::MemoryGrow { delta: v, .. } => bump(*v, &mut max),
                            Op::Select { cond, true_val, false_val } => {
                                bump(*cond, &mut max);
                                bump(*true_val, &mut max);
                                bump(*false_val, &mut max);
                            }
                            Op::Bin(_, l, r) => {
                                bump(*l, &mut max);
                                bump(*r, &mut max);
                            }
                            _ => {}
                        }
                    }
                    Stmt::Region { results, region } => {
                        results.iter().for_each(|&(id, _)| bump(id, &mut max));
                        max = max.max(max_val_id_in_region(region));
                    }
                    Stmt::Call { results, args, .. } => {
                        results.iter().for_each(|&(id, _)| bump(id, &mut max));
                        args.iter().for_each(|&a| bump(a, &mut max));
                    }
                    Stmt::Yield(vs) | Stmt::Return(vs) => vs.iter().for_each(|&v| bump(v, &mut max)),
                    Stmt::Break { cond, values, .. } | Stmt::Continue { cond, values, .. } => {
                        cond.iter().chain(values).for_each(|&v| bump(v, &mut max));
                    }
                    Stmt::Effect(eff) => match eff {
                        EffectOp::Store { addr, val, .. } => {
                            bump(*addr, &mut max);
                            bump(*val, &mut max);
                        }
                        EffectOp::MemoryCopy { dst, src, len, .. }
                        | EffectOp::MemoryFill { dst, val: src, len, .. } => {
                            bump(*dst, &mut max);
                            bump(*src, &mut max);
                            bump(*len, &mut max);
                        }
                        EffectOp::GlobalSet { val, .. } => bump(*val, &mut max),
                        EffectOp::Trap(_) | EffectOp::Nop => {}
                    },
                }
            }
        }
        Region::IfElse { cond, then_region, else_region, .. } => {
            bump(*cond, &mut max);
            max = max
                .max(max_val_id_in_region(then_region))
                .max(max_val_id_in_region(else_region));
        }
        Region::BoundedLoop { init_vars, state_vars, body, .. } => {
            init_vars
                .iter()
                .chain(state_vars.iter().map(|(v, _)| v))
                .for_each(|&v| bump(v, &mut max));
            max = max.max(max_val_id_in_region(body));
        }
        Region::InvariantLoop {
            init_vars,
            state_vars,
            cond,
            invariant_pred,
            fuel_measure,
            body,
        } => {
            init_vars
                .iter()
                .chain(state_vars.iter().map(|(v, _)| v))
                .for_each(|&v| bump(v, &mut max));
            [cond, invariant_pred, fuel_measure, body]
                .into_iter()
                .for_each(|r| max = max.max(max_val_id_in_region(r)));
        }
    }
    max
}

fn unop_tag(u: UnOp) -> i64 {
    match u {
        UnOp::I32Eqz => 0,
        UnOp::I64Eqz => 1,
        UnOp::I32Clz => 2,
        UnOp::I32Ctz => 3,
        UnOp::I32Popcnt => 4,
        UnOp::I64Clz => 5,
        UnOp::I64Ctz => 6,
        UnOp::I64Popcnt => 7,
        UnOp::I32WrapI64 => 8,
        UnOp::I64ExtendI32S => 9,
        UnOp::I64ExtendI32U => 10,
        UnOp::I32Extend8S => 11,
        UnOp::I32Extend16S => 12,
        UnOp::I64Extend8S => 13,
        UnOp::I64Extend16S => 14,
        UnOp::I64Extend32S => 15,
    }
}

fn unop_from_tag(t: i64) -> Option<UnOp> {
    Some(match t {
        0 => UnOp::I32Eqz,
        1 => UnOp::I64Eqz,
        2 => UnOp::I32Clz,
        3 => UnOp::I32Ctz,
        4 => UnOp::I32Popcnt,
        5 => UnOp::I64Clz,
        6 => UnOp::I64Ctz,
        7 => UnOp::I64Popcnt,
        8 => UnOp::I32WrapI64,
        9 => UnOp::I64ExtendI32S,
        10 => UnOp::I64ExtendI32U,
        11 => UnOp::I32Extend8S,
        12 => UnOp::I32Extend16S,
        13 => UnOp::I64Extend8S,
        14 => UnOp::I64Extend16S,
        15 => UnOp::I64Extend32S,
        _ => return None,
    })
}

fn binop_tag(b: BinOp) -> i64 {
    b as u8 as i64
}

fn binop_from_tag(t: i64) -> Option<BinOp> {
    use BinOp::*;
    const ALL: [BinOp; 50] = [
        I32Eq, I32Ne, I32LtS, I32LtU, I32GtS, I32GtU, I32LeS, I32LeU, I32GeS, I32GeU,
        I64Eq, I64Ne, I64LtS, I64LtU, I64GtS, I64GtU, I64LeS, I64LeU, I64GeS, I64GeU,
        I32Add, I32Sub, I32Mul, I32DivS, I32DivU, I32RemS, I32RemU,
        I64Add, I64Sub, I64Mul, I64DivS, I64DivU, I64RemS, I64RemU,
        I32And, I32Or, I32Xor, I32Shl, I32ShrS, I32ShrU, I32Rotl, I32Rotr,
        I64And, I64Or, I64Xor, I64Shl, I64ShrS, I64ShrU, I64Rotl, I64Rotr,
    ];
    usize::try_from(t).ok().and_then(|idx| ALL.get(idx).copied())
}

fn prim_eval_bin_i32(op: i64, a: i64, b: i64) -> Option<i64> {
    let b_op = binop_from_tag(op)?;
    if b_op.operand_ty() != ValType::I32 {
        return None;
    }
    eval_const_binop_i32(b_op, a as i32, b as i32).map(|v| v as i64)
}

fn prim_eval_bin_i64_val(op: i64, a: i64, b: i64) -> Option<i64> {
    let b_op = binop_from_tag(op)?;
    if b_op.operand_ty() != ValType::I64 || b_op.output_ty() != ValType::I64 {
        return None;
    }
    eval_const_binop_i64_val(b_op, a, b)
}

fn prim_eval_bin_i64_cmp(op: i64, a: i64, b: i64) -> Option<i64> {
    let b_op = binop_from_tag(op)?;
    if b_op.operand_ty() != ValType::I64 || b_op.output_ty() != ValType::I32 {
        return None;
    }
    eval_const_binop_i64_cmp(b_op, a, b).map(|v| v as i64)
}

fn prim_eval_un_i32(op: i64, a: i64) -> Option<i64> {
    let u = unop_from_tag(op)?;
    if u.input_ty() != ValType::I32 || u.output_ty() != ValType::I32 {
        return None;
    }
    Some(eval_const_un_i32(u, a as i32) as i64)
}

fn prim_eval_un_i64_val(op: i64, a: i64) -> Option<i64> {
    let u = unop_from_tag(op)?;
    if u.input_ty() != ValType::I64 || u.output_ty() != ValType::I64 {
        return None;
    }
    Some(eval_const_un_i64_val(u, a))
}

fn prim_eval_un_i64_to_i32(op: i64, a: i64) -> Option<i64> {
    let u = unop_from_tag(op)?;
    if u.input_ty() != ValType::I64 || u.output_ty() != ValType::I32 {
        return None;
    }
    Some(match u {
        UnOp::I64Eqz => i64::from(a == 0),
        UnOp::I32WrapI64 => (a as i32) as i64,
        _ => return None,
    })
}

fn prim_eval_un_i32_to_i64(op: i64, a: i64) -> Option<i64> {
    let u = unop_from_tag(op)?;
    match u {
        UnOp::I64ExtendI32S => Some((a as i32) as i64),
        UnOp::I64ExtendI32U => Some(((a as i32) as u32) as i64),
        _ => None,
    }
}

fn eval_const_un_i32(u: UnOp, a: i32) -> i32 {
    match u {
        UnOp::I32Eqz => i32::from(a == 0),
        UnOp::I32Clz => a.leading_zeros() as i32,
        UnOp::I32Ctz => a.trailing_zeros() as i32,
        UnOp::I32Popcnt => a.count_ones() as i32,
        UnOp::I32Extend8S => (a as i8) as i32,
        UnOp::I32Extend16S => (a as i16) as i32,
        _ => unreachable!(),
    }
}

fn eval_const_un_i64_val(u: UnOp, a: i64) -> i64 {
    match u {
        UnOp::I64Clz => a.leading_zeros() as i64,
        UnOp::I64Ctz => a.trailing_zeros() as i64,
        UnOp::I64Popcnt => a.count_ones() as i64,
        UnOp::I64Extend8S => (a as i8) as i64,
        UnOp::I64Extend16S => (a as i16) as i64,
        UnOp::I64Extend32S => (a as i32) as i64,
        _ => unreachable!(),
    }
}

fn eval_const_binop_i32(b: BinOp, a: i32, c: i32) -> Option<i32> {
    let (ua, uc) = (a as u32, c as u32);
    Some(match b {
        BinOp::I32Eq => i32::from(a == c),
        BinOp::I32Ne => i32::from(a != c),
        BinOp::I32LtS => i32::from(a < c),
        BinOp::I32LtU => i32::from(ua < uc),
        BinOp::I32GtS => i32::from(a > c),
        BinOp::I32GtU => i32::from(ua > uc),
        BinOp::I32LeS => i32::from(a <= c),
        BinOp::I32LeU => i32::from(ua <= uc),
        BinOp::I32GeS => i32::from(a >= c),
        BinOp::I32GeU => i32::from(ua >= uc),
        BinOp::I32Add => a.wrapping_add(c),
        BinOp::I32Sub => a.wrapping_sub(c),
        BinOp::I32Mul => a.wrapping_mul(c),
        BinOp::I32DivS if c == 0 || (a == i32::MIN && c == -1) => return None,
        BinOp::I32DivS => a.wrapping_div(c),
        BinOp::I32DivU => ua.checked_div(uc)? as i32,
        BinOp::I32RemS if c == 0 => return None,
        BinOp::I32RemS if a == i32::MIN && c == -1 => 0,
        BinOp::I32RemS => a.wrapping_rem(c),
        BinOp::I32RemU => ua.checked_rem(uc)? as i32,
        BinOp::I32And => a & c,
        BinOp::I32Or => a | c,
        BinOp::I32Xor => a ^ c,
        BinOp::I32Shl => a.wrapping_shl(uc),
        BinOp::I32ShrS => a.wrapping_shr(uc),
        BinOp::I32ShrU => ua.wrapping_shr(uc) as i32,
        BinOp::I32Rotl => ua.rotate_left(uc & 31) as i32,
        BinOp::I32Rotr => ua.rotate_right(uc & 31) as i32,
        _ => return None,
    })
}

fn eval_const_binop_i64_cmp(b: BinOp, a: i64, c: i64) -> Option<i32> {
    let (ua, uc) = (a as u64, c as u64);
    Some(match b {
        BinOp::I64Eq => i32::from(a == c),
        BinOp::I64Ne => i32::from(a != c),
        BinOp::I64LtS => i32::from(a < c),
        BinOp::I64LtU => i32::from(ua < uc),
        BinOp::I64GtS => i32::from(a > c),
        BinOp::I64GtU => i32::from(ua > uc),
        BinOp::I64LeS => i32::from(a <= c),
        BinOp::I64LeU => i32::from(ua <= uc),
        BinOp::I64GeS => i32::from(a >= c),
        BinOp::I64GeU => i32::from(ua >= uc),
        _ => return None,
    })
}

fn eval_const_binop_i64_val(b: BinOp, a: i64, c: i64) -> Option<i64> {
    let (ua, uc) = (a as u64, c as u64);
    Some(match b {
        BinOp::I64Add => a.wrapping_add(c),
        BinOp::I64Sub => a.wrapping_sub(c),
        BinOp::I64Mul => a.wrapping_mul(c),
        BinOp::I64DivS if c == 0 || (a == i64::MIN && c == -1) => return None,
        BinOp::I64DivS => a.wrapping_div(c),
        BinOp::I64DivU => ua.checked_div(uc)? as i64,
        BinOp::I64RemS if c == 0 => return None,
        BinOp::I64RemS if a == i64::MIN && c == -1 => 0,
        BinOp::I64RemS => a.wrapping_rem(c),
        BinOp::I64RemU => ua.checked_rem(uc)? as i64,
        BinOp::I64And => a & c,
        BinOp::I64Or => a | c,
        BinOp::I64Xor => a ^ c,
        BinOp::I64Shl => a.wrapping_shl(uc as u32),
        BinOp::I64ShrS => a.wrapping_shr(uc as u32),
        BinOp::I64ShrU => ua.wrapping_shr(uc as u32) as i64,
        BinOp::I64Rotl => ua.rotate_left((uc as u32) & 63) as i64,
        BinOp::I64Rotr => ua.rotate_right((uc as u32) & 63) as i64,
        _ => return None,
    })
}
