//! Phase 2 library consolidation: `stitch_core` MDL admission + `egglog` 3-step law
//! non-redundancy pruning + TCB-verified `StratumRegistry` rebuild + compact `AutoDoc` export.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::Write as _;

use gnomon_kernel::{
    BinOp, CallTarget, EffectOp, Law, LawKind, LawList, MemWidth, Op, Region, RegionNode,
    RegionRef, Span, Stmt, Stratum, StratumId, StratumOp, StratumRegistry, TrapCode, UnOp, ValId,
    ValType,
};
use serde::{Deserialize, Serialize};
use stitch_core::{
    CompressionStepConfig, Expr, Invention, Lambda, Symbol, compression, compression_factor,
    rewrite_with_invention,
};

use crate::{EgglogSimplifier, EqSatConfig, SieveError, eqsat::count_region_nodes};

/// Configuration for `consolidate_registry`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConsolidationConfig {
    /// Minimum number of distinct verified solutions that must use an op for MDL admission.
    pub min_solutions: usize,
    /// Maximum `egglog` rewrite iterations used to test whether a law is redundant.
    pub max_derivation_steps: usize,
    /// Node budget for each `egglog` redundancy check.
    pub max_eqsat_nodes: usize,
    /// Charge the `StratumOp` body's own SSA node count when computing net MDL compression.
    pub include_definition_cost: bool,
}

impl Default for ConsolidationConfig {
    fn default() -> Self {
        Self {
            min_solutions: 2,
            max_derivation_steps: 3,
            max_eqsat_nodes: 5_000,
            include_definition_cost: true,
        }
    }
}

/// Per-stratum MDL scoring outcome from `stitch_core` rewriting & SSA node accounting.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct OpMdlReport {
    pub stratum_id: u32,
    pub name: String,
    pub layer: u16,
    pub solutions_using: usize,
    pub total_uses: usize,
    pub body_ssa_nodes: usize,
    pub ssa_nodes_before: usize,
    pub ssa_nodes_after: usize,
    pub stitch_cost_before: i32,
    pub stitch_cost_after: i32,
    pub stitch_compression_factor: f64,
    pub kept: bool,
    pub reason: String,
}

/// Per-law non-redundancy outcome from bounded `egglog` derivability checking.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LawRedundancyReport {
    pub stratum_id: u32,
    pub stratum_name: String,
    pub law_name: String,
    pub kept: bool,
    pub reason: String,
}

/// Complete consolidation report plus compact Delta Spec / `AutoDoc` for AI prompt caching.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ConsolidationReport {
    pub op_reports: Vec<OpMdlReport>,
    pub law_reports: Vec<LawRedundancyReport>,
    pub kept_strata: Vec<u32>,
    pub pruned_strata: Vec<u32>,
    pub kept_laws: usize,
    pub pruned_laws: usize,
    pub autodoc_markdown: String,
    pub delta_spec_json: serde_json::Value,
}

/// Candidate abstraction discovered offline by `stitch_core::compression`.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct DiscoveredAbstraction {
    pub name: String,
    pub arity: usize,
    pub body_expr: String,
    pub uses: i32,
    pub initial_cost: i32,
    pub final_cost: i32,
    pub compression_multiplier: f64,
}

/// Runs library consolidation over `registry` and `verified_solutions`:
/// 1. Tests every promoted law for redundancy within `<= cfg.max_derivation_steps` (`<= 3`)
///    `egglog` steps using all other retained laws $R \setminus \{r\}$.
/// 2. Scores every promoted `Stratum` via `stitch_core` silent structural rewriting
///    (`rewrite_with_invention`) and `GnomonIR` SSA node MDL compression across
///    `>= cfg.min_solutions` (`>= 2`) distinct verified solutions.
/// 3. Computes transitive DAG dependencies of retained Strata and rebuilds a fresh
///    `StratumRegistry` by re-admitting each retained `Stratum` through `gnomon-kernel`'s
///    `promote_stratum` gate.
/// 4. Emits a compact Delta Spec / `AutoDoc` summarizing the active library.
///
/// This function NEVER writes to stdout, making it safe inside stdio MCP servers.
pub fn consolidate_registry(
    registry: &StratumRegistry,
    verified_solutions: &[Region],
    cfg: &ConsolidationConfig,
) -> Result<(StratumRegistry, ConsolidationReport), SieveError> {
    let mut strata: Vec<Stratum> = registry.promoted().to_vec();
    strata.sort_by_key(|s| (s.op.layer, s.op.id.0));

    // -----------------------------------------------------------------------
    // Phase 1: Greedy law non-redundancy check (<= 3 egglog steps)
    // -----------------------------------------------------------------------
    // Maintain active laws per stratum; check each law r against all other currently
    // active laws R \ {r}. Checking in reverse order ensures earlier canonical laws win
    // ties when two laws are mutual duplicates.
    let mut active_laws: BTreeMap<u32, Vec<bool>> = strata
        .iter()
        .map(|s| (s.op.id.0, vec![true; s.laws.len()]))
        .collect();
    let mut law_reasons: BTreeMap<(u32, usize), String> = BTreeMap::new();

    let eq_steps = cfg.max_derivation_steps.clamp(1, 3);
    let simplifier = EgglogSimplifier::new(EqSatConfig {
        max_iters: eq_steps,
        max_nodes: cfg.max_eqsat_nodes,
        timeout_ms: 500,
    });

    for stratum in strata.iter().rev() {
        let sid = stratum.op.id.0;
        let laws_vec: Vec<Law> = stratum.laws.iter().cloned().collect();
        for idx in (0..laws_vec.len()).rev() {
            let law = &laws_vec[idx];
            match law.kind {
                LawKind::Algebraic if !law.has_precondition() => {
                    let scratch = build_scratch_registry_without(
                        &strata,
                        &active_laws,
                        sid,
                        idx,
                    )?;
                    let (simp_lhs, _) = simplifier.simplify_region(&law.lhs, &scratch)?;
                    let (simp_rhs, _) = simplifier.simplify_region(&law.rhs, &scratch)?;
                    let lhs_canon = encode_region_as_stitch_expr(&simp_lhs, &law.params)?;
                    let rhs_canon = encode_region_as_stitch_expr(&simp_rhs, &law.params)?;
                    if lhs_canon.to_string_curried(None) == rhs_canon.to_string_curried(None) {
                        if let Some(flags) = active_laws.get_mut(&sid) {
                            flags[idx] = false;
                        }
                        law_reasons.insert(
                            (sid, idx),
                            format!("pruned: derivable from R\\{{r}} in <= {eq_steps} egglog steps"),
                        );
                    } else {
                        law_reasons.insert((sid, idx), "kept: non-redundant algebraic law".into());
                    }
                }
                LawKind::Algebraic => {
                    // Conditional law: check exact canonical duplicate against other active laws.
                    let dup = has_canonical_duplicate_law(&strata, &active_laws, sid, idx, law)?;
                    if dup {
                        if let Some(flags) = active_laws.get_mut(&sid) {
                            flags[idx] = false;
                        }
                        law_reasons.insert((sid, idx), "pruned: duplicate conditional law".into());
                    } else {
                        law_reasons.insert((sid, idx), "kept: non-redundant conditional law".into());
                    }
                }
                LawKind::MemoryFrame { .. } => {
                    let dup = has_canonical_duplicate_law(&strata, &active_laws, sid, idx, law)?;
                    if dup {
                        if let Some(flags) = active_laws.get_mut(&sid) {
                            flags[idx] = false;
                        }
                        law_reasons.insert((sid, idx), "pruned: duplicate memory-frame law".into());
                    } else {
                        law_reasons.insert((sid, idx), "kept: non-redundant memory-frame law".into());
                    }
                }
            }
        }
    }

    // -----------------------------------------------------------------------
    // Phase 2: MDL admission via stitch_core silent rewriting + SSA node count
    // -----------------------------------------------------------------------
    let mut lowered_solutions: Vec<Region> = Vec::with_capacity(verified_solutions.len());
    let mut lowered_exprs: Vec<Expr> = Vec::with_capacity(verified_solutions.len());
    for sol in verified_solutions {
        let mut next_val = 0u32;
        let lowered = registry
            .lower_region_to_layer0(sol, &mut next_val)
            .unwrap_or_else(|_| sol.clone());
        let expr = encode_region_as_stitch_expr(&lowered, &[])?;
        lowered_solutions.push(lowered);
        lowered_exprs.push(expr);
    }

    let mut op_reports: Vec<OpMdlReport> = Vec::with_capacity(strata.len());
    let mut initial_keep: BTreeSet<u32> = BTreeSet::new();

    for stratum in &strata {
        let sid = stratum.op.id.0;
        let kept_law_count = active_laws
            .get(&sid)
            .map(|flags| flags.iter().filter(|&&b| b).count())
            .unwrap_or(0);

        let mut next_val = 0u32;
        let lowered_body = registry
            .lower_region_to_layer0(&stratum.op.body, &mut next_val)
            .unwrap_or_else(|_| stratum.op.body.clone());
        let body_ssa_nodes = count_region_nodes(&lowered_body).max(1);
        let (inv_opt, inv_name) = build_stitch_invention(&stratum.op, &lowered_body)?;

        let mut solutions_using = 0usize;
        let mut total_uses = 0usize;
        let mut stitch_cost_before = 0i32;
        let mut stitch_cost_after = 0i32;
        let mut ssa_nodes_before = 0usize;

        for (sol_idx, orig_sol) in verified_solutions.iter().enumerate() {
            let sol_expr = &lowered_exprs[sol_idx];
            let orig_cost = sol_expr.cost();
            stitch_cost_before += orig_cost;
            ssa_nodes_before += count_region_nodes(&lowered_solutions[sol_idx]);

            let direct_calls = count_stratum_calls_in_region(orig_sol, stratum.op.id);
            let (stitch_uses, rw_cost) = if let Some(ref inv) = inv_opt {
                let rewritten = rewrite_with_invention(sol_expr.clone(), inv);
                let u = count_prim_in_expr(&rewritten, &inv_name);
                (u, rewritten.cost())
            } else {
                (0, orig_cost)
            };

            let matched = stitch_uses.max(direct_calls);
            if matched > 0 {
                solutions_using += 1;
                total_uses += matched;
            }
            if stitch_uses > 0 {
                stitch_cost_after += rw_cost;
            } else if direct_calls > 0 {
                // Direct call not re-matched by stitch (e.g. multi-return/effectful op):
                // approximate cost reduction consistently with stitch_core prim cost.
                let body_cost = encode_region_as_stitch_expr(&lowered_body, &[])
                    .map(|e| e.cost())
                    .unwrap_or(100);
                let call_cost = 100 + stratum.op.params.len() as i32;
                let saved = (body_cost - call_cost).max(0) * direct_calls as i32;
                stitch_cost_after += (orig_cost - saved).max(1);
            } else {
                stitch_cost_after += orig_cost;
            }
        }

        let def_ssa_cost = if cfg.include_definition_cost { body_ssa_nodes } else { 0 };
        let per_use_ssa_saving = body_ssa_nodes.saturating_sub(1);
        let gross_ssa_saving = total_uses.saturating_mul(per_use_ssa_saving);
        let ssa_nodes_after = if total_uses > 0 {
            ssa_nodes_before.saturating_sub(gross_ssa_saving).saturating_add(def_ssa_cost)
        } else {
            ssa_nodes_before
        };

        let factor = if stitch_cost_after > 0 && stitch_cost_before > 0 {
            f64::from(stitch_cost_before) / f64::from(stitch_cost_after)
        } else {
            1.0
        };

        let (kept, reason) = if kept_law_count == 0 {
            (false, "pruned: all laws derivable from other strata".into())
        } else if solutions_using < cfg.min_solutions {
            (
                false,
                format!(
                    "pruned: used in {solutions_using} solutions (< min_solutions={})",
                    cfg.min_solutions
                ),
            )
        } else if ssa_nodes_after >= ssa_nodes_before {
            (
                false,
                format!(
                    "pruned: no net SSA MDL compression (before={ssa_nodes_before}, after={ssa_nodes_after})"
                ),
            )
        } else {
            initial_keep.insert(sid);
            (
                true,
                format!(
                    "kept: compresses SSA {ssa_nodes_before}->{ssa_nodes_after} across {solutions_using} solutions (stitch {factor:.2}x)"
                ),
            )
        };

        op_reports.push(OpMdlReport {
            stratum_id: sid,
            name: stratum.op.name.clone(),
            layer: stratum.op.layer,
            solutions_using,
            total_uses,
            body_ssa_nodes,
            ssa_nodes_before,
            ssa_nodes_after,
            stitch_cost_before,
            stitch_cost_after,
            stitch_compression_factor: factor,
            kept,
            reason,
        });
    }

    // -----------------------------------------------------------------------
    // Phase 3: Transitive DAG dependency closure for retained Strata
    // -----------------------------------------------------------------------
    let stratum_by_id: BTreeMap<u32, &Stratum> =
        strata.iter().map(|s| (s.op.id.0, s)).collect();
    let mut final_keep = initial_keep.clone();
    let mut worklist: Vec<u32> = initial_keep.iter().copied().collect();
    while let Some(sid) = worklist.pop() {
        // Ensure any kept stratum (including newly added DAG dependencies) has >= 1 active law
        // BEFORE scanning its active laws for further transitive dependencies.
        if let Some(flags) = active_laws.get_mut(&sid)
            && !flags.iter().any(|&b| b)
            && let Some(first) = flags.first_mut()
        {
            *first = true;
            law_reasons.insert(
                (sid, 0),
                "kept: required anchor law for DAG dependency".into(),
            );
        }
        if let Some(st) = stratum_by_id.get(&sid) {
            let mut deps = BTreeSet::new();
            collect_stratum_deps(&st.op.body, &mut deps);
            if let Some(flags) = active_laws.get(&sid) {
                for (i, law) in st.laws.iter().enumerate() {
                    if flags.get(i).copied().unwrap_or(false) {
                        collect_stratum_deps(&law.precondition, &mut deps);
                        collect_stratum_deps(&law.lhs, &mut deps);
                        collect_stratum_deps(&law.rhs, &mut deps);
                    }
                }
            }
            for dep in deps {
                if dep != sid && stratum_by_id.contains_key(&dep) && final_keep.insert(dep) {
                    worklist.push(dep);
                }
            }
        }
    }

    // Update op_reports for transitively retained dependencies.
    for rep in &mut op_reports {
        if !rep.kept && final_keep.contains(&rep.stratum_id) {
            rep.kept = true;
            rep.reason = "kept: transitive DAG dependency of a retained higher-layer stratum".into();
        }
    }

    // -----------------------------------------------------------------------
    // Phase 4: Rebuild a clean StratumRegistry through gnomon-kernel TCB gate
    // -----------------------------------------------------------------------
    let mut rebuilt = StratumRegistry::new();
    let mut kept_strata = Vec::new();
    let mut pruned_strata = Vec::new();
    let mut law_reports = Vec::new();
    let mut kept_laws = 0usize;
    let mut pruned_laws = 0usize;

    for stratum in &strata {
        let sid = stratum.op.id.0;
        let is_kept = final_keep.contains(&sid);
        let flags = active_laws.get(&sid).cloned().unwrap_or_default();

        let mut retained_laws = Vec::new();
        for (idx, law) in stratum.laws.iter().enumerate() {
            let law_kept = is_kept && flags.get(idx).copied().unwrap_or(false);
            if law_kept {
                retained_laws.push(law.clone());
                kept_laws += 1;
            } else {
                pruned_laws += 1;
            }
            let reason = if !is_kept {
                "pruned: owning stratum pruned by MDL".into()
            } else {
                law_reasons
                    .get(&(sid, idx))
                    .cloned()
                    .unwrap_or_else(|| "kept".into())
            };
            law_reports.push(LawRedundancyReport {
                stratum_id: sid,
                stratum_name: stratum.op.name.clone(),
                law_name: law.name.clone(),
                kept: law_kept,
                reason,
            });
        }

        if is_kept {
            let new_stratum = Stratum {
                op: stratum.op.clone(),
                laws: LawList::from_vec(retained_laws),
            };
            rebuilt.promote_stratum(new_stratum).map_err(|e| {
                SieveError::EqSatError(format!("TCB re-admission failed during consolidate: {e:?}"))
            })?;
            kept_strata.push(sid);
        } else {
            pruned_strata.push(sid);
        }
    }

    let (autodoc_markdown, delta_spec_json) = render_autodoc(&rebuilt);

    Ok((
        rebuilt,
        ConsolidationReport {
            op_reports,
            law_reports,
            kept_strata,
            pruned_strata,
            kept_laws,
            pruned_laws,
            autodoc_markdown,
            delta_spec_json,
        },
    ))
}

/// Offline abstraction discovery using `stitch_core::compression`.
///
/// Note: upstream `stitch_core::compression` writes diagnostic progress lines to `stdout`,
/// so call this from CLI/offline workflows rather than inside a stdio MCP server.
pub fn discover_candidate_inventions(
    solutions: &[Region],
    max_arity: usize,
    iterations: usize,
) -> Result<Vec<DiscoveredAbstraction>, SieveError> {
    if solutions.len() < 2 || iterations == 0 {
        return Ok(Vec::new());
    }
    let exprs: Vec<Expr> = solutions
        .iter()
        .map(|r| encode_region_as_stitch_expr(r, &[]))
        .collect::<Result<_, _>>()?;
    let corpus = Expr::programs(exprs);
    let tasks: Vec<String> = (0..solutions.len()).map(|i| format!("sol_{i}")).collect();
    let cfg = CompressionStepConfig {
        max_arity,
        threads: 1,
        no_stats: true,
        batch: 1,
        dynamic_batch: false,
        inv_candidates: 1,
        hole_choice: stitch_core::HoleChoice::DepthFirst,
        no_mismatch_check: false,
        no_top_lambda: true,
        track: None,
        follow_track: false,
        verbose_worklist: false,
        verbose_best: false,
        print_stats: 0,
        show_rewritten: false,
        no_opt_free_vars: false,
        no_opt_single_use: false,
        no_opt_single_task: false,
        no_opt_upper_bound: false,
        no_opt_force_multiuse: false,
        no_opt_useless_abstract: false,
        no_opt_arity_zero: false,
        no_other_util: false,
        rewrite_check: false,
        utility_by_rewrite: false,
        dreamcoder_comparison: false,
    };
    let steps = compression(&corpus, &None, iterations, &cfg, &tasks, &[]);
    let mut out = Vec::with_capacity(steps.len());
    for st in steps {
        let mult = compression_factor(&corpus, &st.rewritten);
        out.push(DiscoveredAbstraction {
            name: st.inv.name.clone(),
            arity: st.inv.arity,
            body_expr: st.inv.body.to_string(),
            uses: st.uses,
            initial_cost: st.initial_cost,
            final_cost: st.final_cost,
            compression_multiplier: mult,
        });
    }
    Ok(out)
}

/// Renders a compact prompt-cacheable Markdown AutoDoc + structured JSON Delta Spec
/// for all currently promoted Strata in `registry`.
pub fn render_autodoc(registry: &StratumRegistry) -> (String, serde_json::Value) {
    let mut strata: Vec<&Stratum> = registry.promoted().iter().collect();
    strata.sort_by_key(|s| (s.op.layer, s.op.id.0));

    let mut md = String::new();
    let _ = writeln!(md, "# Gnomon Active Strata Registry ({} ops)\n", strata.len());
    let mut json_strata = Vec::with_capacity(strata.len());

    for st in &strata {
        let params_s = st
            .op
            .params
            .iter()
            .map(|(v, ty)| format!("v{}:{}", v.0, ty_str(*ty)))
            .collect::<Vec<_>>()
            .join(", ");
        let results_s = st
            .op
            .results
            .iter()
            .map(|ty| ty_str(*ty))
            .collect::<Vec<_>>()
            .join(", ");
        let _ = writeln!(
            md,
            "## L{} `{}` (id={}): ({params_s}) -> ({results_s})",
            st.op.layer, st.op.name, st.op.id.0
        );
        if !st.op.docstring.is_empty() {
            let _ = writeln!(md, "- doc: {}", st.op.docstring);
        }
        let mut json_laws = Vec::new();
        for law in st.laws.iter() {
            let kind_s = match law.kind {
                LawKind::Algebraic => "algebraic".to_string(),
                LawKind::MemoryFrame { untouched_mem } => {
                    format!("memory_frame(mem={})", untouched_mem.0)
                }
            };
            let digest_hex: String = law.proof_digest.iter().take(6).map(|b| format!("{b:02x}")).collect();
            let _ = writeln!(
                md,
                "- law `{}` [{}] (digest={}..., pre={})",
                law.name,
                kind_s,
                digest_hex,
                law.has_precondition()
            );
            json_laws.push(serde_json::json!({
                "name": law.name,
                "kind": kind_s,
                "has_precondition": law.has_precondition(),
                "proof_digest_prefix": digest_hex,
            }));
        }
        let _ = writeln!(md);
        json_strata.push(serde_json::json!({
            "id": st.op.id.0,
            "name": st.op.name,
            "layer": st.op.layer,
            "params": st.op.params.iter().map(|(v, ty)| serde_json::json!({"id": v.0, "ty": ty_str(*ty)})).collect::<Vec<_>>(),
            "results": st.op.results.iter().map(|ty| ty_str(*ty)).collect::<Vec<_>>(),
            "docstring": st.op.docstring,
            "laws": json_laws,
        }));
    }

    let delta_spec = serde_json::json!({
        "active_strata_count": strata.len(),
        "strata": json_strata,
    });
    (md, delta_spec)
}

/// Encodes a `GnomonIR` `Region` into a canonical, alpha-normalized `stitch_core::Expr`.
///
/// When `params` is non-empty, parameter `ValId`s are bound to `Expr::ivar(0..arity)` so
/// the resulting expression can be used as a `stitch_core::Invention` body or compared
/// modulo SSA `ValId` renaming.
pub fn encode_region_as_stitch_expr(
    region: &Region,
    params: &[(ValId, ValType)],
) -> Result<Expr, SieveError> {
    let mut env: HashMap<ValId, Expr> = HashMap::new();
    for (idx, &(vid, _)) in params.iter().enumerate() {
        env.insert(vid, Expr::ivar(idx as i32));
    }
    encode_node_ref(region.as_ref(), &mut env)
}

fn build_stitch_invention(
    op: &StratumOp,
    lowered_body: &Region,
) -> Result<(Option<Invention>, String), SieveError> {
    let inv_name = format!("__gnomon_inv_{}", op.id.0);
    // Only single-output / pure-or-structured bodies with at least 2 nodes benefit from
    // stitch_core sub-tree matching. Remap actually-used parameter IVars densely to 0..k
    // so stitch_core's `arity == max_ivar + 1` invariant always holds.
    let raw_expr = encode_region_as_stitch_expr(lowered_body, &op.params)?;
    let mut used_ivars = BTreeSet::new();
    collect_ivars(&raw_expr, &mut used_ivars);
    let mut remap = HashMap::new();
    for (new_idx, old_idx) in used_ivars.into_iter().enumerate() {
        remap.insert(old_idx, new_idx as i32);
    }
    let dense_expr = remap_ivars(&raw_expr, &remap);
    let arity = remap.len();
    // stitch_core requires non-trivial inventions (not a bare IVar or bare Prim).
    let is_trivial = matches!(
        dense_expr.get_root(),
        Lambda::IVar(_) | Lambda::Prim(_) | Lambda::Var(_)
    );
    if is_trivial {
        return Ok((None, inv_name));
    }
    Ok((Some(Invention::new(dense_expr, arity, &inv_name)), inv_name))
}

fn collect_ivars(expr: &Expr, out: &mut BTreeSet<i32>) {
    fn walk(expr: &Expr, id: stitch_core::Id, out: &mut BTreeSet<i32>) {
        match expr.get(id) {
            Lambda::IVar(i) => {
                out.insert(*i);
            }
            Lambda::Var(_) | Lambda::Prim(_) => {}
            Lambda::App([f, x]) => {
                walk(expr, *f, out);
                walk(expr, *x, out);
            }
            Lambda::Lam([b]) => walk(expr, *b, out),
            Lambda::Programs(ps) => {
                for p in ps {
                    walk(expr, *p, out);
                }
            }
        }
    }
    walk(expr, expr.root(), out);
}

fn remap_ivars(expr: &Expr, map: &HashMap<i32, i32>) -> Expr {
    fn rebuild(expr: &Expr, id: stitch_core::Id, map: &HashMap<i32, i32>) -> Expr {
        match expr.get(id) {
            Lambda::IVar(i) => Expr::ivar(*map.get(i).unwrap_or(i)),
            Lambda::Var(v) => Expr::var(*v),
            Lambda::Prim(p) => Expr::prim(*p),
            Lambda::App([f, x]) => Expr::app(rebuild(expr, *f, map), rebuild(expr, *x, map)),
            Lambda::Lam([b]) => Expr::lam(rebuild(expr, *b, map)),
            Lambda::Programs(ps) => {
                Expr::programs(ps.iter().map(|p| rebuild(expr, *p, map)).collect())
            }
        }
    }
    rebuild(expr, expr.root(), map)
}

fn count_prim_in_expr(expr: &Expr, name: &str) -> usize {
    fn walk(expr: &Expr, id: stitch_core::Id, sym: Symbol) -> usize {
        match expr.get(id) {
            Lambda::Prim(p) => usize::from(*p == sym),
            Lambda::IVar(_) | Lambda::Var(_) => 0,
            Lambda::App([f, x]) => walk(expr, *f, sym) + walk(expr, *x, sym),
            Lambda::Lam([b]) => walk(expr, *b, sym),
            Lambda::Programs(ps) => ps.iter().map(|p| walk(expr, *p, sym)).sum(),
        }
    }
    walk(expr, expr.root(), Symbol::from(name))
}

fn encode_node_ref(r: RegionRef<'_>, env: &mut HashMap<ValId, Expr>) -> Result<Expr, SieveError> {
    match r.node {
        RegionNode::Block(span) => encode_block(r, span, env),
        RegionNode::IfElse { cond, then_region, else_region, .. } => {
            let c = lookup_val(env, cond);
            let mut then_env = env.clone();
            let t = encode_node_ref(
                r.child(then_region)
                    .ok_or_else(|| SieveError::EqSatError("missing then_region".into()))?,
                &mut then_env,
            )?;
            let mut else_env = env.clone();
            let e = encode_node_ref(
                r.child(else_region)
                    .ok_or_else(|| SieveError::EqSatError("missing else_region".into()))?,
                &mut else_env,
            )?;
            Ok(app3(prim("if_else"), c, t, e))
        }
        RegionNode::BoundedLoop { max_iters, init_vars, state_vars, body } => {
            let mut loop_env = env.clone();
            let mut inits = Vec::new();
            for i in 0..init_vars.len {
                if let Some(v) = r.region.try_val(init_vars, i) {
                    inits.push(lookup_val(env, v));
                }
            }
            for i in 0..state_vars.len {
                if let Some((sv, _)) = r.region.try_var(state_vars, i) {
                    loop_env.insert(sv, prim(&format!("loop_state_{i}")));
                }
            }
            let b = encode_node_ref(
                r.child(body)
                    .ok_or_else(|| SieveError::EqSatError("missing bloop body".into()))?,
                &mut loop_env,
            )?;
            Ok(app2(
                prim(&format!("bloop_{max_iters}")),
                tuple_expr(&inits),
                b,
            ))
        }
        RegionNode::InvariantLoop {
            init_vars,
            state_vars,
            cond,
            invariant_pred,
            fuel_measure,
            body,
        } => {
            let mut loop_env = env.clone();
            let mut inits = Vec::new();
            for i in 0..init_vars.len {
                if let Some(v) = r.region.try_val(init_vars, i) {
                    inits.push(lookup_val(env, v));
                }
            }
            for i in 0..state_vars.len {
                if let Some((sv, _)) = r.region.try_var(state_vars, i) {
                    loop_env.insert(sv, prim(&format!("iloop_state_{i}")));
                }
            }
            let c = encode_node_ref(
                r.child(cond)
                    .ok_or_else(|| SieveError::EqSatError("missing iloop cond".into()))?,
                &mut loop_env.clone(),
            )?;
            let inv = encode_node_ref(
                r.child(invariant_pred)
                    .ok_or_else(|| SieveError::EqSatError("missing iloop inv".into()))?,
                &mut loop_env.clone(),
            )?;
            let fuel = encode_node_ref(
                r.child(fuel_measure)
                    .ok_or_else(|| SieveError::EqSatError("missing iloop fuel".into()))?,
                &mut loop_env.clone(),
            )?;
            let b = encode_node_ref(
                r.child(body)
                    .ok_or_else(|| SieveError::EqSatError("missing iloop body".into()))?,
                &mut loop_env,
            )?;
            let head = app2(prim("iloop"), tuple_expr(&inits), c);
            Ok(app3(head, inv, fuel, b))
        }
    }
}

fn encode_block(
    r: RegionRef<'_>,
    span: Span,
    env: &mut HashMap<ValId, Expr>,
) -> Result<Expr, SieveError> {
    let mut effects: Vec<Expr> = Vec::new();
    let mut term_expr: Option<Expr> = None;

    for i in 0..span.len {
        let stmt = r
            .region
            .try_stmt(span, i)
            .ok_or_else(|| SieveError::EqSatError("invalid stmt span".into()))?;
        match stmt {
            Stmt::Let { dst, ty: _, op } => {
                let e = encode_op(op, env);
                if op_may_trap_or_mutate(op) {
                    effects.push(e.clone());
                }
                env.insert(dst, e);
            }
            Stmt::Effect(eff) => {
                if !matches!(eff, EffectOp::Nop) {
                    effects.push(encode_effect(eff, env));
                }
            }
            Stmt::Call { results, target, args } => {
                let head = match target {
                    CallTarget::Func(f) => prim(&format!("call.func_{}", f.0)),
                    CallTarget::Host(h) => prim(&format!("call.host_{}", h.0)),
                    CallTarget::Stratum(s) => prim(&format!("call.stratum_{}", s.0)),
                };
                let mut call_e = head;
                for a in 0..args.len {
                    if let Some(v) = r.region.try_val(args, a) {
                        call_e = Expr::app(call_e, lookup_val(env, v));
                    }
                }
                if results.len == 0 {
                    effects.push(call_e);
                } else if results.len == 1 {
                    if let Some((dst, _)) = r.region.try_var(results, 0) {
                        env.insert(dst, call_e);
                    }
                } else {
                    for k in 0..results.len {
                        if let Some((dst, _)) = r.region.try_var(results, k) {
                            env.insert(
                                dst,
                                Expr::app(prim(&format!("proj_{k}")), call_e.clone()),
                            );
                        }
                    }
                }
            }
            Stmt::Region { results, region } => {
                let sub = r
                    .child(region)
                    .ok_or_else(|| SieveError::EqSatError("missing subregion".into()))?;
                let mut sub_env = env.clone();
                let sub_e = encode_node_ref(sub, &mut sub_env)?;
                if results.len == 0 {
                    effects.push(sub_e);
                } else if results.len == 1 {
                    if let Some((dst, _)) = r.region.try_var(results, 0) {
                        env.insert(dst, sub_e);
                    }
                } else {
                    for k in 0..results.len {
                        if let Some((dst, _)) = r.region.try_var(results, k) {
                            env.insert(
                                dst,
                                Expr::app(prim(&format!("proj_{k}")), sub_e.clone()),
                            );
                        }
                    }
                }
            }
            Stmt::Yield(vals) => {
                let mut items = Vec::with_capacity(vals.len as usize);
                for k in 0..vals.len {
                    if let Some(v) = r.region.try_val(vals, k) {
                        items.push(lookup_val(env, v));
                    }
                }
                term_expr = Some(tuple_expr(&items));
            }
            Stmt::Return(vals) => {
                let mut items = Vec::with_capacity(vals.len as usize);
                for k in 0..vals.len {
                    if let Some(v) = r.region.try_val(vals, k) {
                        items.push(lookup_val(env, v));
                    }
                }
                term_expr = Some(Expr::app(prim("return"), tuple_expr(&items)));
            }
            Stmt::Break { depth, cond, values } => {
                let mut items = Vec::with_capacity(values.len as usize);
                for k in 0..values.len {
                    if let Some(v) = r.region.try_val(values, k) {
                        items.push(lookup_val(env, v));
                    }
                }
                let br = match cond {
                    Some(c) => app2(
                        prim(&format!("br_if_{depth}")),
                        lookup_val(env, c),
                        tuple_expr(&items),
                    ),
                    None => Expr::app(prim(&format!("br_{depth}")), tuple_expr(&items)),
                };
                effects.push(br);
            }
            Stmt::Continue { depth, cond, values } => {
                let mut items = Vec::with_capacity(values.len as usize);
                for k in 0..values.len {
                    if let Some(v) = r.region.try_val(values, k) {
                        items.push(lookup_val(env, v));
                    }
                }
                let ct = match cond {
                    Some(c) => app2(
                        prim(&format!("cont_if_{depth}")),
                        lookup_val(env, c),
                        tuple_expr(&items),
                    ),
                    None => Expr::app(prim(&format!("cont_{depth}")), tuple_expr(&items)),
                };
                effects.push(ct);
            }
        }
    }

    let result = term_expr.unwrap_or_else(|| prim("unit"));
    Ok(effects.into_iter().rev().fold(result, |acc, eff| app2(prim("seq"), eff, acc)))
}

fn op_may_trap_or_mutate(op: Op) -> bool {
    matches!(
        op,
        Op::Bin(
            BinOp::I32DivS
                | BinOp::I32DivU
                | BinOp::I32RemS
                | BinOp::I32RemU
                | BinOp::I64DivS
                | BinOp::I64DivU
                | BinOp::I64RemS
                | BinOp::I64RemU,
            _,
            _
        ) | Op::Load { .. }
            | Op::MemoryGrow { .. }
    )
}

fn encode_op(op: Op, env: &HashMap<ValId, Expr>) -> Expr {
    match op {
        Op::ConstI32(c) => prim(&format!("i32.const_{c}")),
        Op::ConstI64(c) => prim(&format!("i64.const_{c}")),
        Op::Copy(v) => lookup_val(env, v),
        Op::Un(u, a) => Expr::app(prim(unop_tag(u)), lookup_val(env, a)),
        Op::Bin(b, l, r) => app2(prim(binop_tag(b)), lookup_val(env, l), lookup_val(env, r)),
        Op::Select { cond, true_val, false_val } => app3(
            prim("select"),
            lookup_val(env, cond),
            lookup_val(env, true_val),
            lookup_val(env, false_val),
        ),
        Op::Load { mem, addr, offset, width, signed, result_ty } => Expr::app(
            prim(&format!(
                "load_m{}_o{}_{}_{}_{}",
                mem.0,
                offset,
                width_tag(width),
                if signed { "s" } else { "u" },
                ty_str(result_ty)
            )),
            lookup_val(env, addr),
        ),
        Op::GlobalGet(g) => prim(&format!("global.get_{}", g.0)),
        Op::MemorySize(m) => prim(&format!("mem.size_{}", m.0)),
        Op::MemoryGrow { mem, delta } => {
            Expr::app(prim(&format!("mem.grow_{}", mem.0)), lookup_val(env, delta))
        }
    }
}

fn encode_effect(eff: EffectOp, env: &HashMap<ValId, Expr>) -> Expr {
    match eff {
        EffectOp::Store { mem, addr, offset, width, val } => app2(
            prim(&format!("store_m{}_o{}_{}", mem.0, offset, width_tag(width))),
            lookup_val(env, addr),
            lookup_val(env, val),
        ),
        EffectOp::MemoryCopy { dst_mem, src_mem, dst, src, len } => app3(
            prim(&format!("mem.copy_m{}_m{}", dst_mem.0, src_mem.0)),
            lookup_val(env, dst),
            lookup_val(env, src),
            lookup_val(env, len),
        ),
        EffectOp::MemoryFill { mem, dst, val, len } => app3(
            prim(&format!("mem.fill_m{}", mem.0)),
            lookup_val(env, dst),
            lookup_val(env, val),
            lookup_val(env, len),
        ),
        EffectOp::GlobalSet { id, val } => {
            Expr::app(prim(&format!("global.set_{}", id.0)), lookup_val(env, val))
        }
        EffectOp::Trap(t) => prim(trap_tag(t)),
        EffectOp::Nop => prim("nop"),
    }
}

fn lookup_val(env: &HashMap<ValId, Expr>, v: ValId) -> Expr {
    env.get(&v).cloned().unwrap_or_else(|| prim(&format!("free_v{}", v.0)))
}

fn prim(s: &str) -> Expr {
    Expr::prim(Symbol::from(s))
}

fn app2(f: Expr, a: Expr, b: Expr) -> Expr {
    Expr::app(Expr::app(f, a), b)
}

fn app3(f: Expr, a: Expr, b: Expr, c: Expr) -> Expr {
    Expr::app(app2(f, a, b), c)
}

fn tuple_expr(items: &[Expr]) -> Expr {
    match items {
        [] => prim("unit"),
        [single] => single.clone(),
        many => many.iter().skip(1).fold(many[0].clone(), |acc, x| app2(prim("pair"), acc, x.clone())),
    }
}

fn build_scratch_registry_without(
    strata: &[Stratum],
    active_laws: &BTreeMap<u32, Vec<bool>>,
    exclude_sid: u32,
    exclude_law_idx: usize,
) -> Result<StratumRegistry, SieveError> {
    let mut reg = StratumRegistry::new();
    for st in strata {
        let sid = st.op.id.0;
        let flags = active_laws.get(&sid);
        let mut laws: Vec<Law> = st
            .laws
            .iter()
            .enumerate()
            .filter(|&(idx, _)| {
                !(sid == exclude_sid && idx == exclude_law_idx)
                    && flags.and_then(|f| f.get(idx)).copied().unwrap_or(false)
            })
            .map(|(_, l)| l.clone())
            .collect();
        if laws.is_empty() {
            // Keep the op available for DAG/type checking without adding any rewrite rule:
            // a trivial empty-to-empty law has identical lhs/rhs and never fires in egglog.
            laws.push(Law {
                name: format!("__anchor_{sid}"),
                kind: LawKind::Algebraic,
                params: Vec::new(),
                precondition: Region::empty(),
                lhs: Region::empty(),
                rhs: Region::empty(),
                proof_digest: [0xff; 32],
            });
        }
        reg.promote_stratum(Stratum { op: st.op.clone(), laws: LawList::from_vec(laws) })
            .map_err(|e| SieveError::EqSatError(format!("scratch registry build failed: {e:?}")))?;
    }
    Ok(reg)
}

fn has_canonical_duplicate_law(
    strata: &[Stratum],
    active_laws: &BTreeMap<u32, Vec<bool>>,
    sid: u32,
    law_idx: usize,
    law: &Law,
) -> Result<bool, SieveError> {
    let lhs_e = encode_region_as_stitch_expr(&law.lhs, &law.params)?.to_string_curried(None);
    let rhs_e = encode_region_as_stitch_expr(&law.rhs, &law.params)?.to_string_curried(None);
    let pre_e = encode_region_as_stitch_expr(&law.precondition, &law.params)?.to_string_curried(None);
    for st in strata {
        let other_sid = st.op.id.0;
        let flags = active_laws.get(&other_sid);
        for (idx, other) in st.laws.iter().enumerate() {
            if other_sid == sid && idx == law_idx {
                continue;
            }
            if !flags.and_then(|f| f.get(idx)).copied().unwrap_or(false) {
                continue;
            }
            if other.kind != law.kind || other.params.len() != law.params.len() {
                continue;
            }
            let o_lhs = encode_region_as_stitch_expr(&other.lhs, &other.params)?.to_string_curried(None);
            let o_rhs = encode_region_as_stitch_expr(&other.rhs, &other.params)?.to_string_curried(None);
            let o_pre = encode_region_as_stitch_expr(&other.precondition, &other.params)?.to_string_curried(None);
            if lhs_e == o_lhs && rhs_e == o_rhs && pre_e == o_pre {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

fn count_stratum_calls_in_region(region: &Region, target: StratumId) -> usize {
    fn walk(r: RegionRef<'_>, target: StratumId) -> usize {
        match r.node {
            RegionNode::Block(span) => {
                let mut c = 0;
                for i in 0..span.len {
                    if let Some(stmt) = r.region.try_stmt(span, i) {
                        match stmt {
                            Stmt::Call { target: CallTarget::Stratum(id), .. } if id == target => {
                                c += 1;
                            }
                            Stmt::Region { region, .. } => {
                                if let Some(sub) = r.child(region) {
                                    c += walk(sub, target);
                                }
                            }
                            _ => {}
                        }
                    }
                }
                c
            }
            RegionNode::IfElse { then_region, else_region, .. } => {
                r.child(then_region).map(|s| walk(s, target)).unwrap_or(0)
                    + r.child(else_region).map(|s| walk(s, target)).unwrap_or(0)
            }
            RegionNode::BoundedLoop { body, .. } => {
                r.child(body).map(|s| walk(s, target)).unwrap_or(0)
            }
            RegionNode::InvariantLoop { cond, invariant_pred, fuel_measure, body, .. } => {
                r.child(cond).map(|s| walk(s, target)).unwrap_or(0)
                    + r.child(invariant_pred).map(|s| walk(s, target)).unwrap_or(0)
                    + r.child(fuel_measure).map(|s| walk(s, target)).unwrap_or(0)
                    + r.child(body).map(|s| walk(s, target)).unwrap_or(0)
            }
        }
    }
    walk(region.as_ref(), target)
}

fn collect_stratum_deps(region: &Region, out: &mut BTreeSet<u32>) {
    fn walk(r: RegionRef<'_>, out: &mut BTreeSet<u32>) {
        match r.node {
            RegionNode::Block(span) => {
                for i in 0..span.len {
                    if let Some(stmt) = r.region.try_stmt(span, i) {
                        match stmt {
                            Stmt::Call { target: CallTarget::Stratum(id), .. } => {
                                out.insert(id.0);
                            }
                            Stmt::Region { region, .. } => {
                                if let Some(sub) = r.child(region) {
                                    walk(sub, out);
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }
            RegionNode::IfElse { then_region, else_region, .. } => {
                if let Some(s) = r.child(then_region) {
                    walk(s, out);
                }
                if let Some(s) = r.child(else_region) {
                    walk(s, out);
                }
            }
            RegionNode::BoundedLoop { body, .. } => {
                if let Some(s) = r.child(body) {
                    walk(s, out);
                }
            }
            RegionNode::InvariantLoop { cond, invariant_pred, fuel_measure, body, .. } => {
                for id in [cond, invariant_pred, fuel_measure, body] {
                    if let Some(s) = r.child(id) {
                        walk(s, out);
                    }
                }
            }
        }
    }
    walk(region.as_ref(), out);
}

fn ty_str(ty: ValType) -> &'static str {
    match ty {
        ValType::I32 => "i32",
        ValType::I64 => "i64",
    }
}

fn width_tag(w: MemWidth) -> &'static str {
    match w {
        MemWidth::B1 => "b1",
        MemWidth::B2 => "b2",
        MemWidth::B4 => "b4",
        MemWidth::B8 => "b8",
    }
}

fn trap_tag(t: TrapCode) -> &'static str {
    match t {
        TrapCode::DivByZero => "trap.div_by_zero",
        TrapCode::IntOverflow => "trap.int_overflow",
        TrapCode::OutOfBoundsMem => "trap.oob_mem",
        TrapCode::OutOfFuel => "trap.out_of_fuel",
        TrapCode::HostContractViolation => "trap.host_contract",
        TrapCode::Unreachable => "trap.unreachable",
    }
}

fn unop_tag(u: UnOp) -> &'static str {
    match u {
        UnOp::I32Eqz => "i32.eqz",
        UnOp::I64Eqz => "i64.eqz",
        UnOp::I32Clz => "i32.clz",
        UnOp::I32Ctz => "i32.ctz",
        UnOp::I32Popcnt => "i32.popcnt",
        UnOp::I64Clz => "i64.clz",
        UnOp::I64Ctz => "i64.ctz",
        UnOp::I64Popcnt => "i64.popcnt",
        UnOp::I32WrapI64 => "i32.wrap_i64",
        UnOp::I64ExtendI32S => "i64.extend_i32_s",
        UnOp::I64ExtendI32U => "i64.extend_i32_u",
        UnOp::I32Extend8S => "i32.extend8_s",
        UnOp::I32Extend16S => "i32.extend16_s",
        UnOp::I64Extend8S => "i64.extend8_s",
        UnOp::I64Extend16S => "i64.extend16_s",
        UnOp::I64Extend32S => "i64.extend32_s",
    }
}

fn binop_tag(b: BinOp) -> &'static str {
    match b {
        BinOp::I32Eq => "i32.eq",
        BinOp::I32Ne => "i32.ne",
        BinOp::I32LtS => "i32.lt_s",
        BinOp::I32LtU => "i32.lt_u",
        BinOp::I32GtS => "i32.gt_s",
        BinOp::I32GtU => "i32.gt_u",
        BinOp::I32LeS => "i32.le_s",
        BinOp::I32LeU => "i32.le_u",
        BinOp::I32GeS => "i32.ge_s",
        BinOp::I32GeU => "i32.ge_u",
        BinOp::I64Eq => "i64.eq",
        BinOp::I64Ne => "i64.ne",
        BinOp::I64LtS => "i64.lt_s",
        BinOp::I64LtU => "i64.lt_u",
        BinOp::I64GtS => "i64.gt_s",
        BinOp::I64GtU => "i64.gt_u",
        BinOp::I64LeS => "i64.le_s",
        BinOp::I64LeU => "i64.le_u",
        BinOp::I64GeS => "i64.ge_s",
        BinOp::I64GeU => "i64.ge_u",
        BinOp::I32Add => "i32.add",
        BinOp::I32Sub => "i32.sub",
        BinOp::I32Mul => "i32.mul",
        BinOp::I32DivS => "i32.div_s",
        BinOp::I32DivU => "i32.div_u",
        BinOp::I32RemS => "i32.rem_s",
        BinOp::I32RemU => "i32.rem_u",
        BinOp::I64Add => "i64.add",
        BinOp::I64Sub => "i64.sub",
        BinOp::I64Mul => "i64.mul",
        BinOp::I64DivS => "i64.div_s",
        BinOp::I64DivU => "i64.div_u",
        BinOp::I64RemS => "i64.rem_s",
        BinOp::I64RemU => "i64.rem_u",
        BinOp::I32And => "i32.and",
        BinOp::I32Or => "i32.or",
        BinOp::I32Xor => "i32.xor",
        BinOp::I32Shl => "i32.shl",
        BinOp::I32ShrS => "i32.shr_s",
        BinOp::I32ShrU => "i32.shr_u",
        BinOp::I32Rotl => "i32.rotl",
        BinOp::I32Rotr => "i32.rotr",
        BinOp::I64And => "i64.and",
        BinOp::I64Or => "i64.or",
        BinOp::I64Xor => "i64.xor",
        BinOp::I64Shl => "i64.shl",
        BinOp::I64ShrS => "i64.shr_s",
        BinOp::I64ShrU => "i64.shr_u",
        BinOp::I64Rotl => "i64.rotl",
        BinOp::I64Rotr => "i64.rotr",
    }
}
