//! Unified stateful Gnomon verification & abstraction engine shared by CLI and MCP server.

use std::path::Path;
use std::time::Instant;

use gnomon_kernel::{
    BinOp, FuncDef, FuncId, HeapState, Law, LawKind, LawList, MemId, MemWidth, MemoryDef, Module,
    Op, Region, RegionBuilder, RegionNode, RegionRef, Stmt, Stratum, StratumId, StratumOp,
    StratumRegistry, TrapCode, UnOp, Val, ValId, ValType, eval_func, eval_region,
    split_invariant_loop, validate_read_only_with_registry,
};
use gnomon_sieve::{
    BitwuzlaNativeBackend, ConsolidationConfig, ConsolidationReport, EgglogSimplifier,
    EqSatConfig, SmtBackend, SmtModel, SmtResult, consolidate_registry,
    eqsat::count_region_nodes, render_autodoc,
};
use gnomon_wasm::{ExecOutcome, FuzzConfig, FuzzOutcome, emit_wasm, fuzz_equivalence};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::GnomonError;
use crate::ir_codec::{
    InputType, IrDocument, IrLawKind, IrModule, IrRegion, IrStratum, IrStratumOp, IrTrapCode,
    IrTypedVar, IrVal, IrValType, LoadedArtifact, find_entry_func,
};

/// Persistent JSON snapshot for CLI `--state` / MCP session durability.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct EngineSnapshot {
    pub next_stratum_id: u32,
    pub active_module: Option<IrModule>,
    pub candidates: Vec<IrStratumOp>,
    pub promoted: Vec<IrStratum>,
    pub verified_solutions: Vec<IrRegion>,
}

/// Core stateful session powering both the `gnomon` CLI and the single `gnomon` MCP server.
pub struct GnomonEngine {
    pub registry: StratumRegistry,
    pub active_module: Option<Module>,
    pub verified_solutions: Vec<Region>,
    pub next_stratum_id: u32,
}

impl Default for GnomonEngine {
    fn default() -> Self {
        Self::new()
    }
}

impl GnomonEngine {
    pub fn new() -> Self {
        Self {
            registry: StratumRegistry::new(),
            active_module: None,
            verified_solutions: Vec::new(),
            next_stratum_id: 1,
        }
    }

    pub fn load_state_file(path: &Path) -> Result<Self, GnomonError> {
        if !path.exists() {
            return Ok(Self::new());
        }
        let text = std::fs::read_to_string(path)
            .map_err(|e| GnomonError::Io(format!("failed reading state '{}': {e}", path.display())))?;
        if text.trim().is_empty() {
            return Ok(Self::new());
        }
        let snap: EngineSnapshot = serde_json::from_str(&text)
            .map_err(|e| GnomonError::InvalidInput(format!("invalid state JSON: {e}")))?;
        Self::from_snapshot(snap)
    }

    pub fn save_state_file(&self, path: &Path) -> Result<(), GnomonError> {
        if let Some(parent) = path.parent()
            && !parent.as_os_str().is_empty()
        {
            std::fs::create_dir_all(parent)
                .map_err(|e| GnomonError::Io(format!("failed creating state dir: {e}")))?;
        }
        let snap = self.to_snapshot();
        let json = serde_json::to_string_pretty(&snap)
            .map_err(|e| GnomonError::Internal(format!("serialize state failed: {e}")))?;
        std::fs::write(path, json)
            .map_err(|e| GnomonError::Io(format!("failed writing state '{}': {e}", path.display())))?;
        Ok(())
    }

    pub fn to_snapshot(&self) -> EngineSnapshot {
        let mut promoted: Vec<IrStratum> =
            self.registry.promoted().iter().map(IrStratum::from_kernel).collect();
        promoted.sort_by_key(|s| (s.op.layer, s.op.id));
        let mut candidates: Vec<IrStratumOp> =
            self.registry.candidates().iter().map(IrStratumOp::from_kernel).collect();
        candidates.sort_by_key(|c| (c.layer, c.id));
        EngineSnapshot {
            next_stratum_id: self.next_stratum_id,
            active_module: self.active_module.as_ref().map(IrModule::from_kernel),
            candidates,
            promoted,
            verified_solutions: self
                .verified_solutions
                .iter()
                .map(IrRegion::from_kernel)
                .collect(),
        }
    }

    pub fn from_snapshot(snap: EngineSnapshot) -> Result<Self, GnomonError> {
        let mut reg = StratumRegistry::new();
        let mut promoted = snap.promoted;
        promoted.sort_by_key(|s| (s.op.layer, s.op.id));
        let mut max_id = 0u32;
        for st in promoted {
            max_id = max_id.max(st.op.id);
            let kst = st.into_kernel()?;
            reg.promote_stratum(kst)
                .map_err(|e| GnomonError::Registry(format!("{e:?}")))?;
        }
        let mut candidates = snap.candidates;
        candidates.sort_by_key(|c| (c.layer, c.id));
        for c in candidates {
            max_id = max_id.max(c.id);
            let kop = c.into_kernel()?;
            reg.register_candidate_op(kop)
                .map_err(|e| GnomonError::Registry(format!("{e:?}")))?;
        }
        let active_module = snap.active_module.map(IrModule::into_kernel).transpose()?;
        let verified_solutions = snap
            .verified_solutions
            .into_iter()
            .map(IrRegion::into_kernel)
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Self {
            registry: reg,
            active_module,
            verified_solutions,
            next_stratum_id: snap.next_stratum_id.max(max_id + 1),
        })
    }

    // -----------------------------------------------------------------------
    // Tool 1: gnomon_lift_check
    // -----------------------------------------------------------------------
    pub fn lift_check(
        &mut self,
        detected_type: InputType,
        artifact: LoadedArtifact,
        include_ir: bool,
    ) -> Result<LiftCheckOutput, GnomonError> {
        match artifact {
            LoadedArtifact::Module(module) => {
                let mut diagnostics = Vec::new();
                let roundtrip_ok = match emit_wasm(&module) {
                    Ok(bytes) => {
                        diagnostics.push(format!("round-trip emit valid ({} wasm bytes)", bytes.len()));
                        true
                    }
                    Err(e) => {
                        diagnostics.push(format!("emit_wasm diagnostic: {e}"));
                        false
                    }
                };
                let functions: Vec<FuncSummary> = module
                    .funcs
                    .iter()
                    .map(|f| FuncSummary {
                        id: f.id.0,
                        name: f.name.clone(),
                        params: f
                            .params
                            .iter()
                            .map(|&(id, ty)| IrTypedVar { id: id.0, ty: ty.into() })
                            .collect(),
                        results: f.results.iter().copied().map(Into::into).collect(),
                        ssa_nodes: count_region_nodes(&f.body),
                        read_only: validate_read_only_with_registry(&f.body, &self.registry),
                    })
                    .collect();
                let ir_doc = if include_ir {
                    Some(IrDocument::from_module(&module))
                } else {
                    None
                };
                let memories = module.memories.len();
                let globals = module.globals.len();
                let host_contracts = module.host_contracts.len();
                self.active_module = Some(module);
                Ok(LiftCheckOutput {
                    input_type: detected_type,
                    artifact_kind: "module".into(),
                    memories,
                    globals,
                    host_contracts,
                    functions,
                    roundtrip_wasm_valid: Some(roundtrip_ok),
                    diagnostics,
                    ir: ir_doc,
                })
            }
            LoadedArtifact::Region { params, results, region } => {
                let ssa_nodes = count_region_nodes(&region);
                let ro = validate_read_only_with_registry(&region, &self.registry);
                let ir_doc = if include_ir {
                    Some(IrDocument::from_region(&params, &results, &region))
                } else {
                    None
                };
                let func_summary = FuncSummary {
                    id: 0,
                    name: "<region>".into(),
                    params: params
                        .iter()
                        .map(|&(id, ty)| IrTypedVar { id: id.0, ty: ty.into() })
                        .collect(),
                    results: results.iter().copied().map(Into::into).collect(),
                    ssa_nodes,
                    read_only: ro,
                };
                // Also wrap as a single-function active module so run_trace works seamlessly.
                self.active_module = Some(Module {
                    memories: Vec::new(),
                    globals: Vec::new(),
                    funcs: vec![FuncDef {
                        id: FuncId(0),
                        name: "entry".into(),
                        export_name: Some("entry".into()),
                        params,
                        results,
                        body: region,
                    }],
                    host_contracts: Vec::new(),
                    memory_exports: Vec::new(),
                    global_exports: Vec::new(),
                });
                Ok(LiftCheckOutput {
                    input_type: detected_type,
                    artifact_kind: "region".into(),
                    memories: 0,
                    globals: 0,
                    host_contracts: 0,
                    functions: vec![func_summary],
                    roundtrip_wasm_valid: None,
                    diagnostics: vec![format!("region loaded ({ssa_nodes} SSA nodes, read_only={ro})")],
                    ir: ir_doc,
                })
            }
        }
    }

    // -----------------------------------------------------------------------
    // Tool 2: gnomon_run_trace
    // -----------------------------------------------------------------------
    pub fn run_trace(
        &self,
        artifact_override: Option<LoadedArtifact>,
        entry: Option<&str>,
        inputs: &[IrVal],
        fuel: u64,
    ) -> Result<RunTraceOutput, GnomonError> {
        let k_inputs: Vec<Val> = inputs.iter().copied().map(Into::into).collect();

        match artifact_override {
            Some(LoadedArtifact::Region { params, results: _, region }) => {
                if params.len() != k_inputs.len() {
                    return Err(GnomonError::InvalidInput(format!(
                        "input arity mismatch: region expects {}, got {}",
                        params.len(),
                        k_inputs.len()
                    )));
                }
                let module = self.active_module.clone().unwrap_or_default();
                let init_heap = HeapState::from_module(&module, fuel)
                    .map_err(|t| GnomonError::Kernel(format!("heap init trap: {t:?}")))?;
                let bindings: Vec<(ValId, Val)> = params
                    .iter()
                    .zip(k_inputs.iter())
                    .map(|(&(vid, _), &val)| (vid, val))
                    .collect();
                let res = eval_region(&module, &self.registry, &region, &bindings, init_heap.clone());
                Ok(build_trace_output("<region>", fuel, &init_heap, res))
            }
            Some(LoadedArtifact::Module(module)) => {
                let func = find_entry_func(&module, entry)?;
                let init_heap = HeapState::from_module(&module, fuel)
                    .map_err(|t| GnomonError::Kernel(format!("heap init trap: {t:?}")))?;
                let res = eval_func(&module, &self.registry, func.id, &k_inputs, init_heap.clone());
                Ok(build_trace_output(&func.name, fuel, &init_heap, res))
            }
            None => {
                let module = self.active_module.as_ref().ok_or_else(|| {
                    GnomonError::InvalidInput(
                        "no module loaded; call gnomon_lift_check or provide an input artifact".into(),
                    )
                })?;
                let func = find_entry_func(module, entry)?;
                let init_heap = HeapState::from_module(module, fuel)
                    .map_err(|t| GnomonError::Kernel(format!("heap init trap: {t:?}")))?;
                let res = eval_func(module, &self.registry, func.id, &k_inputs, init_heap.clone());
                Ok(build_trace_output(&func.name, fuel, &init_heap, res))
            }
        }
    }

    // -----------------------------------------------------------------------
    // Tool 3: gnomon_define_op
    // -----------------------------------------------------------------------
    #[allow(clippy::too_many_arguments)]
    pub fn define_op(
        &mut self,
        name: String,
        layer: u16,
        params: Vec<IrTypedVar>,
        results: Vec<IrValType>,
        body: Region,
        docstring: String,
        explicit_id: Option<u32>,
    ) -> Result<DefineOpOutput, GnomonError> {
        if self.registry.promoted().iter().any(|s| s.op.name == name)
            || self.registry.candidates().iter().any(|c| c.name == name)
        {
            return Err(GnomonError::Registry(format!(
                "duplicate stratum op name '{name}'"
            )));
        }
        let id = explicit_id.unwrap_or_else(|| {
            let id = self.next_stratum_id;
            self.next_stratum_id += 1;
            id
        });
        if id >= self.next_stratum_id {
            self.next_stratum_id = id + 1;
        }
        let op = StratumOp {
            id: StratumId(id),
            name: name.clone(),
            layer,
            params: params.into_iter().map(|v| (ValId(v.id), v.ty.into())).collect(),
            results: results.into_iter().map(Into::into).collect(),
            body,
            docstring,
        };
        let ssa_nodes = count_region_nodes(&op.body);
        self.registry
            .register_candidate_op(op)
            .map_err(|e| GnomonError::Registry(format!("{e:?}")))?;
        let read_only = self.registry.is_stratum_read_only(StratumId(id));
        Ok(DefineOpOutput {
            stratum_id: id,
            name,
            layer,
            ssa_nodes,
            read_only,
            status: "CANDIDATE_REGISTERED".into(),
        })
    }

    // -----------------------------------------------------------------------
    // Tool 4: gnomon_prove_law (3-stage sieve: wasmtime -> Bitwuzla -> kernel)
    // -----------------------------------------------------------------------
    #[allow(clippy::too_many_arguments)]
    pub fn prove_law(
        &mut self,
        op_selector: &str,
        law_name: String,
        kind: IrLawKind,
        params: Vec<IrTypedVar>,
        lhs: Region,
        rhs: Region,
        precondition: Option<Region>,
    ) -> Result<ProveLawOutput, GnomonError> {
        let start = Instant::now();
        let target_op = self.resolve_op(op_selector)?;
        let sid = target_op.id;

        if let Some(existing) = self.registry.get_stratum(sid)
            && existing.laws.iter().any(|l| l.name == law_name)
        {
            return Err(GnomonError::Registry(format!(
                "duplicate law name '{law_name}' on stratum '{}'",
                target_op.name
            )));
        }

        let k_params: Vec<(ValId, ValType)> =
            params.iter().map(|v| (ValId(v.id), v.ty.into())).collect();
        let k_kind = match kind {
            IrLawKind::Algebraic => LawKind::Algebraic,
            IrLawKind::MemoryFrame { untouched_mem } => {
                LawKind::MemoryFrame { untouched_mem: MemId(untouched_mem) }
            }
        };
        let pre_region = precondition.unwrap_or_else(Region::empty);

        // Build a scratch registry that includes `target_op` as a promoted anchor so
        // `lower_region_to_layer0` and `Bitwuzla` can expand calls to `target_op` even before
        // `target_op` has been promoted!
        let scratch_reg = self.registry_with_candidate_as_anchor(&target_op)?;

        if pre_region != Region::empty()
            && !validate_read_only_with_registry(&pre_region, &scratch_reg)
        {
            return Err(GnomonError::Registry(
                "law precondition region must be read-only".into(),
            ));
        }

        // For MemoryFrame laws, `eqsat.rs` installs an unconditional frame rule for
        // `CallHeap(target_op.id, ...)`, so:
        // 1. Preconditions must be empty (unconditional frame non-interference).
        // 2. Stage-2 MUST prove directly on `target_op.body` (over all `target_op.params`),
        //    preventing an attacker from passing an unrelated/empty `lhs` to smuggle a bogus
        //    frame law onto a mutating op!
        // 3. When storing the admitted `Law`, default omitted `rhs` to `lhs.clone()` so
        //    `lhs_tys == rhs_tys` holds for value-returning ops in `gnomon-kernel`.
        if matches!(k_kind, LawKind::MemoryFrame { .. }) && pre_region != Region::empty() {
            return Err(GnomonError::Registry(
                "memory_frame laws must be unconditional (no precondition)".into(),
            ));
        }

        let stored_rhs = if matches!(k_kind, LawKind::MemoryFrame { .. }) && rhs == Region::empty()
        {
            lhs.clone()
        } else {
            rhs
        };

        // Prepare effective (lhs, rhs, pre) regions to prove:
        // - Algebraic: lhs == rhs (under precondition)
        // - MemoryFrame { untouched_mem }: reading MemorySize + any in-bounds symbolic byte of
        //   untouched_mem after executing `target_op.body` equals reading them before.
        let base_module = self.module_for_regions(&lhs, &stored_rhs, k_kind);
        let (check_lhs, check_rhs, check_pre, check_params) = match k_kind {
            LawKind::Algebraic => {
                (lhs.clone(), stored_rhs.clone(), pre_region.clone(), k_params.clone())
            }
            LawKind::MemoryFrame { untouched_mem } => build_memory_frame_probes(
                &target_op.body,
                &pre_region,
                &target_op.params,
                &target_op.results,
                untouched_mem,
            ),
        };

        // --- Stage 1: Fast Wasmtime JIT falsification (when unconditional & Wasm-emittable) ---
        if check_pre == Region::empty()
            && matches!(k_kind, LawKind::Algebraic)
            && let Some(cex) = run_stage1_wasm_fuzz(
                &base_module,
                &scratch_reg,
                &check_params,
                &check_lhs,
                &check_rhs,
            )?
        {
            return Ok(ProveLawOutput {
                status: "FALSIFIED".into(),
                stage: "stage1_wasmtime_fuzz".into(),
                stratum_id: sid.0,
                law_name,
                proof_digest_hex: None,
                elapsed_ms: start.elapsed().as_secs_f64() * 1000.0,
                counterexample: Some(cex),
                detail: "counterexample found by Stage-1 Wasmtime JIT fuzzer".into(),
            });
        }

        // --- Stage 2: Exact Bitwuzla QF_ABV proof ---
        let mut backend = BitwuzlaNativeBackend::with_time_limit_ms(10_000);
        let pre_opt = if check_pre == Region::empty() { None } else { Some(&check_pre) };
        let smt_res = backend
            .check_equivalence(&base_module, &scratch_reg, &check_lhs, &check_rhs, pre_opt)
            .map_err(|e| GnomonError::Sieve(e.to_string()))?;

        match smt_res {
            SmtResult::Sat(model) => {
                let cex = model_to_counterexample(
                    &base_module,
                    &scratch_reg,
                    &check_params,
                    &check_lhs,
                    &check_rhs,
                    &model,
                );
                return Ok(ProveLawOutput {
                    status: "FALSIFIED".into(),
                    stage: "stage2_bitwuzla_smt".into(),
                    stratum_id: sid.0,
                    law_name,
                    proof_digest_hex: None,
                    elapsed_ms: start.elapsed().as_secs_f64() * 1000.0,
                    counterexample: Some(cex),
                    detail: "counterexample found by Stage-2 Bitwuzla QF_ABV oracle".into(),
                });
            }
            SmtResult::Unknown(reason) => {
                return Ok(ProveLawOutput {
                    status: "UNKNOWN".into(),
                    stage: "stage2_bitwuzla_smt".into(),
                    stratum_id: sid.0,
                    law_name,
                    proof_digest_hex: None,
                    elapsed_ms: start.elapsed().as_secs_f64() * 1000.0,
                    counterexample: None,
                    detail: format!("Bitwuzla returned unknown: {reason}"),
                });
            }
            SmtResult::Unsat => {}
        }

        // --- Stage 3: TCB SHA-256 digest & gnomon-kernel StratumRegistry admission ---
        let digest = compute_law_digest(
            sid,
            &law_name,
            k_kind,
            &k_params,
            &pre_region,
            &lhs,
            &stored_rhs,
        );
        let law = Law {
            name: law_name.clone(),
            kind: k_kind,
            params: k_params,
            precondition: pre_region,
            lhs,
            rhs: stored_rhs,
            proof_digest: digest,
        };
        self.admit_proved_law(target_op, law)?;
        let digest_hex = hex_encode(&digest);

        Ok(ProveLawOutput {
            status: "PROVED".into(),
            stage: "stage3_kernel_admitted".into(),
            stratum_id: sid.0,
            law_name,
            proof_digest_hex: Some(digest_hex),
            elapsed_ms: start.elapsed().as_secs_f64() * 1000.0,
            counterexample: None,
            detail: "proved by Bitwuzla QF_ABV and admitted by gnomon-kernel TCB".into(),
        })
    }

    // -----------------------------------------------------------------------
    // Tool 5: gnomon_check_goal (egglog Strata cancellation + Bitwuzla QF_ABV)
    // -----------------------------------------------------------------------
    #[allow(clippy::too_many_arguments)]
    pub fn check_goal(
        &mut self,
        candidate: Region,
        spec: Region,
        params: Vec<IrTypedVar>,
        precondition: Option<Region>,
        loop_postcondition: Option<Region>,
        timeout_ms: u64,
    ) -> Result<CheckGoalOutput, GnomonError> {
        let start = Instant::now();
        let k_params: Vec<(ValId, ValType)> =
            params.iter().map(|v| (ValId(v.id), v.ty.into())).collect();
        let module = self.module_for_regions(&candidate, &spec, LawKind::Algebraic);
        let eqsat = EgglogSimplifier::new(EqSatConfig {
            max_iters: 5,
            max_nodes: 5_000,
            timeout_ms: timeout_ms.min(5_000),
        });

        // Case A: InvariantLoop VC splitting via frozen gnomon-kernel TCB!
        if matches!(candidate.root, RegionNode::InvariantLoop { .. }) {
            let post = loop_postcondition.unwrap_or_else(|| spec.clone());
            let vcs = split_invariant_loop(k_params.clone(), precondition.clone(), &candidate, post)
                .map_err(|e| GnomonError::Kernel(format!("VC splitter rejected loop: {e:?}")))?;
            let mut backend = BitwuzlaNativeBackend::with_time_limit_ms(timeout_ms.max(100));
            let mut vc_statuses = Vec::new();
            let mut all_laws_fired = Vec::new();
            for (label, vc) in [
                ("init", vcs.init),
                ("preservation", vcs.preservation),
                ("exit", vcs.exit),
            ] {
                let (simp_goal, rep) = eqsat
                    .simplify_region(&vc.goal, &self.registry)
                    .map_err(|e| GnomonError::Sieve(e.to_string()))?;
                all_laws_fired.extend(rep.laws_fired);
                let mut simp_vc = vc;
                simp_vc.goal = simp_goal;
                let res = backend
                    .check_vc(&module, &self.registry, &simp_vc)
                    .map_err(|e| GnomonError::Sieve(e.to_string()))?;
                match res {
                    SmtResult::Unsat => vc_statuses.push(format!("{label}:PROVED")),
                    SmtResult::Sat(model) => {
                        return Ok(CheckGoalOutput {
                            status: "FALSIFIED".into(),
                            laws_fired: all_laws_fired,
                            nodes_before: count_region_nodes(&candidate),
                            nodes_after: count_region_nodes(&candidate),
                            vc_results: vc_statuses,
                            elapsed_ms: start.elapsed().as_secs_f64() * 1000.0,
                            counterexample: Some(CounterexampleJson {
                                inputs: model
                                    .scalar_values
                                    .iter()
                                    .map(|&(id, v)| (id.0, v.into()))
                                    .collect(),
                                lhs_outcome: format!("vc_{label}_violated"),
                                rhs_outcome: "expected_holds".into(),
                            }),
                            detail: format!("InvariantLoop VC '{label}' violated"),
                        });
                    }
                    SmtResult::Unknown(r) => {
                        return Ok(CheckGoalOutput {
                            status: "UNKNOWN".into(),
                            laws_fired: all_laws_fired,
                            nodes_before: count_region_nodes(&candidate),
                            nodes_after: count_region_nodes(&candidate),
                            vc_results: vc_statuses,
                            elapsed_ms: start.elapsed().as_secs_f64() * 1000.0,
                            counterexample: None,
                            detail: format!("InvariantLoop VC '{label}' unknown: {r}"),
                        });
                    }
                }
            }
            self.verified_solutions.push(candidate.clone());
            dedup_preserve_order(&mut all_laws_fired);
            return Ok(CheckGoalOutput {
                status: "PROVED".into(),
                laws_fired: all_laws_fired,
                nodes_before: count_region_nodes(&candidate),
                nodes_after: count_region_nodes(&candidate),
                vc_results: vc_statuses,
                elapsed_ms: start.elapsed().as_secs_f64() * 1000.0,
                counterexample: None,
                detail: "all 3 InvariantLoop VCs (init, preservation, exit) proved".into(),
            });
        }

        // Case B: Bounded egglog cancellation using proved Strata laws + residual Bitwuzla QF_ABV!
        let (simp_cand, rep_cand) = eqsat
            .simplify_region(&candidate, &self.registry)
            .map_err(|e| GnomonError::Sieve(e.to_string()))?;
        let (simp_spec, rep_spec) = eqsat
            .simplify_region(&spec, &self.registry)
            .map_err(|e| GnomonError::Sieve(e.to_string()))?;
        let mut laws_fired = rep_cand.laws_fired;
        laws_fired.extend(rep_spec.laws_fired);
        dedup_preserve_order(&mut laws_fired);

        let nodes_before = rep_cand.nodes_before + rep_spec.nodes_before;
        let nodes_after = rep_cand.nodes_after + rep_spec.nodes_after;

        let mut backend = BitwuzlaNativeBackend::with_time_limit_ms(timeout_ms.max(100));
        let pre_ref = precondition.as_ref().filter(|p| **p != Region::empty());
        let smt_res = backend
            .check_equivalence(&module, &self.registry, &simp_cand, &simp_spec, pre_ref)
            .map_err(|e| GnomonError::Sieve(e.to_string()))?;

        match smt_res {
            SmtResult::Unsat => {
                self.verified_solutions.push(candidate);
                Ok(CheckGoalOutput {
                    status: "PROVED".into(),
                    laws_fired,
                    nodes_before,
                    nodes_after,
                    vc_results: Vec::new(),
                    elapsed_ms: start.elapsed().as_secs_f64() * 1000.0,
                    counterexample: None,
                    detail: "goal proved equivalent by egglog + Bitwuzla QF_ABV".into(),
                })
            }
            SmtResult::Sat(model) => {
                let cex = model_to_counterexample(
                    &module,
                    &self.registry,
                    &k_params,
                    &candidate,
                    &spec,
                    &model,
                );
                Ok(CheckGoalOutput {
                    status: "FALSIFIED".into(),
                    laws_fired,
                    nodes_before,
                    nodes_after,
                    vc_results: Vec::new(),
                    elapsed_ms: start.elapsed().as_secs_f64() * 1000.0,
                    counterexample: Some(cex),
                    detail: "goal falsified by Bitwuzla QF_ABV".into(),
                })
            }
            SmtResult::Unknown(reason) => Ok(CheckGoalOutput {
                status: "UNKNOWN".into(),
                laws_fired,
                nodes_before,
                nodes_after,
                vc_results: Vec::new(),
                elapsed_ms: start.elapsed().as_secs_f64() * 1000.0,
                counterexample: None,
                detail: format!("Bitwuzla returned unknown: {reason}"),
            }),
        }
    }

    // -----------------------------------------------------------------------
    // Tool 6: gnomon_consolidate (stitch_core MDL + egglog non-redundancy)
    // -----------------------------------------------------------------------
    pub fn consolidate(
        &mut self,
        extra_solutions: &[Region],
        cfg: &ConsolidationConfig,
    ) -> Result<ConsolidationReport, GnomonError> {
        let mut all_solutions = self.verified_solutions.clone();
        all_solutions.extend(extra_solutions.iter().cloned());
        let (rebuilt, report) = consolidate_registry(&self.registry, &all_solutions, cfg)
            .map_err(|e| GnomonError::Sieve(e.to_string()))?;
        // Preserve any unpromoted candidates alongside the newly rebuilt promoted Strata.
        let candidates: Vec<StratumOp> = self.registry.candidates().to_vec();
        let mut final_reg = rebuilt;
        for c in candidates {
            let _ = final_reg.register_candidate_op(c);
        }
        self.registry = final_reg;
        self.verified_solutions = all_solutions;
        Ok(report)
    }

    pub fn autodoc(&self) -> (String, serde_json::Value) {
        render_autodoc(&self.registry)
    }

    // -----------------------------------------------------------------------
    // Internal helpers
    // -----------------------------------------------------------------------
    fn resolve_op(&self, selector: &str) -> Result<StratumOp, GnomonError> {
        if let Ok(id_num) = selector.parse::<u32>()
            && let Some(op) = self.registry.get_op(StratumId(id_num))
        {
            return Ok(op.clone());
        }
        for st in self.registry.promoted() {
            if st.op.name == selector {
                return Ok(st.op.clone());
            }
        }
        for c in self.registry.candidates() {
            if c.name == selector {
                return Ok(c.clone());
            }
        }
        Err(GnomonError::InvalidInput(format!(
            "stratum op '{selector}' not found in candidates or promoted registry"
        )))
    }

    fn registry_with_candidate_as_anchor(&self, target: &StratumOp) -> Result<StratumRegistry, GnomonError> {
        if self.registry.get_stratum(target.id).is_some() {
            return Ok(self.registry.clone());
        }
        let mut reg = StratumRegistry::new();
        let mut promoted: Vec<Stratum> = self.registry.promoted().to_vec();
        promoted.push(Stratum {
            op: target.clone(),
            laws: LawList::single(Law {
                name: format!("__prove_anchor_{}", target.id.0),
                kind: LawKind::Algebraic,
                params: Vec::new(),
                precondition: Region::empty(),
                lhs: Region::empty(),
                rhs: Region::empty(),
                proof_digest: [0xee; 32],
            }),
        });
        promoted.sort_by_key(|s| (s.op.layer, s.op.id.0));
        for st in promoted {
            reg.promote_stratum(st)
                .map_err(|e| GnomonError::Registry(format!("{e:?}")))?;
        }
        Ok(reg)
    }

    fn admit_proved_law(&mut self, op: StratumOp, new_law: Law) -> Result<(), GnomonError> {
        if self.registry.get_stratum(op.id).is_none() {
            self.registry
                .promote_stratum(Stratum { op, laws: LawList::single(new_law) })
                .map_err(|e| GnomonError::Registry(format!("{e:?}")))?;
            return Ok(());
        }
        // Adding an additional proved law to an already-promoted Stratum:
        // rebuild a clean StratumRegistry in ascending layer order so gnomon-kernel
        // re-verifies every Stratum via promote_stratum.
        let mut promoted: Vec<Stratum> = self.registry.promoted().to_vec();
        for st in &mut promoted {
            if st.op.id == op.id {
                st.laws.push(new_law.clone());
            }
        }
        promoted.sort_by_key(|s| (s.op.layer, s.op.id.0));
        let candidates: Vec<StratumOp> = self.registry.candidates().to_vec();

        let mut rebuilt = StratumRegistry::new();
        for st in promoted {
            rebuilt
                .promote_stratum(st)
                .map_err(|e| GnomonError::Registry(format!("{e:?}")))?;
        }
        for c in candidates {
            rebuilt
                .register_candidate_op(c)
                .map_err(|e| GnomonError::Registry(format!("{e:?}")))?;
        }
        self.registry = rebuilt;
        Ok(())
    }

    fn module_for_regions(&self, lhs: &Region, rhs: &Region, kind: LawKind) -> Module {
        let mut m = self.active_module.clone().unwrap_or_default();
        let mut max_mem: Option<u16> = match kind {
            LawKind::MemoryFrame { untouched_mem } => Some(untouched_mem.0),
            LawKind::Algebraic => None,
        };
        for reg in [lhs, rhs] {
            if let Some(mx) = max_mem_id_in_region(reg) {
                max_mem = Some(max_mem.map_or(mx, |cur| cur.max(mx)));
            }
        }
        for st in self.registry.promoted() {
            if let Some(mx) = max_mem_id_in_region(&st.op.body) {
                max_mem = Some(max_mem.map_or(mx, |cur| cur.max(mx)));
            }
        }
        if let Some(mx) = max_mem {
            for id in 0..=mx {
                if !m.memories.iter().any(|mem| mem.id == MemId(id)) {
                    m.memories.push(MemoryDef {
                        id: MemId(id),
                        min_pages: 1,
                        max_pages: Some(1),
                        init_data: Vec::new(),
                    });
                }
            }
        }
        m
    }
}

// ===========================================================================
// Output DTOs (shared between CLI JSON and MCP structured JSON)
// ===========================================================================

#[derive(Clone, Debug, Serialize, Deserialize, schemars::JsonSchema)]
pub struct FuncSummary {
    pub id: u32,
    pub name: String,
    pub params: Vec<IrTypedVar>,
    pub results: Vec<IrValType>,
    pub ssa_nodes: usize,
    pub read_only: bool,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct LiftCheckOutput {
    pub input_type: InputType,
    pub artifact_kind: String,
    pub memories: usize,
    pub globals: usize,
    pub host_contracts: usize,
    pub functions: Vec<FuncSummary>,
    pub roundtrip_wasm_valid: Option<bool>,
    pub diagnostics: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub ir: Option<IrDocument>,
}

#[derive(Clone, Debug, Serialize, Deserialize, schemars::JsonSchema)]
pub struct MemoryDiffEntry {
    pub mem_id: u16,
    pub offset: u32,
    pub before: u8,
    pub after: u8,
}

#[derive(Clone, Debug, Serialize, Deserialize, schemars::JsonSchema)]
pub struct RunTraceOutput {
    pub entry: String,
    pub status: String,
    pub outputs: Vec<IrVal>,
    pub trap: Option<IrTrapCode>,
    pub fuel_budget: u64,
    pub fuel_consumed: Option<u64>,
    pub memory_diff: Vec<MemoryDiffEntry>,
}

#[derive(Clone, Debug, Serialize, Deserialize, schemars::JsonSchema)]
pub struct DefineOpOutput {
    pub stratum_id: u32,
    pub name: String,
    pub layer: u16,
    pub ssa_nodes: usize,
    pub read_only: bool,
    pub status: String,
}

#[derive(Clone, Debug, Serialize, Deserialize, schemars::JsonSchema)]
pub struct CounterexampleJson {
    pub inputs: Vec<(u32, IrVal)>,
    pub lhs_outcome: String,
    pub rhs_outcome: String,
}

#[derive(Clone, Debug, Serialize, Deserialize, schemars::JsonSchema)]
pub struct ProveLawOutput {
    pub status: String,
    pub stage: String,
    pub stratum_id: u32,
    pub law_name: String,
    pub proof_digest_hex: Option<String>,
    pub elapsed_ms: f64,
    pub counterexample: Option<CounterexampleJson>,
    pub detail: String,
}

#[derive(Clone, Debug, Serialize, Deserialize, schemars::JsonSchema)]
pub struct CheckGoalOutput {
    pub status: String,
    pub laws_fired: Vec<String>,
    pub nodes_before: usize,
    pub nodes_after: usize,
    pub vc_results: Vec<String>,
    pub elapsed_ms: f64,
    pub counterexample: Option<CounterexampleJson>,
    pub detail: String,
}

// ===========================================================================
// Stage-1 Fuzz, MemoryFrame Probes, Digest, and Trace Helpers
// ===========================================================================

fn build_trace_output(
    entry: &str,
    fuel_budget: u64,
    init_heap: &HeapState,
    res: Result<(Vec<Val>, HeapState), TrapCode>,
) -> RunTraceOutput {
    match res {
        Ok((vals, final_heap)) => {
            let fuel_consumed = fuel_budget.saturating_sub(final_heap.fuel_remaining);
            let memory_diff = compute_memory_diff(init_heap, &final_heap);
            RunTraceOutput {
                entry: entry.into(),
                status: "OK".into(),
                outputs: vals.into_iter().map(Into::into).collect(),
                trap: None,
                fuel_budget,
                fuel_consumed: Some(fuel_consumed),
                memory_diff,
            }
        }
        Err(trap) => RunTraceOutput {
            entry: entry.into(),
            status: "TRAP".into(),
            outputs: Vec::new(),
            trap: Some(trap.into()),
            fuel_budget,
            fuel_consumed: if matches!(trap, TrapCode::OutOfFuel) {
                Some(fuel_budget)
            } else {
                None
            },
            memory_diff: Vec::new(),
        },
    }
}

fn compute_memory_diff(before: &HeapState, after: &HeapState) -> Vec<MemoryDiffEntry> {
    let mut diffs = Vec::new();
    for (idx, after_mem) in after.memories.iter().enumerate() {
        let before_bytes = before
            .memories
            .get(idx)
            .map(|m| m.bytes.as_slice())
            .unwrap_or(&[]);
        for (off, &ab) in after_mem.bytes.iter().enumerate() {
            let bb = before_bytes.get(off).copied().unwrap_or(0);
            if ab != bb {
                diffs.push(MemoryDiffEntry {
                    mem_id: idx as u16,
                    offset: off as u32,
                    before: bb,
                    after: ab,
                });
                if diffs.len() >= 256 {
                    return diffs;
                }
            }
        }
    }
    diffs
}

fn run_stage1_wasm_fuzz(
    base_module: &Module,
    registry: &StratumRegistry,
    params: &[(ValId, ValType)],
    lhs: &Region,
    rhs: &Region,
) -> Result<Option<CounterexampleJson>, GnomonError> {
    if !base_module.host_contracts.is_empty() {
        return Ok(None);
    }
    let mut next_val = params.iter().map(|(v, _)| v.0 + 1).max().unwrap_or(0);
    let Ok(lhs_l0) = registry.lower_region_to_layer0(lhs, &mut next_val) else {
        return Ok(None);
    };
    let Ok(rhs_l0) = registry.lower_region_to_layer0(rhs, &mut next_val) else {
        return Ok(None);
    };
    let results = infer_yield_types(&lhs_l0, params);
    let mut m_lhs = base_module.clone();
    m_lhs.funcs = vec![FuncDef {
        id: FuncId(0),
        name: "entry".into(),
        export_name: Some("entry".into()),
        params: params.to_vec(),
        results: results.clone(),
        body: lhs_l0,
    }];
    let mut m_rhs = base_module.clone();
    m_rhs.funcs = vec![FuncDef {
        id: FuncId(0),
        name: "entry".into(),
        export_name: Some("entry".into()),
        params: params.to_vec(),
        results,
        body: rhs_l0,
    }];
    let (Ok(w_lhs), Ok(w_rhs)) = (emit_wasm(&m_lhs), emit_wasm(&m_rhs)) else {
        return Ok(None);
    };
    let cfg = FuzzConfig {
        total_vectors: 10_000,
        fuel_per_run: 50_000,
        seed: 0x5EED_9E37_79B9_7F4A,
    };
    match fuzz_equivalence(&w_lhs, &w_rhs, FuncId(0), &cfg) {
        Ok(FuzzOutcome::Falsified(cex)) => Ok(Some(CounterexampleJson {
            inputs: params
                .iter()
                .zip(cex.inputs.iter())
                .map(|(&(vid, _), &val)| (vid.0, val.into()))
                .collect(),
            lhs_outcome: format_exec_outcome(&cex.lhs_outcome),
            rhs_outcome: format_exec_outcome(&cex.rhs_outcome),
        })),
        Ok(FuzzOutcome::NoCounterexample { .. }) | Err(_) => Ok(None),
    }
}

fn format_exec_outcome(o: &ExecOutcome) -> String {
    match o {
        ExecOutcome::Values(vs) => format!("{vs:?}"),
        ExecOutcome::Trap(t) => format!("Trap({t:?})"),
    }
}

fn model_to_counterexample(
    module: &Module,
    registry: &StratumRegistry,
    params: &[(ValId, ValType)],
    lhs: &Region,
    rhs: &Region,
    model: &SmtModel,
) -> CounterexampleJson {
    let mut bindings: Vec<(ValId, Val)> = Vec::new();
    for &(vid, ty) in params {
        let val = model
            .scalar_values
            .iter()
            .find(|(id, _)| *id == vid)
            .map(|(_, v)| *v)
            .unwrap_or(match ty {
                ValType::I32 => Val::I32(0),
                ValType::I64 => Val::I64(0),
            });
        bindings.push((vid, val));
    }
    for &(vid, val) in &model.scalar_values {
        if !bindings.iter().any(|(id, _)| *id == vid) {
            bindings.push((vid, val));
        }
    }
    let mut heap = HeapState::from_module(module, 100_000).unwrap_or(HeapState {
        memories: Vec::new(),
        globals: Vec::new(),
        fuel_remaining: 100_000,
    });
    for (mem_id, bytes) in &model.memory_bytes {
        if let Some(mem) = heap.memories.get_mut(mem_id.0 as usize) {
            for &(off, b) in bytes {
                if (off as usize) < mem.bytes.len() {
                    mem.bytes[off as usize] = b;
                }
            }
        }
    }
    let lhs_out = match eval_region(module, registry, lhs, &bindings, heap.clone()) {
        Ok((vs, _)) => format!("{vs:?}"),
        Err(t) => format!("Trap({t:?})"),
    };
    let rhs_out = match eval_region(module, registry, rhs, &bindings, heap) {
        Ok((vs, _)) => format!("{vs:?}"),
        Err(t) => format!("Trap({t:?})"),
    };
    CounterexampleJson {
        inputs: bindings.into_iter().map(|(id, v)| (id.0, v.into())).collect(),
        lhs_outcome: lhs_out,
        rhs_outcome: rhs_out,
    }
}

fn build_memory_frame_probes(
    op_body: &Region,
    existing_pre: &Region,
    params: &[(ValId, ValType)],
    results: &[ValType],
    untouched_mem: MemId,
) -> (Region, Region, Region, Vec<(ValId, ValType)>) {
    let max_id = max_val_in_region(op_body)
        .max(max_val_in_region(existing_pre))
        .max(params.iter().map(|(v, _)| v.0).max().unwrap_or(0));
    let mut next_id = max_id + 1;
    let mut fresh = || {
        let id = ValId(next_id);
        next_id += 1;
        id
    };

    let probe_addr = fresh();
    let sz_val = fresh();
    let byte_val = fresh();
    let lhs_res_vars: Vec<(ValId, ValType)> =
        results.iter().copied().map(|ty| (fresh(), ty)).collect();

    let mut ext_params = params.to_vec();
    ext_params.push((probe_addr, ValType::I32));

    let load_op = Op::Load {
        mem: untouched_mem,
        addr: probe_addr,
        offset: 0,
        width: MemWidth::B1,
        signed: false,
        result_ty: ValType::I32,
    };

    // Guard probe_addr strictly in-bounds of untouched_mem (using u64 arithmetic to prevent
    // 32-bit page-size multiplication overflow) so `b_before`'s Load can NEVER introduce a
    // spurious OutOfBoundsMem trap before a trapping `lhs`.
    let pre_sz_pages = fresh();
    let pre_sz_u64 = fresh();
    let pre_page_bytes = fresh();
    let pre_byte_len = fresh();
    let pre_addr_u64 = fresh();
    let pre_in_bounds = fresh();
    let mut pre_b = RegionBuilder::new();
    pre_b.push_let(pre_sz_pages, ValType::I32, Op::MemorySize(untouched_mem));
    pre_b.push_let(pre_sz_u64, ValType::I64, Op::Un(UnOp::I64ExtendI32U, pre_sz_pages));
    pre_b.push_let(pre_page_bytes, ValType::I64, Op::ConstI64(65_536));
    pre_b.push_let(pre_byte_len, ValType::I64, Op::Bin(BinOp::I64Mul, pre_sz_u64, pre_page_bytes));
    pre_b.push_let(pre_addr_u64, ValType::I64, Op::Un(UnOp::I64ExtendI32U, probe_addr));
    pre_b.push_let(
        pre_in_bounds,
        ValType::I32,
        Op::Bin(BinOp::I64LtU, pre_addr_u64, pre_byte_len),
    );
    if *existing_pre != Region::empty() {
        let ex_raw = fresh();
        let zero = fresh();
        let ex_bool = fresh();
        let combined = fresh();
        pre_b.push_subregion(&[(ex_raw, ValType::I32)], existing_pre);
        pre_b.push_let(zero, ValType::I32, Op::ConstI32(0));
        pre_b.push_let(ex_bool, ValType::I32, Op::Bin(BinOp::I32Ne, ex_raw, zero));
        pre_b.push_let(combined, ValType::I32, Op::Bin(BinOp::I32And, ex_bool, pre_in_bounds));
        pre_b.push_yield(&[combined]);
    } else {
        pre_b.push_yield(&[pre_in_bounds]);
    }

    // Both probes verify BOTH memory size (catching memory.grow on untouched_mem) and
    // arbitrary byte content at `probe_addr` (catching store/fill/copy on untouched_mem),
    // while preserving `op_body`'s exact result arity and trap behavior!
    let mut b_after = RegionBuilder::new();
    b_after.push_subregion(&lhs_res_vars, op_body);
    b_after.push_let(sz_val, ValType::I32, Op::MemorySize(untouched_mem));
    b_after.push_let(byte_val, ValType::I32, load_op);
    b_after.push_yield(&[sz_val, byte_val]);

    let mut b_before = RegionBuilder::new();
    b_before.push_let(sz_val, ValType::I32, Op::MemorySize(untouched_mem));
    b_before.push_let(byte_val, ValType::I32, load_op);
    b_before.push_subregion(&lhs_res_vars, op_body);
    b_before.push_yield(&[sz_val, byte_val]);

    (b_after.finish(), b_before.finish(), pre_b.finish(), ext_params)
}

fn compute_law_digest(
    sid: StratumId,
    law_name: &str,
    kind: LawKind,
    params: &[(ValId, ValType)],
    pre: &Region,
    lhs: &Region,
    rhs: &Region,
) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"gnomon-law-v1:");
    hasher.update(sid.0.to_le_bytes());
    hasher.update(law_name.as_bytes());
    match kind {
        LawKind::Algebraic => hasher.update([0u8]),
        LawKind::MemoryFrame { untouched_mem } => {
            hasher.update([1u8]);
            hasher.update(untouched_mem.0.to_le_bytes());
        }
    }
    for &(vid, ty) in params {
        hasher.update(vid.0.to_le_bytes());
        hasher.update([matches!(ty, ValType::I64) as u8]);
    }
    if let Ok(s) = serde_json::to_vec(&IrRegion::from_kernel(pre)) {
        hasher.update(&s);
    }
    if let Ok(s) = serde_json::to_vec(&IrRegion::from_kernel(lhs)) {
        hasher.update(&s);
    }
    if let Ok(s) = serde_json::to_vec(&IrRegion::from_kernel(rhs)) {
        hasher.update(&s);
    }
    let mut out: [u8; 32] = hasher.finalize().into();
    if out.iter().all(|&b| b == 0) {
        out[0] = 1;
    }
    out
}

fn dedup_preserve_order(items: &mut Vec<String>) {
    let mut seen = std::collections::HashSet::new();
    items.retain(|x| seen.insert(x.clone()));
}

fn hex_encode(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        use std::fmt::Write as _;
        let _ = write!(s, "{b:02x}");
    }
    s
}

fn infer_yield_types(region: &Region, params: &[(ValId, ValType)]) -> Vec<ValType> {
    let mut tys = std::collections::HashMap::new();
    for &(vid, ty) in params {
        tys.insert(vid, ty);
    }
    if let RegionNode::Block(span) = region.root {
        let mut yielded = Vec::new();
        for i in 0..span.len {
            if let Some(stmt) = region.try_stmt(span, i) {
                match stmt {
                    Stmt::Let { dst, ty, .. } => {
                        tys.insert(dst, ty);
                    }
                    Stmt::Call { results, .. } | Stmt::Region { results, .. } => {
                        for (vid, ty) in region.vars(results) {
                            tys.insert(vid, ty);
                        }
                    }
                    Stmt::Yield(vals) | Stmt::Return(vals) => {
                        yielded = region
                            .vals(vals)
                            .map(|v| tys.get(&v).copied().unwrap_or(ValType::I32))
                            .collect();
                    }
                    _ => {}
                }
            }
        }
        return yielded;
    }
    Vec::new()
}

fn max_val_in_region(region: &Region) -> u32 {
    fn walk(r: RegionRef<'_>) -> u32 {
        let mut m = 0u32;
        match r.node {
            RegionNode::Block(span) => {
                for i in 0..span.len {
                    if let Some(stmt) = r.region.try_stmt(span, i) {
                        match stmt {
                            Stmt::Let { dst, op, .. } => {
                                m = m.max(dst.0);
                                match op {
                                    Op::Copy(a) | Op::Un(_, a) | Op::Load { addr: a, .. }
                                    | Op::MemoryGrow { delta: a, .. } => m = m.max(a.0),
                                    Op::Bin(_, a, b) => m = m.max(a.0).max(b.0),
                                    Op::Select { cond, true_val, false_val } => {
                                        m = m.max(cond.0).max(true_val.0).max(false_val.0);
                                    }
                                    _ => {}
                                }
                            }
                            Stmt::Call { results, args, .. } => {
                                for (v, _) in r.vars(results) {
                                    m = m.max(v.0);
                                }
                                for v in r.vals(args) {
                                    m = m.max(v.0);
                                }
                            }
                            Stmt::Region { results, region } => {
                                for (v, _) in r.vars(results) {
                                    m = m.max(v.0);
                                }
                                if let Some(sub) = r.child(region) {
                                    m = m.max(walk(sub));
                                }
                            }
                            Stmt::Yield(vals) | Stmt::Return(vals) => {
                                for v in r.vals(vals) {
                                    m = m.max(v.0);
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }
            RegionNode::IfElse { cond, then_region, else_region, .. } => {
                m = m.max(cond.0);
                if let Some(s) = r.child(then_region) {
                    m = m.max(walk(s));
                }
                if let Some(s) = r.child(else_region) {
                    m = m.max(walk(s));
                }
            }
            RegionNode::BoundedLoop { body, .. } => {
                if let Some(s) = r.child(body) {
                    m = m.max(walk(s));
                }
            }
            RegionNode::InvariantLoop { cond, invariant_pred, fuel_measure, body, .. } => {
                for id in [cond, invariant_pred, fuel_measure, body] {
                    if let Some(s) = r.child(id) {
                        m = m.max(walk(s));
                    }
                }
            }
        }
        m
    }
    walk(region.as_ref())
}

fn max_mem_id_in_region(region: &Region) -> Option<u16> {
    fn walk(r: RegionRef<'_>) -> Option<u16> {
        let mut mx: Option<u16> = None;
        let bump = |mx: &mut Option<u16>, id: u16| {
            *mx = Some(mx.map_or(id, |cur| cur.max(id)));
        };
        match r.node {
            RegionNode::Block(span) => {
                for i in 0..span.len {
                    if let Some(stmt) = r.region.try_stmt(span, i) {
                        match stmt {
                            Stmt::Let {
                                op:
                                    Op::Load { mem, .. }
                                    | Op::MemorySize(mem)
                                    | Op::MemoryGrow { mem, .. },
                                ..
                            } => bump(&mut mx, mem.0),
                            Stmt::Effect(
                                gnomon_kernel::EffectOp::Store { mem, .. }
                                | gnomon_kernel::EffectOp::MemoryFill { mem, .. },
                            ) => bump(&mut mx, mem.0),
                            Stmt::Effect(gnomon_kernel::EffectOp::MemoryCopy {
                                dst_mem,
                                src_mem,
                                ..
                            }) => {
                                bump(&mut mx, dst_mem.0);
                                bump(&mut mx, src_mem.0);
                            }
                            Stmt::Region { region, .. } => {
                                if let Some(sub) = r.child(region)
                                    && let Some(sub_mx) = walk(sub)
                                {
                                    bump(&mut mx, sub_mx);
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }
            RegionNode::IfElse { then_region, else_region, .. } => {
                for id in [then_region, else_region] {
                    if let Some(sub) = r.child(id)
                        && let Some(sub_mx) = walk(sub)
                    {
                        bump(&mut mx, sub_mx);
                    }
                }
            }
            RegionNode::BoundedLoop { body, .. } => {
                if let Some(sub) = r.child(body)
                    && let Some(sub_mx) = walk(sub)
                {
                    bump(&mut mx, sub_mx);
                }
            }
            RegionNode::InvariantLoop { cond, invariant_pred, fuel_measure, body, .. } => {
                for id in [cond, invariant_pred, fuel_measure, body] {
                    if let Some(sub) = r.child(id)
                        && let Some(sub_mx) = walk(sub)
                    {
                        bump(&mut mx, sub_mx);
                    }
                }
            }
        }
        mx
    }
    walk(region.as_ref())
}
