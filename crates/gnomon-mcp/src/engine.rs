//! Unified stateful Gnomon verification & abstraction engine shared by CLI and MCP server.

use std::path::Path;
use std::time::Instant;

use gnomon_kernel::{
    BinOp, CallTarget, FuncDef, FuncId, HeapState, HostCallId, Law, LawKind, LawList, MemId,
    MemWidth, MemoryDef, Module, Op, Region, RegionBuilder, RegionNode, RegionRef, Stmt, Stratum,
    StratumId, StratumOp, StratumRegistry, TrapCode, UnOp, Val, ValId, ValType, eval_func,
    eval_region, split_invariant_loop, validate_read_only_with_registry,
};
use gnomon_sieve::{
    BitwuzlaNativeBackend, CliffReport, ConsolidationConfig, ConsolidationReport, ContractSpec,
    EgglogSimplifier, EqSatConfig, EquivOptions, FuncCliffReport, SliceBoundExpr, SliceFrameSpec,
    SmtBackend, SmtModel, SmtResult, StackRefinement, consolidate_registry,
    eqsat::count_region_nodes, estimate_region_cliff, estimate_smt_cliff, render_autodoc,
};
use gnomon_wasm::{ExecOutcome, FuzzConfig, FuzzOutcome, emit_wasm, fuzz_equivalence};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::GnomonError;
use crate::ir_codec::{
    InputType, IrDocument, IrLawKind, IrModule, IrRegion, IrStratum, IrStratumOp, IrTrapCode,
    IrTypedVar, IrVal, IrValType, LoadedArtifact, find_entry_func,
    load_artifact_bytes_with_registry, load_artifact_from_mcp_arg_with_registry,
};
use crate::rust_bridge::{
    bind_stratum_imports, generate_strata_rs, lower_module_strata, module_has_stratum_calls,
    module_has_stratum_imports, normalize_nested_returns_for_stratum, rewrite_region_call_targets,
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

    pub fn bind_artifact(&self, artifact: LoadedArtifact) -> Result<LoadedArtifact, GnomonError> {
        match artifact {
            LoadedArtifact::Module(m) if module_has_stratum_imports(&m) => {
                Ok(LoadedArtifact::Module(bind_stratum_imports(m, &self.registry)?))
            }
            other => Ok(other),
        }
    }

    pub fn load_artifact_bytes(
        &self,
        bytes: &[u8],
        kind: InputType,
        path: Option<&str>,
    ) -> Result<(InputType, LoadedArtifact), GnomonError> {
        load_artifact_bytes_with_registry(bytes, kind, path, Some(&self.registry))
    }

    pub fn load_artifact_from_mcp_arg(
        &self,
        content: Option<&str>,
        file_path: Option<&str>,
        kind: InputType,
    ) -> Result<(InputType, LoadedArtifact), GnomonError> {
        load_artifact_from_mcp_arg_with_registry(content, file_path, kind, Some(&self.registry))
    }

    pub fn emit_rust(&self, include_candidates: bool) -> String {
        generate_strata_rs(&self.registry, include_candidates)
    }

    pub fn lower_module(&self, module: &Module) -> Result<Module, GnomonError> {
        lower_module_strata(module, &self.registry)
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
            LoadedArtifact::Module(mut module) => {
                let mut diagnostics = Vec::new();
                if module_has_stratum_imports(&module) {
                    let bound_count = module
                        .host_contracts
                        .iter()
                        .filter(|hc| hc.module_name == "stratum")
                        .count();
                    module = bind_stratum_imports(module, &self.registry)?;
                    diagnostics.push(format!(
                        "bound {bound_count} stratum import(s) to CallTarget::Stratum"
                    ));
                }
                let roundtrip_ok = if module_has_stratum_calls(&module) {
                    match lower_module_strata(&module, &self.registry)
                        .and_then(|lowered| {
                            emit_wasm(&lowered).map_err(|e| GnomonError::Wasm(e.to_string()))
                        }) {
                        Ok(bytes) => {
                            diagnostics.push(format!(
                                "lowered standalone round-trip emit valid ({} wasm bytes)",
                                bytes.len()
                            ));
                            true
                        }
                        Err(e) => {
                            diagnostics.push(format!("lowered emit_wasm diagnostic: {e}"));
                            false
                        }
                    }
                } else {
                    match emit_wasm(&module) {
                        Ok(bytes) => {
                            diagnostics
                                .push(format!("round-trip emit valid ({} wasm bytes)", bytes.len()));
                            true
                        }
                        Err(e) => {
                            diagnostics.push(format!("emit_wasm diagnostic: {e}"));
                            false
                        }
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
                let cliff_report = estimate_smt_cliff(&module, &self.registry);
                let cliff_warnings = cliff_report.warnings.clone();
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
                    cliff_report: Some(cliff_report),
                    cliff_warnings,
                    ir: ir_doc,
                })
            }
            LoadedArtifact::Region { params, results, region } => {
                let ssa_nodes = count_region_nodes(&region);
                let ro = validate_read_only_with_registry(&region, &self.registry);
                let region_metrics = estimate_region_cliff(&region, &self.registry);
                let cliff_warnings = region_metrics.warnings.clone();
                let cliff_report = CliffReport {
                    level: region_metrics.level,
                    total_ssa_nodes: region_metrics.ssa_nodes,
                    total_nonlinear_ops: region_metrics.nonlinear_ops,
                    total_nonlinear64_ops: region_metrics.nonlinear64_ops,
                    max_nonlinear_chain_depth: region_metrics.max_nonlinear_chain_depth,
                    max_nonlinear64_chain_depth: region_metrics.max_nonlinear64_chain_depth,
                    total_mem_stores: region_metrics.mem_stores,
                    total_conditional_mem_stores: region_metrics.conditional_mem_stores,
                    max_loop_depth: region_metrics.max_loop_depth,
                    has_unbounded_loop: region_metrics.has_unbounded_loop,
                    functions: vec![FuncCliffReport {
                        func_id: 0,
                        name: "<region>".into(),
                        export_name: None,
                        metrics: region_metrics,
                    }],
                    warnings: cliff_warnings.clone(),
                };
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
                    cliff_report: Some(cliff_report),
                    cliff_warnings,
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
            Some(LoadedArtifact::Module(mut module)) => {
                if module_has_stratum_imports(&module) {
                    module = bind_stratum_imports(module, &self.registry)?;
                }
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
        let normalized_body = normalize_nested_returns_for_stratum(&body)?;
        let op = StratumOp {
            id: StratumId(id),
            name: name.clone(),
            layer,
            params: params.into_iter().map(|v| (ValId(v.id), v.ty.into())).collect(),
            results: results.into_iter().map(Into::into).collect(),
            body: normalized_body,
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
        ignore_dead_stack: bool,
    ) -> Result<CheckGoalOutput, GnomonError> {
        self.check_goal_with_module(
            None,
            candidate,
            spec,
            params,
            precondition,
            loop_postcondition,
            timeout_ms,
            ignore_dead_stack,
        )
    }

    /// Runs `check_goal` using an explicit module context (preserving `memories`, `globals`,
    /// helper `funcs`, and `host_contracts` from `.wasm`/`.rs` inputs without requiring `--state`),
    /// falling back to `self.active_module` when `context_module` is `None`.
    ///
    /// Note: `check_goal` routes directly to `egglog` + `Bitwuzla` (`check_equivalence_with_options`)
    /// without Stage-1 raw-memory Wasmtime fuzzing so `--ignore-dead-stack` never suffers false
    /// falsifications on dead shadow-stack bytes `[0 .. SP_in)`.
    #[allow(clippy::too_many_arguments)]
    pub fn check_goal_with_module(
        &mut self,
        context_module: Option<Module>,
        candidate: Region,
        spec: Region,
        params: Vec<IrTypedVar>,
        precondition: Option<Region>,
        loop_postcondition: Option<Region>,
        timeout_ms: u64,
        ignore_dead_stack: bool,
    ) -> Result<CheckGoalOutput, GnomonError> {
        let start = Instant::now();
        let k_params: Vec<(ValId, ValType)> =
            params.iter().map(|v| (ValId(v.id), v.ty.into())).collect();
        let mut module = match context_module {
            Some(m) => m,
            None => self.active_module.clone().unwrap_or_default(),
        };
        let mut mem_regions: Vec<&Region> = vec![&candidate, &spec];
        if let Some(ref pre) = precondition {
            mem_regions.push(pre);
        }
        if let Some(ref post) = loop_postcondition {
            mem_regions.push(post);
        }
        ensure_memories_for_regions(&mut module, &self.registry, &mem_regions);

        let eqsat = EgglogSimplifier::new(EqSatConfig {
            max_iters: 5,
            max_nodes: 5_000,
            timeout_ms: timeout_ms.min(5_000),
        });

        // Case A: InvariantLoop VC splitting via frozen gnomon-kernel TCB!
        if matches!(candidate.root, RegionNode::InvariantLoop { .. }) {
            let cliff_warnings =
                collect_region_cliff_warnings(&[("candidate", &candidate)], &self.registry);
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
                            cliff_warnings,
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
                            cliff_warnings,
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
                cliff_warnings,
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
        let cliff_warnings = collect_region_cliff_warnings(
            &[("candidate", &simp_cand), ("spec", &simp_spec)],
            &self.registry,
        );

        let mut backend = BitwuzlaNativeBackend::with_time_limit_ms(timeout_ms.max(100));
        let pre_ref = precondition.as_ref().filter(|p| **p != Region::empty());
        let equiv_opts = EquivOptions {
            stack_refinement: ignore_dead_stack.then(StackRefinement::default),
        };
        let smt_res = backend
            .check_equivalence_with_options(
                &module,
                &self.registry,
                &simp_cand,
                &simp_spec,
                pre_ref,
                &equiv_opts,
            )
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
                    cliff_warnings,
                    elapsed_ms: start.elapsed().as_secs_f64() * 1000.0,
                    counterexample: None,
                    detail: if ignore_dead_stack {
                        "goal proved equivalent (shadow-stack refined) by egglog + Bitwuzla QF_ABV"
                            .into()
                    } else {
                        "goal proved equivalent by egglog + Bitwuzla QF_ABV".into()
                    },
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
                    cliff_warnings,
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
                cliff_warnings,
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
    // Tool 7: gnomon_check_contract (pre/post, inductive invariants, inline assume/assert)
    // -----------------------------------------------------------------------
    pub fn check_contract(
        &self,
        req: CheckContractRequest,
    ) -> Result<CheckContractOutput, GnomonError> {
        let start = Instant::now();
        let suite_mode = !req.ops.is_empty() || req.init.is_some();

        if suite_mode && req.entry.is_some() {
            return Err(GnomonError::InvalidInput(
                "cannot combine entry with ops/init inductive suite mode".into(),
            ));
        }
        if suite_mode && (req.requires.is_some() || req.ensures.is_some()) {
            return Err(GnomonError::InvalidInput(
                "requires/ensures are only supported in single-op mode; use invariant for multi-op suite mode"
                    .into(),
            ));
        }
        if suite_mode && req.use_initial_state {
            return Err(GnomonError::InvalidInput(
                "use_initial_state applies only to single-op mode; in suite mode --init runs with initial state and --ops run inductively"
                    .into(),
            ));
        }

        // Preserve full Module (memories, globals, host_contracts, helper funcs) when loading
        // `.wasm`/`.ir`/`.rs`, or fall back to `self.active_module`.
        let (mut module, standalone_region) = match req.artifact {
            Some(LoadedArtifact::Module(mut m)) => {
                if module_has_stratum_imports(&m) {
                    m = bind_stratum_imports(m, &self.registry)?;
                }
                (m, None)
            }
            Some(LoadedArtifact::Region { params, results, region }) => {
                if suite_mode {
                    return Err(GnomonError::InvalidInput(
                        "inductive multi-op suite mode requires a module artifact with named functions, not a standalone region"
                            .into(),
                    ));
                }
                if req.entry.is_some() {
                    return Err(GnomonError::InvalidInput(
                        "cannot specify entry function when checking a standalone region artifact"
                            .into(),
                    ));
                }
                (self.active_module.clone().unwrap_or_default(), Some((params, results, region)))
            }
            None => {
                let mut m = self
                    .active_module
                    .as_ref()
                    .ok_or_else(|| {
                        GnomonError::InvalidInput(
                            "no module loaded; call gnomon_lift_check or provide an input artifact"
                                .into(),
                        )
                    })?
                    .clone();
                if module_has_stratum_imports(&m) {
                    m = bind_stratum_imports(m, &self.registry)?;
                }
                (m, None)
            }
        };

        let resolved_req = req
            .requires
            .map(|p| resolve_contract_pred(&module, &self.registry, p, "requires"))
            .transpose()?;
        let resolved_ens = req
            .ensures
            .map(|p| resolve_contract_pred(&module, &self.registry, p, "ensures"))
            .transpose()?;
        let resolved_inv = req
            .invariant
            .map(|p| resolve_contract_pred(&module, &self.registry, p, "invariant"))
            .transpose()?;
        if let Some(ref inv) = resolved_inv
            && inv.params.as_ref().is_some_and(|p| !p.is_empty())
        {
            return Err(GnomonError::InvalidInput(
                "invariant predicate must take 0 parameters".into(),
            ));
        }

        // For standalone region inputs, synthesize any referenced memories that aren't already
        // declared on the fallback module (real Module inputs are preserved untouched).
        if let Some((_, _, ref reg)) = standalone_region {
            let mut regions: Vec<&Region> = vec![reg];
            if let Some(ref r) = resolved_req {
                regions.push(&r.region);
            }
            if let Some(ref e) = resolved_ens {
                regions.push(&e.region);
            }
            if let Some(ref i) = resolved_inv {
                regions.push(&i.region);
            }
            ensure_memories_for_regions(&mut module, &self.registry, &regions);
        }

        // --- Single-op mode ---
        if !suite_mode {
            let (entry_name, params, results, body) = match standalone_region {
                Some((p, r, reg)) => ("<region>".to_string(), p, r, reg),
                None => {
                    let func = find_entry_func(&module, req.entry.as_deref())?;
                    (
                        func.name.clone(),
                        func.params.clone(),
                        func.results.clone(),
                        func.body.clone(),
                    )
                }
            };
            let cliff_warnings =
                collect_region_cliff_warnings(&[(&entry_name, &body)], &self.registry);
            let op_res = self.run_single_contract(
                &module,
                &entry_name,
                &params,
                &results,
                &body,
                resolved_req.as_ref(),
                resolved_ens.as_ref(),
                resolved_inv.as_ref(),
                req.use_initial_state,
                req.check_trap_free,
                req.ignore_dead_stack,
                req.slice_frame,
                req.timeout_ms,
                "single",
            )?;
            return Ok(CheckContractOutput {
                status: op_res.status,
                mode: "single".into(),
                entry: Some(op_res.entry),
                use_initial_state: req.use_initial_state,
                check_trap_free: req.check_trap_free,
                cliff_warnings,
                elapsed_ms: start.elapsed().as_secs_f64() * 1000.0,
                counterexample: op_res.counterexample,
                op_results: Vec::new(),
                detail: op_res.detail,
            });
        }

        // --- Inductive multi-op suite mode ---
        // Validate all referenced functions exist before invoking the SMT solver.
        let init_func = match req.init.as_deref() {
            Some(init_name) => Some(
                find_entry_func(&module, Some(init_name))
                    .map_err(|_| {
                        GnomonError::InvalidInput(format!(
                            "init function '{init_name}' not found in module"
                        ))
                    })?
                    .clone(),
            ),
            None => None,
        };
        let mut op_funcs = Vec::with_capacity(req.ops.len());
        for op_name in &req.ops {
            let f = find_entry_func(&module, Some(op_name.as_str()))
                .map_err(|_| {
                    GnomonError::InvalidInput(format!(
                        "op function '{op_name}' not found in module"
                    ))
                })?
                .clone();
            op_funcs.push(f);
        }

        let mut cliff_targets: Vec<(&str, &Region)> =
            Vec::with_capacity(op_funcs.len() + usize::from(init_func.is_some()));
        if let Some(ref init_f) = init_func {
            cliff_targets.push((&init_f.name, &init_f.body));
        }
        for op_f in &op_funcs {
            cliff_targets.push((&op_f.name, &op_f.body));
        }
        let cliff_warnings = collect_region_cliff_warnings(&cliff_targets, &self.registry);

        let mut op_results = Vec::with_capacity(op_funcs.len() + usize::from(init_func.is_some()));

        // Base case: verify `init` from concrete initial state (`I(post_init)`).
        if let Some(init_f) = init_func {
            let res = self.run_single_contract(
                &module,
                &init_f.name,
                &init_f.params,
                &init_f.results,
                &init_f.body,
                None,
                None,
                resolved_inv.as_ref(),
                true,
                req.check_trap_free,
                req.ignore_dead_stack,
                req.slice_frame,
                req.timeout_ms,
                "init",
            )?;
            op_results.push(res);
        }

        // Inductive step: verify every op in `ops` with `use_initial_state = false`.
        for op_f in &op_funcs {
            let res = self.run_single_contract(
                &module,
                &op_f.name,
                &op_f.params,
                &op_f.results,
                &op_f.body,
                None,
                None,
                resolved_inv.as_ref(),
                false,
                req.check_trap_free,
                req.ignore_dead_stack,
                req.slice_frame,
                req.timeout_ms,
                "op",
            )?;
            op_results.push(res);
        }

        let falsified: Vec<&str> = op_results
            .iter()
            .filter(|r| r.status == "FALSIFIED")
            .map(|r| r.entry.as_str())
            .collect();
        let unknown: Vec<&str> = op_results
            .iter()
            .filter(|r| r.status == "UNKNOWN")
            .map(|r| r.entry.as_str())
            .collect();
        let first_cex = op_results
            .iter()
            .find(|r| r.status == "FALSIFIED")
            .and_then(|r| r.counterexample.clone());

        let (overall_status, detail) = if !falsified.is_empty() {
            (
                "FALSIFIED".to_string(),
                format!(
                    "inductive suite falsified ({}/{} checks failed: {})",
                    falsified.len(),
                    op_results.len(),
                    falsified.join(", ")
                ),
            )
        } else if !unknown.is_empty() {
            (
                "UNKNOWN".to_string(),
                format!(
                    "inductive suite unknown ({}/{} checks unknown: {})",
                    unknown.len(),
                    op_results.len(),
                    unknown.join(", ")
                ),
            )
        } else {
            (
                "PROVED".to_string(),
                format!(
                    "inductive suite proved (all {} checks passed)",
                    op_results.len()
                ),
            )
        };

        Ok(CheckContractOutput {
            status: overall_status,
            mode: "inductive_suite".into(),
            entry: None,
            use_initial_state: req.init.is_some(),
            check_trap_free: req.check_trap_free,
            cliff_warnings,
            elapsed_ms: start.elapsed().as_secs_f64() * 1000.0,
            counterexample: first_cex,
            op_results,
            detail,
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn run_single_contract(
        &self,
        module: &Module,
        entry_name: &str,
        params: &[(ValId, ValType)],
        results: &[ValType],
        body: &Region,
        requires: Option<&ResolvedPred>,
        ensures: Option<&ResolvedPred>,
        invariant: Option<&ResolvedPred>,
        use_initial_state: bool,
        check_trap_free: bool,
        ignore_dead_stack: bool,
        slice_frame: Option<SliceFrameSpec>,
        timeout_ms: u64,
        role: &str,
    ) -> Result<ContractOpResult, GnomonError> {
        let op_start = Instant::now();
        let mut spec = ContractSpec::new(params, results, body)
            .with_check_trap_free(check_trap_free)
            .with_initial_state(use_initial_state);
        if ignore_dead_stack {
            spec = spec.with_stack_refinement(StackRefinement::default());
        }
        if let Some(sf) = slice_frame {
            spec = spec.with_slice_frame(sf);
        }
        if let Some(r) = requires {
            spec.requires = Some(&r.region);
            spec.requires_params = r.params.as_deref();
        }
        if let Some(e) = ensures {
            spec.ensures = Some(&e.region);
            spec.ensures_params = e.params.as_deref();
        }
        if let Some(inv) = invariant {
            spec.invariant = Some(&inv.region);
        }

        let mut backend = BitwuzlaNativeBackend::with_time_limit_ms(timeout_ms.max(100));
        let smt_res = backend
            .check_contract(module, &self.registry, &spec)
            .map_err(|e| GnomonError::Sieve(e.to_string()))?;
        let elapsed_ms = op_start.elapsed().as_secs_f64() * 1000.0;

        match smt_res {
            SmtResult::Unsat => Ok(ContractOpResult {
                entry: entry_name.to_string(),
                role: role.to_string(),
                status: "PROVED".into(),
                use_initial_state,
                check_trap_free,
                elapsed_ms,
                counterexample: None,
                detail: format!("contract for '{entry_name}' proved by Bitwuzla QF_ABV"),
            }),
            SmtResult::Sat(model) => {
                let cex = smt_model_to_contract_cex(params, &model);
                Ok(ContractOpResult {
                    entry: entry_name.to_string(),
                    role: role.to_string(),
                    status: "FALSIFIED".into(),
                    use_initial_state,
                    check_trap_free,
                    elapsed_ms,
                    counterexample: Some(cex),
                    detail: format!("contract for '{entry_name}' falsified by Bitwuzla QF_ABV"),
                })
            }
            SmtResult::Unknown(reason) => Ok(ContractOpResult {
                entry: entry_name.to_string(),
                role: role.to_string(),
                status: "UNKNOWN".into(),
                use_initial_state,
                check_trap_free,
                elapsed_ms,
                counterexample: None,
                detail: format!("Bitwuzla returned unknown for '{entry_name}': {reason}"),
            }),
        }
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

    // -----------------------------------------------------------------------
    // Tool 8: gnomon_profile (native x86-64 & ARM64 assembly + llvm-mca + host bench)
    // -----------------------------------------------------------------------
    pub fn profile(
        &self,
        req: &crate::profiler::ProfileRequest,
    ) -> Result<crate::profiler::ProfileOutput, GnomonError> {
        let reg = if self.registry.promoted().is_empty() && self.registry.candidates().is_empty() {
            None
        } else {
            Some(&self.registry)
        };
        crate::profiler::profile_rust(req, reg)
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
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub cliff_report: Option<CliffReport>,
    #[serde(default)]
    pub cliff_warnings: Vec<String>,
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
    #[serde(default)]
    pub cliff_warnings: Vec<String>,
    pub elapsed_ms: f64,
    pub counterexample: Option<CounterexampleJson>,
    pub detail: String,
}

/// Predicate reference for `check_contract` (`requires`, `ensures`, or `invariant`).
#[derive(Clone, Debug)]
pub enum ContractPred {
    /// Function name inside the target module.
    FuncName(String),
    /// External `.wasm` or `.ir` artifact (optionally selecting a named function inside a module).
    Artifact {
        artifact: Box<LoadedArtifact>,
        entry: Option<String>,
    },
}

/// Request parameters for `GnomonEngine::check_contract` (single-op or multi-op inductive suite).
#[derive(Clone, Debug)]
pub struct CheckContractRequest {
    /// Optional module or region artifact override (defaults to `self.active_module` when `None`).
    pub artifact: Option<LoadedArtifact>,
    /// Single-op mode: entry function name (defaults to func 0 when `ops`/`init` are empty).
    pub entry: Option<String>,
    /// Inductive suite mode: operation function names checked with `use_initial_state = false`.
    pub ops: Vec<String>,
    /// Inductive suite mode: optional initializer function name checked with `use_initial_state = true`.
    pub init: Option<String>,
    /// Optional precondition (`requires`, single-op mode only).
    pub requires: Option<ContractPred>,
    /// Optional postcondition (`ensures`, single-op mode only).
    pub ensures: Option<ContractPred>,
    /// Optional 0-arg state invariant (`invariant`).
    pub invariant: Option<ContractPred>,
    /// Single-op mode: start from concrete initial state and do NOT assume `invariant` on pre-state.
    pub use_initial_state: bool,
    /// Require trap-freedom on assumption-satisfying paths (default `true`).
    pub check_trap_free: bool,
    /// Enable shadow-stack refinement (`StackRefinement::default()`): pins/constrains `SP_in`,
    /// proves `SP_out == SP_in`, and ignores dead stack bytes strictly below `SP_in`.
    pub ignore_dead_stack: bool,
    /// Optional intra-memory write-frame restriction (`SliceFrameSpec`).
    pub slice_frame: Option<SliceFrameSpec>,
    /// Bitwuzla per-check timeout budget in milliseconds (default `5_000`, clamped to `>= 100`).
    pub timeout_ms: u64,
}

impl Default for CheckContractRequest {
    fn default() -> Self {
        Self {
            artifact: None,
            entry: None,
            ops: Vec::new(),
            init: None,
            requires: None,
            ensures: None,
            invariant: None,
            use_initial_state: false,
            check_trap_free: true,
            ignore_dead_stack: false,
            slice_frame: None,
            timeout_ms: 5_000,
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize, schemars::JsonSchema)]
pub struct ContractMemoryBytesJson {
    pub mem_id: u16,
    pub bytes: Vec<(u32, u8)>,
}

#[derive(Clone, Debug, Serialize, Deserialize, schemars::JsonSchema)]
pub struct ContractCounterexampleJson {
    /// Symbolic scalar parameter values `(val_id, val)` formatted like `inputs` in `check_goal`.
    pub scalar_values: Vec<(u32, IrVal)>,
    /// Symbolic pre-state global values `(global_id, val)`.
    pub global_values: Vec<(u32, IrVal)>,
    /// Sparse pre-state memory byte witnesses grouped by `mem_id`.
    pub memory_bytes: Vec<ContractMemoryBytesJson>,
}

#[derive(Clone, Debug, Serialize, Deserialize, schemars::JsonSchema)]
pub struct ContractOpResult {
    pub entry: String,
    pub role: String,
    pub status: String,
    pub use_initial_state: bool,
    pub check_trap_free: bool,
    pub elapsed_ms: f64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub counterexample: Option<ContractCounterexampleJson>,
    pub detail: String,
}

#[derive(Clone, Debug, Serialize, Deserialize, schemars::JsonSchema)]
pub struct CheckContractOutput {
    pub status: String,
    pub mode: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub entry: Option<String>,
    pub use_initial_state: bool,
    pub check_trap_free: bool,
    #[serde(default)]
    pub cliff_warnings: Vec<String>,
    pub elapsed_ms: f64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub counterexample: Option<ContractCounterexampleJson>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub op_results: Vec<ContractOpResult>,
    pub detail: String,
}

struct ResolvedPred {
    params: Option<Vec<(ValId, ValType)>>,
    region: Region,
}

fn resolve_contract_pred(
    module: &Module,
    registry: &StratumRegistry,
    pred: ContractPred,
    role: &str,
) -> Result<ResolvedPred, GnomonError> {
    match pred {
        ContractPred::FuncName(name) => {
            let func = find_entry_func(module, Some(&name)).map_err(|_| {
                GnomonError::InvalidInput(format!(
                    "{role} function '{name}' not found in module"
                ))
            })?;
            Ok(ResolvedPred {
                params: Some(func.params.clone()),
                region: func.body.clone(),
            })
        }
        ContractPred::Artifact { artifact, entry } => match *artifact {
            LoadedArtifact::Module(mut ext_mod) => {
                if module_has_stratum_imports(&ext_mod) {
                    ext_mod = bind_stratum_imports(ext_mod, registry)?;
                }
                let func = find_entry_func(&ext_mod, entry.as_deref()).map_err(|e| {
                    GnomonError::InvalidInput(format!("{role} artifact error: {e}"))
                })?;
                Ok(ResolvedPred {
                    params: Some(func.params.clone()),
                    region: func.body.clone(),
                })
            }
            LoadedArtifact::Region { params, results: _, region } => Ok(ResolvedPred {
                params: if params.is_empty() { None } else { Some(params) },
                region,
            }),
        },
    }
}

fn smt_model_to_contract_cex(
    params: &[(ValId, ValType)],
    model: &SmtModel,
) -> ContractCounterexampleJson {
    let mut scalar_values: Vec<(u32, IrVal)> = Vec::new();
    for &(vid, ty) in params {
        let val = model
            .scalar_values
            .iter()
            .find(|(id, _)| *id == vid)
            .map(|(_, v)| *v)
            .unwrap_or(Val::default_for(ty));
        scalar_values.push((vid.0, val.into()));
    }
    for &(vid, val) in &model.scalar_values {
        if !scalar_values.iter().any(|(id, _)| *id == vid.0) {
            scalar_values.push((vid.0, val.into()));
        }
    }
    let global_values = model
        .global_values
        .iter()
        .map(|&(gid, val)| (gid.0, val.into()))
        .collect();
    let memory_bytes = model
        .memory_bytes
        .iter()
        .map(|(mid, bytes)| ContractMemoryBytesJson {
            mem_id: mid.0,
            bytes: bytes.clone(),
        })
        .collect();
    ContractCounterexampleJson {
        scalar_values,
        global_values,
        memory_bytes,
    }
}

fn ensure_memories_for_regions(module: &mut Module, registry: &StratumRegistry, regions: &[&Region]) {
    let mut max_mem: Option<u16> = None;
    for reg in regions {
        if let Some(mx) = max_mem_id_in_region(reg) {
            max_mem = Some(max_mem.map_or(mx, |cur| cur.max(mx)));
        }
    }
    for st in registry.promoted() {
        if let Some(mx) = max_mem_id_in_region(&st.op.body) {
            max_mem = Some(max_mem.map_or(mx, |cur| cur.max(mx)));
        }
    }
    if let Some(mx) = max_mem {
        for id in 0..=mx {
            if !module.memories.iter().any(|mem| mem.id == MemId(id)) {
                module.memories.push(MemoryDef {
                    id: MemId(id),
                    min_pages: 1,
                    max_pages: Some(1),
                    init_data: Vec::new(),
                });
            }
        }
    }
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
            .unwrap_or(Val::default_for(ty));
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
    for &(gid, val) in &model.global_values {
        if let Some(g) = heap.globals.get_mut(gid.0 as usize) {
            *g = val;
        }
    }
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
        hasher.update([ty.to_u8()]);
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
                                    Op::ConstI32(_)
                                    | Op::ConstI64(_)
                                    | Op::ConstF32(_)
                                    | Op::ConstF64(_)
                                    | Op::ConstV128(_)
                                    | Op::GlobalGet(_)
                                    | Op::MemorySize(_) => {}
                                    Op::Copy(a)
                                    | Op::Un(_, a)
                                    | Op::Load { addr: a, .. }
                                    | Op::MemoryGrow { delta: a, .. }
                                    | Op::SimdExtractLane { vec: a, .. } => m = m.max(a.0),
                                    Op::Bin(_, a, b)
                                    | Op::SimdReplaceLane { vec: a, val: b, .. }
                                    | Op::SimdShuffle { lhs: a, rhs: b, .. } => {
                                        m = m.max(a.0).max(b.0);
                                    }
                                    Op::Select { cond, true_val, false_val } => {
                                        m = m.max(cond.0).max(true_val.0).max(false_val.0);
                                    }
                                    Op::SimdBitselect { a, b, mask } => {
                                        m = m.max(a.0).max(b.0).max(mask.0);
                                    }
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

// ===========================================================================
// Static SMT-Cliff Helper, Goal Module Merger, and `--slice-frame` Parser
// ===========================================================================

fn collect_region_cliff_warnings(
    regions: &[(&str, &Region)],
    registry: &StratumRegistry,
) -> Vec<String> {
    let mut out = Vec::new();
    for &(label, reg) in regions {
        let metrics = estimate_region_cliff(reg, registry);
        for w in metrics.warnings {
            out.push(format!("[{label}] {w}"));
        }
    }
    dedup_preserve_order(&mut out);
    out
}

/// Prepared regions and merged module context for `GnomonEngine::check_goal_with_module`.
#[derive(Clone, Debug)]
pub struct PreparedGoal {
    pub context_module: Option<Module>,
    pub candidate_params: Vec<(ValId, ValType)>,
    pub candidate: Region,
    pub spec: Region,
    pub precondition: Option<Region>,
    pub loop_postcondition: Option<Region>,
}

fn remap_region_ids(
    region: &Region,
    func_offset: u32,
    host_offset: u32,
) -> Result<Region, GnomonError> {
    if func_offset == 0 && host_offset == 0 {
        return Ok(region.clone());
    }
    rewrite_region_call_targets(region, &mut |target| match target {
        CallTarget::Func(fid) => Ok(CallTarget::Func(FuncId(fid.0 + func_offset))),
        CallTarget::Host(hid) => Ok(CallTarget::Host(HostCallId(hid.0 + host_offset))),
        CallTarget::Stratum(sid) => Ok(CallTarget::Stratum(sid)),
    })
}

struct GoalModuleMerger {
    merged: Option<Module>,
    sources: Vec<(Module, u32, u32)>,
}

impl GoalModuleMerger {
    fn new() -> Self {
        Self { merged: None, sources: Vec::new() }
    }

    fn merge_module(&mut self, module: Module) -> Result<(u32, u32), GnomonError> {
        for (prev, f_off, h_off) in &self.sources {
            if *prev == module {
                return Ok((*f_off, *h_off));
            }
        }
        if self.merged.is_none() {
            self.merged = Some(module.clone());
            self.sources.push((module, 0, 0));
            return Ok((0, 0));
        }

        let base = self.merged.as_mut().expect("checked is_some");
        for mem in &module.memories {
            if let Some(existing) = base.memories.iter_mut().find(|m| m.id == mem.id) {
                let new_min = existing.min_pages.max(mem.min_pages);
                existing.min_pages = new_min;
                existing.max_pages = match (existing.max_pages, mem.max_pages) {
                    (Some(a), Some(b)) => Some(a.max(b).max(new_min)),
                    _ => None,
                };
            } else {
                base.memories.push(mem.clone());
            }
        }
        for g in &module.globals {
            if !base.globals.iter().any(|bg| bg.id == g.id) {
                base.globals.push(g.clone());
            }
        }

        let func_off = base.funcs.iter().map(|f| f.id.0 + 1).max().unwrap_or(0);
        let host_off = base.host_contracts.iter().map(|h| h.id.0 + 1).max().unwrap_or(0);

        for hc in &module.host_contracts {
            let mut remapped = hc.clone();
            remapped.id = HostCallId(hc.id.0 + host_off);
            remapped.precondition = remap_region_ids(&hc.precondition, func_off, host_off)?;
            remapped.postcondition = remap_region_ids(&hc.postcondition, func_off, host_off)?;
            if let Some(ref sim) = hc.sim_body {
                remapped.sim_body = Some(remap_region_ids(sim, func_off, host_off)?);
            }
            base.host_contracts.push(remapped);
        }
        for f in &module.funcs {
            let mut remapped = f.clone();
            remapped.id = FuncId(f.id.0 + func_off);
            remapped.body = remap_region_ids(&f.body, func_off, host_off)?;
            base.funcs.push(remapped);
        }

        self.sources.push((module, func_off, host_off));
        Ok((func_off, host_off))
    }

    fn extract(
        &mut self,
        artifact: LoadedArtifact,
        entry: Option<&str>,
    ) -> Result<(Vec<(ValId, ValType)>, Region), GnomonError> {
        match artifact {
            LoadedArtifact::Module(m) => {
                let func = find_entry_func(&m, entry)?;
                let params = func.params.clone();
                let body = func.body.clone();
                let (func_off, host_off) = self.merge_module(m)?;
                let remapped_body = remap_region_ids(&body, func_off, host_off)?;
                Ok((params, remapped_body))
            }
            LoadedArtifact::Region { params, results: _, region } => Ok((params, region)),
        }
    }
}

/// Extracts candidate, spec, precondition, and postcondition regions from loaded artifacts
/// while preserving and merging full `Module` contexts (memories, globals, helper funcs,
/// host contracts) with collision-free `FuncId`/`HostCallId` remapping across distinct modules.
pub fn prepare_goal_artifacts(
    cand_art: LoadedArtifact,
    cand_entry: Option<&str>,
    spec_art: LoadedArtifact,
    spec_entry: Option<&str>,
    pre_art: Option<(LoadedArtifact, Option<&str>)>,
    post_art: Option<(LoadedArtifact, Option<&str>)>,
) -> Result<PreparedGoal, GnomonError> {
    let mut merger = GoalModuleMerger::new();
    let (candidate_params, candidate) = merger.extract(cand_art, cand_entry)?;
    let (_, spec) = merger.extract(spec_art, spec_entry)?;
    let precondition = match pre_art {
        Some((art, entry)) => Some(merger.extract(art, entry)?.1),
        None => None,
    };
    let loop_postcondition = match post_art {
        Some((art, entry)) => Some(merger.extract(art, entry)?.1),
        None => None,
    };
    Ok(PreparedGoal {
        context_module: merger.merged,
        candidate_params,
        candidate,
        spec,
        precondition,
        loop_postcondition,
    })
}

fn parse_u32_lit(raw: &str, full_spec: &str, field: &str) -> Result<u32, GnomonError> {
    let s = raw.trim();
    let parsed = if let Some(hex) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
        u32::from_str_radix(hex, 16)
    } else {
        s.parse::<u32>()
    };
    parsed.map_err(|_| {
        GnomonError::InvalidInput(format!(
            "invalid --slice-frame '{full_spec}': invalid u32 '{s}' for {field}"
        ))
    })
}

fn parse_slice_bound_expr(
    raw: &str,
    full_spec: &str,
    field: &str,
) -> Result<SliceBoundExpr, GnomonError> {
    let s = raw.trim();
    if let Some(rest) = s.strip_prefix("param:") {
        let idx = parse_u32_lit(rest, full_spec, &format!("{field} param index"))?;
        return Ok(SliceBoundExpr::Param(ValId(idx)));
    }
    if let Some(rest) = s.strip_prefix("const:") {
        let val = parse_u32_lit(rest, full_spec, &format!("{field} const value"))?;
        return Ok(SliceBoundExpr::Const(val));
    }
    let val = parse_u32_lit(s, full_spec, field)?;
    Ok(SliceBoundExpr::Const(val))
}

/// Parses a CLI `--slice-frame <SPEC>` string into a `gnomon_sieve::SliceFrameSpec`.
///
/// Supported forms:
/// - `readonly` (shorthand for `mem=0,base=0,len=0`)
/// - `base=<param:N|U32>,len=<param:N|U32>` with optional `mem=<M>` (e.g. `base=param:2,len=32`,
///   `mem=0,base=param:0,len=param:1`, `mem=1,readonly`)
/// - `param:<BASE_IDX>:<LEN>` or `param:<BASE_IDX>:param:<LEN_IDX>` (shorthand on `mem=0`, e.g. `param:2:32`)
pub fn parse_slice_frame_spec(raw: &str) -> Result<SliceFrameSpec, GnomonError> {
    let trimmed = raw.trim();
    if trimmed.is_empty() {
        return Err(GnomonError::InvalidInput(
            "invalid --slice-frame '': expected 'readonly', 'base=<param:N|U32>,len=<param:N|U32>' (optional 'mem=M'), or 'param:<N>:<LEN>'"
                .into(),
        ));
    }

    let lower = trimmed.to_ascii_lowercase();
    if lower == "readonly" || lower == "read-only" || lower == "read_only" {
        return Ok(SliceFrameSpec {
            mem: MemId(0),
            base: SliceBoundExpr::Const(0),
            len: SliceBoundExpr::Const(0),
        });
    }

    // Shorthand form: `param:<base_idx>:<len>` or `param:<base_idx>:param:<len_idx>`
    if !trimmed.contains('=') && !trimmed.contains(',') {
        let parts: Vec<&str> = trimmed.split(':').collect();
        if parts.len() == 3 && parts[0] == "param" {
            let base_idx = parse_u32_lit(parts[1], trimmed, "base param index")?;
            let len_val = parse_u32_lit(parts[2], trimmed, "len")?;
            return Ok(SliceFrameSpec {
                mem: MemId(0),
                base: SliceBoundExpr::Param(ValId(base_idx)),
                len: SliceBoundExpr::Const(len_val),
            });
        }
        if parts.len() == 4 && parts[0] == "param" && parts[2] == "param" {
            let base_idx = parse_u32_lit(parts[1], trimmed, "base param index")?;
            let len_idx = parse_u32_lit(parts[3], trimmed, "len param index")?;
            return Ok(SliceFrameSpec {
                mem: MemId(0),
                base: SliceBoundExpr::Param(ValId(base_idx)),
                len: SliceBoundExpr::Param(ValId(len_idx)),
            });
        }
        return Err(GnomonError::InvalidInput(format!(
            "invalid --slice-frame '{trimmed}': expected 'readonly', 'base=<param:N|U32>,len=<param:N|U32>' (optional 'mem=M'), or 'param:<N>:<LEN>'"
        )));
    }

    // Key-value comma-separated form: `mem=0,base=param:2,len=32` or `mem=1,readonly`
    let mut mem: Option<u16> = None;
    let mut base: Option<SliceBoundExpr> = None;
    let mut len: Option<SliceBoundExpr> = None;
    let mut readonly = false;

    for token in trimmed.split(',') {
        let tok = token.trim();
        if tok.is_empty() {
            return Err(GnomonError::InvalidInput(format!(
                "invalid --slice-frame '{trimmed}': empty comma-separated segment"
            )));
        }
        let tok_lower = tok.to_ascii_lowercase();
        if tok_lower == "readonly" || tok_lower == "read-only" || tok_lower == "read_only" {
            if readonly {
                return Err(GnomonError::InvalidInput(format!(
                    "invalid --slice-frame '{trimmed}': duplicate 'readonly'"
                )));
            }
            readonly = true;
            continue;
        }
        let Some((k, v)) = tok.split_once('=') else {
            return Err(GnomonError::InvalidInput(format!(
                "invalid --slice-frame '{trimmed}': expected 'key=value' or 'readonly', got '{tok}'"
            )));
        };
        match k.trim() {
            "mem" => {
                if mem.is_some() {
                    return Err(GnomonError::InvalidInput(format!(
                        "invalid --slice-frame '{trimmed}': duplicate key 'mem'"
                    )));
                }
                let m = v.trim().parse::<u16>().map_err(|_| {
                    GnomonError::InvalidInput(format!(
                        "invalid --slice-frame '{trimmed}': invalid u16 mem id '{}'",
                        v.trim()
                    ))
                })?;
                mem = Some(m);
            }
            "base" => {
                if base.is_some() {
                    return Err(GnomonError::InvalidInput(format!(
                        "invalid --slice-frame '{trimmed}': duplicate key 'base'"
                    )));
                }
                base = Some(parse_slice_bound_expr(v, trimmed, "base")?);
            }
            "len" => {
                if len.is_some() {
                    return Err(GnomonError::InvalidInput(format!(
                        "invalid --slice-frame '{trimmed}': duplicate key 'len'"
                    )));
                }
                len = Some(parse_slice_bound_expr(v, trimmed, "len")?);
            }
            other => {
                return Err(GnomonError::InvalidInput(format!(
                    "invalid --slice-frame '{trimmed}': unknown key '{other}' (expected 'mem', 'base', 'len', or 'readonly')"
                )));
            }
        }
    }

    let mem_id = MemId(mem.unwrap_or(0));
    if readonly {
        if base.is_some() || len.is_some() {
            return Err(GnomonError::InvalidInput(format!(
                "invalid --slice-frame '{trimmed}': cannot combine 'readonly' with explicit 'base' or 'len'"
            )));
        }
        return Ok(SliceFrameSpec {
            mem: mem_id,
            base: SliceBoundExpr::Const(0),
            len: SliceBoundExpr::Const(0),
        });
    }

    let base = base.ok_or_else(|| {
        GnomonError::InvalidInput(format!(
            "invalid --slice-frame '{trimmed}': missing required 'base=...' (or use 'readonly')"
        ))
    })?;
    let len = len.ok_or_else(|| {
        GnomonError::InvalidInput(format!(
            "invalid --slice-frame '{trimmed}': missing required 'len=...' (or use 'readonly')"
        ))
    })?;
    Ok(SliceFrameSpec { mem: mem_id, base, len })
}
