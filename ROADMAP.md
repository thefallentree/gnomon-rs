# Project Gnomon Roadmap & Unified Step Plan

## 1. Completed Foundation

- **Phase 1 — Verified Grounded Engine (`phase-1-frozen` → `phase-1-optimized`, `d1bfa2a`):**
  - `#![no_std]` `#![forbid(unsafe_code)]` zero-dependency TCB (`gnomon-kernel`, 24B `IrSlot`, O(1) `Env`/`TypeEnv`, **12/12 Kani proofs green** in `314.52s`, zero stubs/unwindsets).
  - Lossless `.wasm <-> GnomonIR` + `wasmtime` Stage-1 fuzzer (`gnomon-wasm`): **30/30** real `no_std` Wasm round-trip, **30/30** mutants falsified in median **`3.63 ms`**, **0** unsound.
- **Phase 2A — Sieve Consolidation, UF CEGAR, CLI, MCP, & Proof 1 (`61e17d3` → `6069a6f`):**
  - `stitch_core` silent MDL admission (`>= 2` solutions) + `egglog` `<= 3`-step law pruning + transitive DAG TCB rebuild + `AutoDoc`.
  - Sound Ackermann **UF Congruence CEGAR** in `gnomon-sieve` (`smt_ir.rs`).
  - `gnomon` CLI (`-t auto|wasm|ir`, files & stdin, `--state`, `gnomon schema`) + single registered stdio `rmcp` MCP server (`~/.gemini/config/mcp_config.json`).
  - **Proof 1 (`proof1_cliff`, 10s cap):** Flat Bitwuzla timed out on **8/10** nonlinear/dual-memory benchmarks (`>10 s`), while Gnomon proved **10/10** in **`22.5 – 505.4 ms`** (`>20x – >445x`) and falsified a 1-bit bug at `N=8` in **`13.27 ms`**.

---

## 2. Key Architectural Decision: What Should AI Agents Write? (Strict Rust vs. Raw Strata `.ir`)

**Recommendation: AI agents should write strict `no_std` Rust — NEVER hand-author `.ir` JSON in normal workflows — while Gnomon preserves exact Strata boundaries across compilation.**

### Why Not Hand-Authored `.ir` JSON?
- Writing raw SSA `.ir` JSON is verbose (10× more tokens than Rust), alien to LLM pretraining, prone to manual `ValId` numbering bugs, and produces artifacts humans cannot maintain in a real repository.

### Why Not Plain Rust Alone?
- If an AI writes normal Rust helper functions and compiles with `rustc --target wasm32-unknown-unknown`, LLVM **inlines** the helpers into flat Layer-0 Wasm — erasing the Stratum call boundaries so `egglog` and UF CEGAR can no longer see `CallTarget::Stratum` and Bitwuzla hits the exponential cliff again.

### The Best of Both Worlds: Strict `no_std` Rust + Auto-Generated `strata.rs` Bindings
1. **Defining a Stratum:** The AI writes a normal strict `no_std` Rust function (`#[unsafe(no_mangle)] pub extern "C" fn fmix64(x: u64) -> u64 { ... }`), compiled to `.wasm` via `rustc --target wasm32-unknown-unknown` (or `-t rust` in `gnomon`), and registers it with `gnomon define-op`.
2. **Calling Strata from Higher Layers & Laws (Zero Inlining Loss!):** `gnomon consolidate` / `define-op` auto-generates a tiny safe `strata.rs` binding module wrapping `#[link(wasm_import_module = "stratum")] extern "C" { fn fmix64(x: u64) -> u64; }`.
   - LLVM **cannot** inline Wasm `"stratum"` imports, so the compiled `.wasm` retains exact Layer-$k$ call boundaries.
   - `gnomon-mcp` / `gnomon-wasm` resolves `import "stratum" "<name>"` directly into `CallTarget::Stratum(StratumId)` during lifting!
   - Law LHS/RHS, preconditions, and `InvariantLoop` annotations (`gnomon_invariant(cond)`, `gnomon_fuel(measure)`) are all written as **ordinary `rustc`-typechecked Rust functions**.
3. **Shipping Real Code:** Once verified, Gnomon either lowers `CallTarget::Stratum` back to a standalone `.wasm` binary (`lower_region_to_layer0 → emit_wasm`) or links the verified Rust crate directly for production.
4. **`.ir` JSON stays as the lossless wire/inspection format** underneath (and remains supported via `-t ir`), rather than the primary authoring language for AI agents.

---

## 3. Unified Master Step Plan

| Step | Scope & Goal | Key Technical Deliverables | Exit Gate |
| --- | --- | --- | --- |
| **Step 1** | **Strict Rust Front-End for Strata (`-t rust` + `strata.rs` bridge)** *(Zero TCB churn)* | • Map Wasm imports from module `"stratum"` (`import "stratum" "<op_name>"`) to `CallTarget::Stratum(id)` in `gnomon-mcp` engine.<br>• Add `gnomon consolidate --emit-rust <strata.rs>` generating safe `no_std` Rust wrappers + docstrings for all active Strata.<br>• Add `-t rust` input support in `gnomon` CLI/MCP invoking `rustc --target wasm32-unknown-unknown` cleanly (with deterministic flags & zero-inline Stratum imports), plus `gnomon emit-wasm` to link/lower verified Strata into a standalone `.wasm`. | Blind AI subagent solves a nonlinear multi-layer problem (like `fmix64` + dual-memory ring) writing **100% strict `no_std` Rust** (zero hand-written `.ir` JSON), with `egglog` + UF CEGAR firing and standalone `.wasm` emitted. |
| **Step 2** | **`wasm-smith` Differential & Blowup-Detector Fuzzer + Static Cliff Diagnostics** *(Zero TCB churn)* | • Add a `wasm-smith` property/fuzz test suite in `gnomon-wasm`/`gnomon-sieve` generating thousands of random valid supported `.wasm` modules and asserting: (a) `lift → emit → wasmtime == gnomon-kernel`, (b) `egglog` equivalence soundness, (c) strict latency & node ceilings on `lift`, `egglog`, and `smt_ir` encoding to catch hidden exponential blowups.<br>• Add a static SMT-cliff risk estimator to `gnomon lift` / `check-goal` (nonlinear `mul`/`div` depth, symbolic `Store` count, `IfElse` diamond fanout) that warns agents *before* timeout and recommends Strata decomposition. | `>= 1,000` random `wasm-smith` modules pass differential soundness + latency/node blowup budgets with `0` crashes, `0` hangs, and `0` semantic mismatches. |
| **Step 3** | **Register Spilling & Multi-Memory `SliceFrame`** *(Zero TCB churn)* | • **Spill-Refinement Equivalence (`--ignore-scratch-mem <MemId>`):** Verify spilled candidate (`MemId(SPILL)` + `GlobalId(SP)`) matches virtual-SSA ref on all outputs, traps, globals, and user memories `MemId(0..k)` while optionally proving `SP_out == SP_in` and `MemoryFrame` isolation of user heap.<br>• **Intra-Memory `SliceFrame`:** Prove disjoint `[base_a, base_a+len_a)` vs `[base_b, base_b+len_b)` non-interference *within* the same `MemId` (for spill slots, single-memory arenas, partitioned shared SRAM).<br>• **Spilled-Kernel Cliff Benchmark:** High-pressure spilled nonlinear kernel vs SSA ref proved in ms via spill-forwarding Strata + UF CEGAR; injected spill-slot aliasing bug falsified in `< 15 ms`. | Spilled nonlinear kernel equivalence proved in `< 100 ms` where flat Bitwuzla times out; slot-aliasing & missing-restore bugs falsified with concrete counterexamples. |
| **Step 4** | **IEEE-754 Floating Point (`f32`/`f64` → `QF_ABVFP`)** *(Controlled TCB v2 extension)* | • **`gnomon-kernel`:** Add `ValType::{F32, F64}`, bit-exact `Val::{F32(u32), F64(u64)}`, Wasm MVP + `trunc_sat` FP ops, and `reinterpret` casts while keeping `IrSlot <= 24 B` and `#![no_std]`.<br>• **`gnomon-wasm`:** Lift/emit all Wasm FP instructions + Stage-1 FP boundary vectors (`±0.0`, subnormals, `±Inf`, `qNaN`/`sNaN`, `trunc` trap boundaries).<br>• **`gnomon-sieve`:** Upgrade `SmtTarget` to native Bitwuzla `QF_ABVFP` (`mk_fp_sort`, `RoundingMode::Rne`) + strictly IEEE-safe `egglog` rules (`neg(neg(x))`, `abs(abs(x))`, `reinterpret`, never unsound FP associativity). | **14/14 Kani harnesses green** (adding FP NaN canonicalization & `trunc` trap proofs), `>= 10,000` FP differential checks vs `wasmtime`, and `QF_ABVFP` equivalence + counterexample tests passing. |
| **Step 5** | **Wasm SIMD (`v128`), `memory64`, & Deterministic SIMT / GPU Kernels** *(TCB v3 extension)* | • Add `v128` lane-typed vector ops (`i8x16`, `i16x8`, `i32x4`, `i64x2`, `f32x4`, `f64x2`, `v128.load`/`store`, `shuffle`/`swizzle`) mapped to `BV128` / lane terms in Bitwuzla + Cranelift SIMD fuzzing.<br>• Add `memory64` (`Array<BV64, BV8>`) and a fixed-grid SIMT kernel model (`tid`, `bid`, `MemId(0)` shared SRAM, `MemId(1)` global HBM, `MemId(2)` local spill stack). | Verify a vectorized + spilled + tiled SIMT kernel against a scalar reference spec via Strata + `SliceFrame`/`MemoryFrame` + UF CEGAR, with Kani + `wasm-smith` SIMD tests green. |
| **Step 6** | **Proof 2 — Compute-Matched 3-Arm Agentic Ablation (`gnomon-bench`)** | • Run a strictly **token- & wall-clock-matched** 3-arm ablation where AI agents write **strict `no_std` Rust** across progressive cliff tasks (nonlinear integer, IEEE-754 FP, multi-memory, register-spilled, SIMD/tiled kernels):<br>  - **Arm A:** Flat Rust + fast Wasmtime/Bitwuzla feedback (no Strata)<br>  - **Arm B:** Rust helper macros only (inlined to Layer 0, no proved laws)<br>  - **Arm C:** Full Gnomon (`strata.rs` + `prove-law` + `egglog` + UF CEGAR + `consolidate`) | Arm C achieves `>= 2.0x` held-out Rung-4 `pass@8` at matched compute over Arms A & B, `>= 5.0x` median SMT speedup, `>= 30%` cross-task law firing, and `0` unsound admissions. |
