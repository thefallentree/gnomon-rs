# Project Gnomon Roadmap & Next Plan

## 1. Completed Milestones

- **Phase 1 — Verified Grounded Engine (`phase-1-frozen` → `phase-1-optimized`, `d1bfa2a`):**
  - `#![no_std]` `#![forbid(unsafe_code)]` zero-dependency TCB (`gnomon-kernel`) with 24-byte `IrSlot`, O(1) direct-indexed `Env`/`TypeEnv`, deterministic small-step evaluator, 3-way `InvariantLoop` VC splitter, and `StratumRegistry` admission gate.
  - **12/12 Kani proof harnesses verified green** (`0` failures, `314.52s` total, zero stubs/unwindsets).
  - Lossless `.wasm <-> GnomonIR` lifter/emitter + `wasmtime` Cranelift Stage-1 fuzzer (`gnomon-wasm`).
  - `egglog` v3.0 regional simplifier + `Bitwuzla` 0.11 `QF_ABV` native & persistent-pipe backends (`gnomon-sieve`).
  - Phase 1 Exit Gate (`phase1_gate`): **30/30** round-trip, **30/30** mutants falsified, median **`3.63 ms`**, **0** unsound.
- **Phase 2A — Sieve Consolidation, UF CEGAR, CLI, Single MCP, & Proof 1 (`61e17d3` → `3c34fe1`):**
  - `stitch_core` silent MDL admission (`>= 2` solutions) + `egglog` `<= 3`-step law non-redundancy + transitive DAG rebuild + compact `AutoDoc`.
  - Sound Ackermann **UF Congruence CEGAR** in `gnomon-sieve` (`smt_ir.rs`).
  - `gnomon` CLI (`-t auto|wasm|ir`, files & stdin, `--state`, `gnomon schema`) + single registered stdio `rmcp` MCP server (`~/.gemini/config/mcp_config.json`) exposing all 6 atomic tools, verified by CLI/MCP E2E tests and a live blind-agent synthesis demo.
  - **Proof 1 (`proof1_cliff`):** Flat Bitwuzla timed out on **8/10** nonlinear/dual-memory benchmarks (`>10 s`), while Gnomon proved **10/10** in **`22.5 – 505.4 ms`** (`>20x – >445x`), catching an injected 1-bit bug in **`13.27 ms`**.

---

## 2. Priority Capability Roadmap (Phase 3 Foundations + Phase 2B Proof)

To move from integer linear-memory systems code into real-world compilers, ML/DSP/SIMD kernels, and GPU/accelerator lowering, four core capabilities are prioritized:

### Pillar A: IEEE-754 Floating Point (`f32` / `f64` → `QF_ABVFP`)
**Why:** Scientific computing, audio/video codecs, graphics, quantitative finance, and ML/GPU kernels all rely on IEEE-754 `f32`/`f64` — where NaN propagation, `-0.0` vs `+0.0`, subnormals, and non-associativity cause subtle optimizer bugs that tests miss.
- **`gnomon-kernel`:** Add `ValType::{F32, F64}`, `Val::{F32(u32), F64(u64)}` (storing raw IEEE-754 bit patterns so `#![no_std]` determinism and exact bit-level `PartialEq` stay clean for Kani!), `Op::{ConstF32, ConstF64}`, FP `UnOp` (`abs`, `neg`, `ceil`, `floor`, `trunc`, `nearest`, `sqrt`, `promote`/`demote`, `convert_i32/i64_{s,u}`, trapping `trunc_f32/f64_{s,u}`, saturating `trunc_sat_*`, `reinterpret_*`), and FP `BinOp` (`add`, `sub`, `mul`, `div`, `min`, `max`, `copysign`, `eq`, `ne`, `lt`, `gt`, `le`, `ge`).
- **`gnomon-wasm`:** Lift/emit all Wasm MVP + `nontrapping-float-to-int-conversions` FP instructions and extend Stage-1 boundary vectors with `±0.0`, `±1.0`, subnormals (`MIN_POSITIVE / 2`), `±MAX`, `±Inf`, canonical `qNaN`, signaling `sNaN`, and rounding ties-to-even boundaries.
- **`gnomon-sieve`:** Upgrade `SmtTarget` to `QF_ABVFP` using Bitwuzla 0.11's native IEEE-754 floating-point theory (`mk_fp_sort(8, 24)` / `mk_fp_sort(11, 53)`, `Kind::FpAdd`, `FpFma`, `FpToSbv`, `FpToIeeeBv`, `RoundingMode::Rne`). Add **strictly IEEE-sound** `egglog` FP rules (e.g., `neg(neg(x)) == x`, `abs(abs(x)) == abs(x)`, `reinterpret` round-trips — NEVER unsound algebraic associativity unless explicitly gated by a proved finite/fast-math precondition!).
- **Kani proofs:** Add harnesses verifying Wasm deterministic NaN canonicalization, `trunc` `IntOverflow` / `InvalidConversionToInteger` traps, and `reinterpret` bit-exactness.

### Pillar B: Advanced Multi-Memory & Disjoint-Slice Isolation
**Why:** Gnomon already has multi-memory `MemId(u16)`, cross-memory `memory.copy`/`fill`/`grow`, `u64` effective-address bounds, and `MemoryFrame { untouched_mem }` laws. Real kernels and multi-tenant sandboxes need two next-level extensions:
1. **Intra-Memory Disjoint-Slice Frame Laws (`SliceFrame`):** Prove that a write to `[base_a, base_a + len_a)` inside `MemId(m)` leaves reads in `[base_b, base_b + len_b)` of the *same* `MemId(m)` untouched whenever disjointness holds (essential for single-memory Wasm arenas, ring buffers, and partitioned GPU shared memory!).
2. **Memory-Space Roles & `memory64`:** Support 64-bit linear memories (`memory64` / `Array<BV64, BV8>`) and explicit memory-space attributes (User Heap, Host/Control Plane, Shared SRAM, Spill Stack) so `egglog` and `prove-law` apply cross-space frame isolation automatically.

### Pillar C: Register Spilling & Lowered Stack-Frame Verification
**Why:** Register allocation and spilling (in Cranelift, LLVM, and GPU PTX/AMDGPU backends) are a notorious source of silent miscompilations: clobbered spill slots, overlapping live ranges, misaligned stack offsets, and bad rematerialization.
- **Dedicated Spill Memory Model:** Represent spilled registers in a dedicated `MemId(SPILL)` memory (completely disjoint from user memories `MemId(0..k)` via `MemoryFrame`!) paired with a stack-pointer global (`GlobalId(SP)`).
- **Spill-Refinement Equivalence Mode (`--ignore-dead-mem SPILL`):** Extend `check_equivalence` / `check-goal` to verify that a register-allocated + spilled candidate matches a virtual-SSA reference on **all return values, traps, globals, and user memories `MemId(0..k)`** while allowing dead scratch state in `MemId(SPILL)` (optionally asserting stack-pointer restoration `SP_out == SP_in`).
- **Spill Strata & `egglog` Forwarding Laws:** Define reusable `spill_save(slot, val)` / `spill_reload(slot)` Strata with proved slot-disjointness (`slot_a != slot_b`) and store-to-load forwarding laws so `egglog` cancels spill round-trips *before* Bitwuzla sees the spill array, preventing `QF_ABV` Ackermann blowup on high-pressure kernels.
- **Kani / E2E Coverage:** Prove spill non-interference against user heap and falsify classic compiler bugs (aliased spill slot reuse, missing callee-save restore, off-by-one frame offset).

### Pillar D: Wasm SIMD (`v128`) & Deterministic SIMT / GPU Kernels
- **Wasm SIMD (`v128`):** Lane-typed vector ops (`i8x16`, `i16x8`, `i32x4`, `i64x2`, `f32x4`, `f64x2`, `v128.load`/`store`, `swizzle`/`shuffle`) mapped to `BV128` / lane-packed Bitwuzla terms + Cranelift SIMD Stage-1 fuzzing.
- **Deterministic SIMT Kernels:** Model warp/block execution via explicit `(tid, bid)` parameters, shared SRAM (`MemId(0)`), global HBM (`MemId(1)`), and local register-spill memory (`MemId(2)`), using UF CEGAR + `MemoryFrame`/`SliceFrame` to verify tiled/fused GPU kernels against scalar reference specs.

### Pillar E: Proof 2 — Compute-Matched 3-Arm LLM Flywheel Benchmark (`gnomon-bench`)
- Build the controlled 60-task 4-rung ablation (Arm A: flat + fast feedback, Arm B: macros only, Arm C: Gnomon Strata + `egglog` + UF CEGAR + `consolidate`) under strictly matched token & wall-clock budgets, anchored directly on cliff tasks from Proof 1 + FP/multi-memory/register-spilling tasks.

---

## 3. Proposed Next Execution Plan (Recommended Sequence)

| Step | Focus | Concrete Deliverable & Exit Gate |
| --- | --- | --- |
| **Step 1** | **Register Spilling + Multi-Memory `SliceFrame` (Zero TCB churn first!)** | Add `ignore_scratch_mems` (spill-refinement equivalence) + intra-memory `SliceFrame` non-interference in `gnomon-sieve` & `gnomon-mcp`; build a real spilled vs SSA kernel benchmark (including a high-register-pressure nonlinear kernel + injected slot-aliasing bug) proving spill verification works in ms. |
| **Step 2** | **IEEE-754 Floating Point (`f32`/`f64` → `QF_ABVFP`)** | Extend `gnomon-kernel` (`IrSlot` stays `<= 24B`!), `gnomon-wasm` (MVP + saturating FP), `gnomon-sieve` (`Bitwuzla` `QF_ABVFP` + IEEE-safe `egglog`), `gnomon-mcp` (`.ir` codec), and add Kani FP trap/NaN harnesses + FP differential fuzzing (`>= 10,000` vectors). |
| **Step 3** | **Wasm SIMD (`v128`) & Multi-Memory `memory64` / GPU Kernel Prototype** | Add `v128` integer + FP lanes + tiled SIMT kernel example (scalar ref vs vectorized + spilled + shared-memory tiled candidate proved equivalent via Strata + UF CEGAR). |
| **Step 4** | **Proof 2 — Compute-Matched 3-Arm Agentic Ablation** | Run token- & time-matched Arm A / B / C ablation across progressive rungs (including nonlinear, FP, multi-memory, and spilled kernels) and publish the full empirical scorecard. |
