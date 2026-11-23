# Project Gnomon Roadmap & Unified Master Plan

## 1. North Star: Product Architecture

Project Gnomon is a **Verified AI Performance Engineering Engine** targeting native **x86-64 and ARM64** systems code written in **strict `no_std` Rust** (with LLVM/`rustc` trusted for native lowering, and deterministic `wasm32` / `GnomonIR` serving as the tiny, Kani-verified semantic verification layer):

1. **The Foundation — Application Postconditions & State Contracts:**
   - Every systems component starts with its **application contract**: preconditions & data-structure invariants (`requires(s, args)` / `I(s)`), panic/trap-freedom (`!trap`), relational postconditions (`ensures(old_s, new_s, ret)`), inductive invariant preservation (`I(s) ⇒ I(op(s))`), and memory isolation (`MemoryFrame` / `SliceFrame`).
   - Exact functional equivalence (`opt ≡ ref` under `I(s)`) sits cleanly on top of this foundation as a relational postcondition, never generating false counterexamples on unreachable garbage states.
2. **The Targeted Use Case — Closed-Loop Native x64 & ARM64 Performance Optimization:**
   - An AI agent (or engineer) takes a simple, slow reference function (`ref.rs`) + its **application contract** and iteratively synthesizes faster strict `no_std` Rust (`opt.rs`: SWAR bit hacks, branchless transforms, wide loads, division elimination, loop fusion, register-pressure-aware live-range shaping, and SIMD `v128`).
   - Complex nonlinear/stateful pieces are decomposed into **Strata** via auto-generated `strata.rs` bindings (`import "stratum"` → `CallTarget::Stratum`) so `egglog` + Ackermann UF CEGAR discharge proofs in **20–50 ms** instead of hitting Bitwuzla's exponential cliff.
   - A deterministic **Native Performance Oracle (`gnomon profile`)** compiles verified Rust via `rustc -C opt-level=3 --emit=asm` for **both `x86_64` and `aarch64`** and runs **`/usr/lib/llvm-23/bin/llvm-mca`**, returning exact instruction count, estimated cycles/throughput, branch & `div` counts, and **exact LLVM register spill/reload counts** (`[rsp+...]` / `[sp, #...]`) with zero timing jitter.
   - Once `PROVED` and beating the static performance oracle, the exact same strict Rust compiles straight to native x64 & ARM64 binaries (with optional host microbenchmarking for final wall-clock confirmation).

---

## 2. Completed Foundation

- **Phase 1 — Verified Grounded Engine (`phase-1-frozen` → `phase-1-optimized`, `d1bfa2a`):**
  - `#![no_std]` `#![forbid(unsafe_code)]` zero-dependency TCB (`gnomon-kernel`, 24B `IrSlot`, O(1) `Env`/`TypeEnv`, **12/12 Kani proofs green** in `314.52s`, zero stubs/unwindsets).
  - Lossless `.wasm <-> GnomonIR` + `wasmtime` Stage-1 fuzzer (`gnomon-wasm`): **30/30** real `no_std` Wasm round-trip, **30/30** mutants falsified in median **`3.63 ms`**, **0** unsound.
- **Phase 2A — Sieve Consolidation, UF CEGAR, CLI, Single MCP, & Proof 1 (`61e17d3` → `6069a6f`):**
  - `stitch_core` silent MDL admission (`>= 2` solutions) + `egglog` `<= 3`-step law pruning + transitive DAG TCB rebuild + `AutoDoc`.
  - Sound Ackermann **UF Congruence CEGAR** in `gnomon-sieve` (`smt_ir.rs`).
  - `gnomon` CLI (`-t auto|wasm|ir`, files & stdin, `--state`, `gnomon schema`) + single registered stdio `rmcp` MCP server (`~/.gemini/config/mcp_config.json`).
  - **Proof 1 (`proof1_cliff`, 10s cap):** Flat Bitwuzla timed out on **8/10** nonlinear/dual-memory benchmarks (`>10 s`), while Gnomon proved **10/10** in **`22.5 – 505.4 ms`** (`>20x – >445x`) and falsified a 1-bit bug at `N=8` in **`13.27 ms`**.

---

## 3. Critical Scope Boundaries (What We Deliberately Cut/Defer)

- **No x86-64 / ARM64 binary lifters right now:** Because we trust `rustc`/LLVM to compile verified strict Rust to native code, we get exact x64 & ARM64 instruction, cycle, and register-spill feedback via `rustc --emit=asm` + `llvm-mca` (~200 LoC) instead of maintaining 15k+ LoC of ISA decoders. *(Can still be added later if compiler-verification ever becomes a goal.)*
- **No distributed/concurrent temporal logic:** Application state assertions stay focused on deterministic single-threaded data-structure invariants, panic/trap-freedom, relational pre/postconditions, and memory/slice isolation.
- **`.ir` JSON stays as wire/debug format, not the AI authoring language:** AI agents write strict `no_std` Rust using auto-generated `strata.rs` bindings.

---

## 4. Unified 5-Step Execution Plan

| Step | Layer & Priority | Deliverables | Exit Gate |
| --- | --- | --- | --- |
| **Step 1** | **Foundation: Application Postconditions & State Contracts + Strict Rust Strata Bridge** *(Zero TCB churn)* | • **Application Contracts (`gnomon check-contract` CLI + MCP):** First-class verification via existing `Bitwuzla::check_vc` for `(requires(s, args) ⇒ !trap ∧ ensures(old_s, new_s, ret))`, inductive API invariant checks (`init` establishes `I`, every method preserves `I`), and inline `gnomon::assume(c)` / `gnomon::assert(c)` intrinsics.<br>• **Strict Rust → Strata Bridge (`-t rust`):** Lift Wasm `import "stratum" "<op>"` → `CallTarget::Stratum(id)`, auto-generate safe `strata.rs` wrappers (`consolidate --emit-rust`), compile strict `no_std` Rust via `rustc --target wasm32-unknown-unknown`, and emit standalone lowered `.wasm`. | Real strict `no_std` Rust stateful component (e.g., ring buffer / vault / frame codec) proved panic-free + invariant-preserving + postcondition-valid via `check-contract`, AND multi-layer Strata composed in 100% strict Rust (zero hand-written `.ir` JSON). |
| **Step 2** | **Targeted Use Case: Native x64 & ARM64 Performance Oracle (`gnomon profile`) + Closed-Loop Optimization Demo** *(Zero TCB churn)* | • **`gnomon profile` (CLI + MCP):** Compiles strict `no_std` Rust via `rustc -C opt-level=3 --emit=asm` for `x86_64` and `aarch64` (`rustup target add aarch64-unknown-linux-gnu`), parses assembly for **instruction count, branch count, `div` count, and LLVM register spill/reload count**, and runs `/usr/lib/llvm-23/bin/llvm-mca` (`skylake`/`znver4` + `neoverse-v2`/`apple-m3`) for deterministic cycles & reciprocal throughput (plus Wasm/IR instruction proxy & optional host microbenchmark).<br>• **Live Closed-Loop AI Demo:** Give a blind AI agent slow `ref.rs` kernels (ASCII/delimiter SWAR scanner, varint/endian codec, Barrett div-elimination, pipelined `fmix64`) + application contracts and observe it hill-climb verified x64/ARM64 speedups! | Blind AI agent produces `PROVED` (contract + `opt ≡ ref`) optimized Rust kernels with measured drops in x64 & ARM64 `llvm-mca` cycles, instructions, branches, and **0 register spills**, confirmed by host microbenchmark. |
| **Step 3** | **Real-World Rust Slices (`__stack_pointer` Shadow-Stack + `SliceFrame`) & `wasm-smith` Blowup Fuzzer** *(Zero TCB churn)* | • **Shadow-Stack Refinement (`--ignore-dead-stack` / `--ignore-scratch-mem`):** Ignore dead dirty bytes below `__stack_pointer` (`Global(0)`) while asserting `SP_out == SP_in`, unblocking real `rustc` functions using `&[u8]`, `&mut [u8]`, and local stack arrays/structs.<br>• **Intra-Memory `SliceFrame`:** Prove disjoint `[base_a, base_a+len_a)` vs `[base_b, base_b+len_b)` non-interference inside a single linear memory.<br>• **`wasm-smith` Differential & Blowup Fuzzer + Static Cliff Estimator:** Fuzz `lift → emit → egglog → smt_ir` with tight latency/node ceilings; add static SMT-cliff warnings to `lift`/`check-goal`. | Real `rustc` slice functions with local stack arrays prove equivalent to zero-allocation optimizations; `>= 1,000` random `wasm-smith` modules pass with `0` crashes, `0` blowups, and `0` semantic mismatches. |
| **Step 4** | **TCB v2: IEEE-754 Floating Point (`f32`/`f64` → `QF_ABVFP`) + Portable SIMD (`v128`)** *(One clean TCB upgrade + Kani re-verify)* | • **`gnomon-kernel`:** Add `ValType::{F32, F64, V128}`, raw-bit deterministic FP + `v128` lane ops (keeping `IrSlot` compact and `#![no_std]`).<br>• **`gnomon-wasm`:** Lift/emit MVP + `trunc_sat` FP and `v128` SIMD + FP/SIMD Stage-1 corner-case fuzzing (`±0.0`, subnormals, `±Inf`, `qNaN`/`sNaN`, lane boundaries).<br>• **`gnomon-sieve`:** Native Bitwuzla `QF_ABVFP` + `BV128` + strictly IEEE-safe `egglog` rules.<br>• Verified `v128` Rust kernels compile straight to x64 SSE/AVX and ARM64 NEON via `rustc -O3`! | **15+/15+ Kani harnesses green** (adding FP NaN/trap & `v128` lane proofs), `>= 10,000` FP + SIMD differential checks vs `wasmtime`, and a verified `v128` SIMD optimization delivering measured x64/ARM64 speedup. |
| **Step 5** | **Proof 2 — Compute-Matched 3-Arm Agentic Optimization Benchmark (`gnomon-bench`)** | • Token- & wall-clock-matched ablation across progressive real-world optimization tasks (nonlinear integer, stateful contracts, slice parsers, FP, `v128` SIMD):<br>  - **Arm A:** Flat Rust + fast feedback (no Strata)<br>  - **Arm B:** Rust helper functions only (inlined to Layer 0, no proved laws)<br>  - **Arm C:** Full Gnomon (`check-contract` + `strata.rs` + `prove-law` + `egglog` + UF CEGAR + `profile` + `consolidate`) | Arm C beats compute-matched Arms A & B by `>= 2.0x` on held-out cliff tasks (`pass@8` + verified x64/ARM64 `llvm-mca`/host speedup), `>= 5.0x` median SMT speedup, `>= 30%` cross-task law reuse, `0` unsound admissions. |
