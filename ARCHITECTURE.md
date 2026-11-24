# Project Gnomon (`gnomon-rs`) Architecture & Audited Environment

## 1. Audited Build & Verification Environment

| Component | Exact Version / Detail | Notes |
| --- | --- | --- |
| **OS** | Ubuntu 22.04.5 LTS (`jammy`), `x86_64` | `glibc 2.35` |
| **CPU** | Intel Xeon Gold 6132 @ 2.60 GHz (8 cores) | `avx2`, `avx512*`, `bmi1`, `bmi2`, `popcnt` |
| **Memory / Disk** | 23 GiB RAM, 275 GiB free | — |
| **Rust Compiler** | `rustc 1.100.0` (bundled LLVM `23.1.5`) | Edition `2024`, Resolver `2` |
| **Rust Targets** | `x86_64-unknown-linux-gnu`, `wasm32-unknown-unknown` | Includes `clippy`, `rustfmt`; ARM64 lowering via LLVM-23 `llc` + `llvm-mca` |
| **Kani Verifier** | `Kani Rust Verifier 0.68.0` / `CBMC 6.11.0` | **15/15** TCB v2 harnesses verified green (`0` failures, `11m54.38s` total, `0` stubs/unwindsets) |
| **Bitwuzla SMT** | `0.11.0` (source-built static release) | `QF_ABVFP` + `BV128`; static PIC `GMP 6.3.0` + `MPFR 4.2.1` in `~/.local/bitwuzla` |
| **C/C++ & LLVM** | `clang 23.0.0`, `llvm-23` (`llc`, `llvm-mca`), `cmake`, `meson`, `ninja`, `pkg-config` | `libclang-23` (`/usr/lib/llvm-23/lib`) used by `bindgen`; `llvm-mca` used by `gnomon profile` |

### Required Environment Variables
```bash
export PATH="/usr/lib/llvm-23/bin:$HOME/.cargo/bin:$HOME/.local/bitwuzla/bin:$HOME/.local/bin:$PATH"
export PKG_CONFIG_PATH="$HOME/.local/bitwuzla/lib/pkgconfig${PKG_CONFIG_PATH:+:$PKG_CONFIG_PATH}"
export LIBCLANG_PATH="/usr/lib/llvm-23/lib"
export CC="/usr/lib/llvm-23/bin/clang"
export CXX="/usr/lib/llvm-23/bin/clang++"
```

### Locked Workspace Crate Versions (`Cargo.toml`)
- `wasmparser = "0.263.0"`, `wasm-encoder = "0.263.0"`, `wasm-smith = "0.263.0"`, `wasmtime = "51.0.0"`, `arbitrary = "1.5.0"`
- `egglog = "3.0.0"`, `bitwuzla = { version = "0.11.0", features = ["static"] }`, `stitch_core = "0.1.0"`
- `rmcp = "3.11.0"`, `tokio = "1.54.1"`, `serde = "1.0.229"`, `serde_json = "1.0.154"`, `schemars = "1"`, `clap = "4"`, `sha2 = "0.10"`, `base64 = "0.22"`, `thiserror = "2.0.21"`, `proptest = "1.12.0"`

---

## 2. Immutable Architectural Invariants

1. **De Bruijn Separation of Trust (TCB v2):**
   - **Trusted Computing Base (`crates/gnomon-kernel`):** `#![no_std]` (+ `alloc`), `#![forbid(unsafe_code)]`, **0** runtime dependencies. Contains ONLY the flat **24-byte `IrSlot`** (`Copy`, `!needs_drop`) arena `GnomonIR` data model, O(1) direct-indexed `Env`/`TypeEnv`, pure `#![no_std]` deterministic IEEE-754 + `v128` semantics (`src/fp.rs`), small-step reference interpreter, 3-way `InvariantLoop` VC splitter, `StratumRegistry` admission checker, and **15 `#[cfg(kani)]` verification harnesses** (`0` stubs, `0` `--unwindset`, `0` `ManuallyDrop`/`mem::forget`, `0` `#[cfg(kani)]` shims outside `src/lib.rs:13`).
   - **Untrusted High-Speed Search & Tooling (`gnomon-wasm`, `gnomon-sieve`, `gnomon-mcp`, `gnomon-bench`):** 100% Safe Rust (`unsafe_code = "forbid"` workspace-wide) optimized for Cranelift JIT falsification (`wasmtime 51`), bounded `egglog` v3.0 equality saturation, `Bitwuzla` `QF_ABVFP` SMT proving + Ackermann UF congruence CEGAR, `stitch_core` silent MDL compression, strict Rust Strata compilation (`-t rust`), and native x64/ARM64 hardware profiling (`gnomon profile`). Every admitted Stratum passes through `gnomon-kernel::StratumRegistry::promote_stratum`.
2. **Exact Deterministic Wasm Semantics (Zero Toy Shortcuts):**
   - **Types & Ops:** 5 `ValType`s (`I32`, `I64`, `F32`, `F64`, `V128`), 5 `MemWidth`s (`B1`, `B2`, `B4`, `B8`, `B16`), 8 `LaneKind`s, **100** dense `UnOp`s, **141** dense `BinOp`s, **17** `Op` variants (including `ConstF32`/`ConstF64`/`ConstV128`, `SimdExtractLane`, `SimdReplaceLane`, `SimdBitselect`, `SimdShuffle`).
   - **Integer & Trap Determinism:** Two's-complement `i32`/`i64` wrapping arithmetic and explicit deterministic traps (`DivByZero`, `IntOverflow`, `OutOfBoundsMem`, `OutOfFuel`, `HostContractViolation`, `Unreachable`). `div_s(MIN, -1)` traps `IntOverflow`; `rem_s(MIN, -1)` yields `0`; effective address `addr + offset` checks in `u64` prevent 32-bit wrap-around memory escapes.
   - **IEEE-754 FP & `v128` SIMD Determinism (`fp.rs`):** Wasm canonical quiet NaN (`0x7fc0_0000` / `0x7ff8_0000_0000_0000`), payload-preserving `abs`/`neg`/`copysign`/`pmin`/`pmax`, `-0.0`-preserving bit-level `ceil`/`floor`/`trunc`/`nearest` (RNE), exact integer-sqrt, exact Wasm trapping `trunc` vs trap-free `trunc_sat`. Verified across **27,768** 3-way differential checks vs `wasmtime` (incl. **13,896** FP/SIMD corner cases, `0` mismatches).
   - **Memory, Stack & Slice Isolation:** Multi-memory isolation (`MemId(u16)`) maps 1:1 to independent SMT `Array<BV32, BV8>` instances; `--ignore-dead-stack` proves `SP_out == SP_in` on `Global(0)` while ignoring dead bytes below `SP_in`; `--slice-frame` proves intra-memory write containment (`readonly` or `base`/`len` byte windows).
3. **Paired Sub-Abstractions ("Strata"):**
   - Every promoted `Stratum` at Layer `k >= 1` bundles:
     1. A named typed `StratumOp` defined strictly as an acyclic composition over Layer `0 .. k-1` ops (authored in strict `#![no_std]` Rust via `#[link(wasm_import_module = "stratum")]` → `CallTarget::Stratum`, or `.wasm`/`.ir`).
     2. At least one non-empty machine-proved `Law` (`Algebraic` or unconditional `MemoryFrame { untouched_mem }` verified directly over `target_op.body` for both `MemorySize` and all in-bounds `u64`-guarded bytes) with non-zero SHA-256 `proof_digest`.
4. **Verification & Optimization Pipeline:**
   - **Stage 1 (`gnomon-wasm`):** `wasmtime 51` Cranelift JIT differential fuzzer (`.wasm_simd(true)` + `.cranelift_nan_canonicalization(true)`, `< 5 ms` concrete counterexamples).
   - **Stage 2a (`gnomon-sieve`):** Bounded `egglog` v3.0 rewrite saturation (`<= 5` iters, `<= 5,000` nodes) firing proved algebraic & `MemoryFrame` Strata laws + sound Ackermann Uninterpreted-Function (UF) congruence CEGAR for shared pure-total Strata + static SMT-cliff estimator (`cliff.rs`).
   - **Stage 2b (`gnomon-sieve`):** Exact `Bitwuzla` `QF_ABVFP` + `BV128` solver (in-process native API + zero-respawn SMT-LIB2 pipe backend) supporting equivalence (`check-goal`), pre/post/inductive/inline contracts (`check-contract`), `--ignore-dead-stack`, and `--slice-frame`.
   - **Stage 3 (`gnomon-kernel`):** SHA-256 `proof_digest` computation + TCB `promote_stratum` admission.
   - **Consolidation (`gnomon-sieve::consolidate`):** `stitch_core` silent `rewrite_with_invention` MDL scoring across `>= 2` verified solutions + `egglog` `<= 3`-step law non-redundancy pruning + transitive DAG closure + fresh TCB `promote_stratum` rebuild + compact `AutoDoc` export.
   - **Native Performance Oracle (`gnomon-mcp::profiler`):** Compiles strict `#![no_std]` Rust to native `x86_64` (`rustc -C opt-level=3 --emit=asm`) and `aarch64` (`rustc --emit=llvm-ir` → LLVM-23 `llc -O3 -mtriple=aarch64-unknown-linux-gnu`), analyzes via `llvm-mca` (`skylake` / `neoverse-v2`) with exact instruction, branch, hardware `div`/`udiv`, stack frame, register spill/reload, and SSE/AVX/NEON SIMD counters, plus opt-in 1M-iteration native host microbenchmark (`--bench`).

---

## 3. Workspace Layout & Crate Contracts

```text
gnomon-rs/
├── Cargo.toml                  # Workspace manifest, forbidden unsafe_code, locked deps
├── README.md                   # Overview, measured benchmark tables, CLI/MCP quickstart
├── ARCHITECTURE.md             # Audited environment, TCB v2 invariants, crate contracts
├── ROADMAP.md                  # Completed 6-step execution report & measured tables
├── AGENTS.md                   # Engineering & verification instructions for AI agents
├── crates/
│   ├── gnomon-kernel/          # [TCB v2] #![no_std] IR (24B IrSlot), fp.rs, eval, VC, registry, 15 Kani proofs (14 tests)
│   ├── gnomon-wasm/            # Lossless wasm <-> GnomonIR (i32/i64/f32/f64/v128) + wasmtime fuzzer (14 tests, 27,768 checks)
│   ├── gnomon-sieve/           # egglog v3.0 + Bitwuzla QF_ABVFP + Ackermann UF CEGAR + cliff + stitch_core (34 tests)
│   ├── gnomon-mcp/             # Codec, rust_bridge (-t rust), profiler (x64/ARM64), CLI, 8-tool MCP server (32 tests)
│   └── gnomon-bench/           # phase1_gate, proof1_cliff, wasm_smith_fuzz (1,000 mods), proof2_oms_ablation (9 tests)
└── examples/
    ├── oms_strata/             # 15 OMS Strata (S1.1-S4.2) + S4.3 6 perf pairs + 11 *_buggy.rs files + build.sh (27 .rs files)
    └── vertical_packs/         # 4 non-trading packs: AI Q8_0, Parquet varint, WireGuard replay, Cloud quota saga (8 .rs files)
```

### Public Crate Contracts
- **`gnomon-kernel` (14 unit/prop tests + 15 Kani harnesses):** `ir` (`IrSlot` 24B, `SlotPool`, `Region`, `Module`, `ValType`/`Val` 5 types, `MemWidth` `B1..B16`, `LaneKind` 8, `UnOp` 100, `BinOp` 141, `Op` 17, `MemId`, `HostContract`), `fp` (`#![no_std]` IEEE-754 & `v128` semantics), `eval` (`HeapState`, `eval_func`, `eval_region`), `vc` (`LoopVcs`, `VcObligation`, `split_invariant_loop`, `eval_vc`, `validate_read_only_with_registry`), `registry` (`Law`, `LawKind`, `StratumOp`, `Stratum`, `StratumRegistry`).
- **`gnomon-wasm` (14 tests, 27,768 3-way checks):** `lift_wasm`, `emit_wasm`, `fuzz_equivalence`, `verify_round_trip`, `differential_check` (full `i32`/`i64`/`f32`/`f64`/`v128` coverage).
- **`gnomon-sieve` (34 tests):** `SmtBackend`, `BitwuzlaNativeBackend`, `BitwuzlaPipeBackend`, `EgglogSimplifier`, `estimate_smt_cliff`, `estimate_region_cliff`, `consolidate_registry`, `discover_candidate_inventions`, `encode_region_as_stitch_expr`, `render_autodoc`.
- **`gnomon-mcp` (32 tests):** `GnomonEngine`, `GnomonMcpServer`, `IrDocument`, `InputType` (`Auto | Wasm | Ir | Rust`), `rust_bridge` (`compile_rust_to_wasm_with_registry`, `generate_strata_rs`, `lower_module_strata`), `profiler` (`profile_rust`, `ProfileArch`, `DEFAULT_X64_CPU = "skylake"`, `DEFAULT_ARM64_CPU = "neoverse-v2"`), `MCP_TOOL_NAMES` (**8 tools**: `gnomon_lift_check`, `gnomon_run_trace`, `gnomon_define_op`, `gnomon_prove_law`, `gnomon_check_goal`, `gnomon_check_contract`, `gnomon_consolidate`, `gnomon_profile`), and `gnomon` CLI binary (`lift`, `trace`, `define-op`, `prove-law`, `check-goal`, `check-contract`, `consolidate`, `emit-rust`, `profile`, `mcp`, `schema`).
- **`gnomon-bench` (9 tests):** `phase1_gate` (30+30 corpus), `proof1_cliff` (nonlinear & dual-memory cliff), `wasm_smith_fuzz` / `wasm_smith_gate` (1,000-module differential & blowup gate), `proof2_oms_ablation` / `proof2_ablation_gate` (compute-matched 3-arm ablation on `Gnomon-T2T` OMS).
