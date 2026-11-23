# Project Gnomon (`gnomon-rs`) Architecture & Audited Environment

## 1. Audited Build & Verification Environment

| Component | Exact Version / Detail | Notes |
| --- | --- | --- |
| **OS** | Ubuntu 22.04.5 LTS (`jammy`), `x86_64` | `glibc 2.35` |
| **CPU** | Intel Xeon Gold 6132 @ 2.60 GHz (8 cores) | `avx2`, `avx512*`, `bmi1`, `bmi2`, `popcnt` |
| **Memory / Disk** | 23 GiB RAM, 275 GiB free | — |
| **Rust Compiler** | `rustc 1.100.0` (bundled LLVM `23.1.5`) | Edition `2024`, Resolver `2` |
| **Rust Targets** | `x86_64-unknown-linux-gnu`, `wasm32-unknown-unknown` | Includes `clippy` and `rustfmt` |
| **Kani Verifier** | `Kani Rust Verifier 0.68.0` / `CBMC 6.11.0` | **12/12** harnesses verified green (`0` failures, `314.52s` total, zero stubs/unwindsets) |
| **Bitwuzla SMT** | `0.11.0` (source-built static release) | Static PIC `GMP 6.3.0` + `MPFR 4.2.1` in `~/.local/bitwuzla` |
| **C/C++ & Build** | `clang 23.0.0`, `llvm-23`, `cmake`, `meson`, `ninja`, `pkg-config` | `libclang-23` (`/usr/lib/llvm-23/lib`) used by `bindgen` |

### Required Environment Variables
```bash
export PATH="/usr/lib/llvm-23/bin:$HOME/.cargo/bin:$HOME/.local/bitwuzla/bin:$HOME/.local/bin:$PATH"
export PKG_CONFIG_PATH="$HOME/.local/bitwuzla/lib/pkgconfig${PKG_CONFIG_PATH:+:$PKG_CONFIG_PATH}"
export LIBCLANG_PATH="/usr/lib/llvm-23/lib"
export CC="/usr/lib/llvm-23/bin/clang"
export CXX="/usr/lib/llvm-23/bin/clang++"
```

### Locked Workspace Crate Versions (`Cargo.toml`)
- `wasmparser = "0.263.0"`, `wasm-encoder = "0.263.0"`, `wasmtime = "51.0.0"`
- `egglog = "3.0.0"`, `bitwuzla = { version = "0.11.0", features = ["static"] }`, `stitch_core = "0.1.0"`
- `rmcp = "3.11.0"`, `tokio = "1.54.1"`, `serde = "1.0.229"`, `serde_json = "1.0.154"`, `schemars = "1"`, `clap = "4"`, `sha2 = "0.10"`, `base64 = "0.22"`, `thiserror = "2.0.21"`, `proptest = "1.12.0"`

---

## 2. Immutable Architectural Invariants

1. **De Bruijn Separation of Trust:**
   - **Trusted Computing Base (`crates/gnomon-kernel`):** `#![no_std]` (+ `alloc`), `#![forbid(unsafe_code)]`, zero runtime dependencies. Contains ONLY the flat 24-byte `IrSlot` arena `GnomonIR` data model, O(1) direct-indexed `Env`/`TypeEnv`, deterministic small-step reference interpreter, 3-way `InvariantLoop` VC splitter, `StratumRegistry` admission checker, and 12 `#[cfg(kani)]` verification harnesses (`0` stubs, `0` unwindsets, `0` `ManuallyDrop`/`mem::forget`, `0` `#[cfg(kani)]` shims outside `lib.rs`).
   - **Untrusted High-Speed Search (`gnomon-wasm`, `gnomon-sieve`, `gnomon-mcp`):** Safe Rust (`unsafe_code = "forbid"` workspace-wide) optimized for Cranelift JIT falsification (`wasmtime`), bounded `egglog` v3.0 equality saturation, `Bitwuzla` `QF_ABV` SMT proving + Ackermann UF congruence CEGAR, and `stitch_core` silent MDL compression. Every admitted Stratum passes through `gnomon-kernel::StratumRegistry::promote_stratum`.
2. **Exact Deterministic Wasm Semantics (Zero Toy Shortcuts):**
   - Two's-complement `i32`/`i64` wrapping arithmetic and explicit deterministic traps (`DivByZero`, `IntOverflow`, `OutOfBoundsMem`, `OutOfFuel`, `HostContractViolation`, `Unreachable`).
   - `div_s(MIN, -1)` traps `IntOverflow`; `rem_s(MIN, -1)` yields `0`; effective address `addr + offset` checks in `u64` prevent 32-bit wrap-around memory escapes.
   - Multi-memory isolation (`MemId(u16)`) maps 1:1 to Wasm linear memories and independent SMT `Array<BV32, BV8>` instances.
   - Zero mocks or stubs of JIT/SMT failures.
3. **Paired Sub-Abstractions ("Strata"):**
   - Every promoted `Stratum` at Layer `k >= 1` bundles:
     1. A named typed `StratumOp` defined strictly as an acyclic composition over Layer `0 .. k-1` ops.
     2. At least one non-empty machine-proved `Law` (`Algebraic` or unconditional `MemoryFrame { untouched_mem }` verified directly over `target_op.body` for both `MemorySize` and all in-bounds `u64`-guarded bytes) with non-zero SHA-256 `proof_digest`.
4. **Verification Pipeline (3-Stage Sieve + UF CEGAR):**
   - **Stage 1 (`gnomon-wasm`):** `wasmtime` Cranelift JIT differential fuzzer (`< 5 ms` concrete counterexamples).
   - **Stage 2a (`gnomon-sieve`):** Bounded `egglog` v3.0 rewrite saturation (`<= 5` iters, `<= 5,000` nodes) firing proved algebraic & `MemoryFrame` Strata laws + sound Ackermann Uninterpreted-Function (UF) congruence CEGAR for shared pure-total Strata.
   - **Stage 2b (`gnomon-sieve`):** Exact `Bitwuzla` `QF_ABV` fallback (in-process native API + zero-respawn SMT-LIB2 pipe backend) returning `Unsat` (proved) or concrete counterexample `SmtModel`.
   - **Stage 3 (`gnomon-kernel`):** SHA-256 `proof_digest` computation + TCB `promote_stratum` admission.
   - **Consolidation (`gnomon-sieve::consolidate`):** `stitch_core` silent `rewrite_with_invention` MDL scoring across `>= 2` verified solutions + `egglog` `<= 3`-step law non-redundancy pruning + transitive DAG closure + fresh TCB `promote_stratum` rebuild + compact `AutoDoc` export.

---

## 3. Workspace Layout & Crate Contracts

```text
gnomon-rs/
├── Cargo.toml                  # Workspace manifest, forbidden unsafe_code, locked deps
├── README.md                   # Quickstart, CLI/MCP usage, Proof 1 highlights
├── ARCHITECTURE.md             # Environment, TCB invariants, crate contracts
├── AGENTS.md                   # Engineering & verification instructions for AI agents
├── ROADMAP.md                  # Next plan: FP, multi-memory, register spilling, SIMD/GPU, Proof 2
└── crates/
    ├── gnomon-kernel/          # [TCB, frozen at phase-1-optimized] #![no_std] IR, eval, VC, registry, 12 Kani proofs
    ├── gnomon-wasm/            # [frozen] wasmparser/wasm-encoder <-> GnomonIR + wasmtime Stage-1 fuzzer
    ├── gnomon-sieve/           # egglog v3.0 + Bitwuzla QF_ABV + Ackermann UF CEGAR + stitch_core consolidation
    ├── gnomon-mcp/             # .ir JSON codec, GnomonEngine, `gnomon` CLI (-t wasm|ir|auto, stdin), single rmcp MCP server
    └── gnomon-bench/           # Phase 1 30+30 Wasm corpus (`phase1_gate`) & Proof 1 solver-cliff (`proof1_cliff`)
```

### Public Crate Contracts
- **`gnomon-kernel`:** `ir` (`IrSlot` 24B, `SlotPool`, `Region`, `Module`, `MemId`, `HostContract`, ...), `eval` (`HeapState`, `eval_func`, `eval_region`), `vc` (`LoopVcs`, `VcObligation`, `split_invariant_loop`, `eval_vc`, `validate_read_only_with_registry`), `registry` (`Law`, `LawKind`, `StratumOp`, `Stratum`, `StratumRegistry`).
- **`gnomon-wasm`:** `lift_wasm`, `emit_wasm`, `fuzz_equivalence`, `verify_round_trip`, `differential_check`.
- **`gnomon-sieve`:** `SmtBackend`, `BitwuzlaNativeBackend`, `BitwuzlaPipeBackend`, `EgglogSimplifier`, `consolidate_registry`, `discover_candidate_inventions`, `encode_region_as_stitch_expr`, `render_autodoc`.
- **`gnomon-mcp`:** `GnomonEngine`, `GnomonMcpServer`, `IrDocument`, `InputType` (`Auto | Wasm | Ir`), `MCP_TOOL_NAMES` (6 tools), and `gnomon` CLI binary (`lift`, `trace`, `define-op`, `prove-law`, `check-goal`, `consolidate`, `mcp`, `schema`).
- **`gnomon-bench`:** `CorpusCase`, `Phase1Scorecard`, `phase1_gate`, `proof1_cliff`.
