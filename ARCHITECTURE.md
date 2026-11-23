# Project Gnomon (`gnomon-rs`) Architecture & Audited Environment

## 1. Audited Build & Verification Environment

| Component | Exact Version / Detail | Notes |
| --- | --- | --- |
| **OS** | Ubuntu 22.04.5 LTS (`jammy`), `x86_64` | `glibc 2.35` (`ldd 2.35-0ubuntu3.18`) |
| **CPU** | Intel Xeon Gold 6132 @ 2.60 GHz (8 cores) | SIMD/bit flags: `avx2`, `avx512f`, `avx512dq`, `avx512cd`, `avx512bw`, `avx512vl`, `bmi1`, `bmi2`, `popcnt` |
| **Memory / Disk** | 23 GiB RAM, 275 GiB free | Measured at Milestone 1.0 audit |
| **Rust Compiler** | `rustc 1.100.0 (0ef1bc386 2026-11-09)` | Installed via `rustup 1.29.3 (edbc831ce 2026-11-02)` (bundled LLVM `23.1.5`) |
| **Cargo** | `cargo 1.100.0 (3acc79c0c 2026-11-05)` | Workspace Edition `2024`, Resolver `2` |
| **Rust Targets** | `x86_64-unknown-linux-gnu`, `wasm32-unknown-unknown` | Includes `clippy` and `rustfmt` |
| **Kani Verifier** | `Kani Rust Verifier 0.68.0 (cargo plugin)` / `CBMC 6.11.0` | Installed in `~/.cargo/bin` + `~/.kani/kani-0.68.0` |
| **Bitwuzla SMT** | `0.11.0` (source-built static release) | Built with static PIC `GMP 6.3.0` (`--enable-cxx`) + `MPFR 4.2.1` into `~/.local/bitwuzla` (required because upstream prebuilt zip targets `GLIBC_2.38`/`GLIBCXX_3.4.32`) |
| **C/C++ & Build** | `gcc 11.4.0`, `clang 23.0.0`, `llvm-23`, `cmake 3.22.1`, `meson 1.12.1`, `ninja 1.13.2`, `pkg-config 0.29.2` | `libclang-23` (`/usr/lib/llvm-23/lib`) used for `bindgen` / `libbitwuzla-sys` |

### Environment Variables for Builds & Verification
```bash
export PATH="/usr/lib/llvm-23/bin:$HOME/.cargo/bin:$HOME/.local/bitwuzla/bin:$HOME/.local/bin:$PATH"
export PKG_CONFIG_PATH="$HOME/.local/bitwuzla/lib/pkgconfig${PKG_CONFIG_PATH:+:$PKG_CONFIG_PATH}"
export LIBCLANG_PATH="/usr/lib/llvm-23/lib"
export CC="/usr/lib/llvm-23/bin/clang"
export CXX="/usr/lib/llvm-23/bin/clang++"
```
`~/.local/bitwuzla/lib/` provides `libbitwuzla.a`, `libgmp.a`, `libgmpxx.a`, `libmpfr.a`, headers in `~/.local/bitwuzla/include/`, and `bitwuzla.pc`, `gmp.pc`, `gmpxx.pc`, `mpfr.pc` in `pkgconfig/`.

### Locked Workspace Crate Versions (`Cargo.toml`)
- `wasmparser = "0.263.0"`, `wasm-encoder = "0.263.0"`, `wasmtime = "51.0.0"`
- `egglog = "3.0.0"`, `bitwuzla = { version = "0.11.0", features = ["static"] }`, `stitch_core = "0.1.0"`
- `rmcp = "3.11.0"`, `tokio = "1.54.1"`, `serde = "1.0.229"`, `serde_json = "1.0.154"`, `thiserror = "2.0.21"`, `proptest = "1.12.0"`

---

## 2. Immutable Architectural Invariants

1. **De Bruijn Separation of Trust:**
   - **Trusted Computing Base (`crates/gnomon-kernel`):** `~1,000–2,000 LoC` minimal TCB, `#![no_std]` (+ `alloc`), `#![forbid(unsafe_code)]`, zero runtime dependencies. Contains ONLY the `GnomonIR` data model, deterministic small-step reference interpreter, 3-way loop VC splitter, Stratum registry admission checker, and `#[cfg(kani)]` verification harnesses.
   - **Untrusted Search (`crates/gnomon-wasm`, `crates/gnomon-sieve`):** Safe Rust (`unsafe_code = "forbid"` at workspace level) optimized for Cranelift JIT falsification, `egglog` v3.0 equality saturation, `Bitwuzla` `QF_ABV` SMT proving, and `stitch_core` MDL compression. All candidate abstractions/laws pass through `gnomon-kernel` before permanent registry admission.
2. **Exact Deterministic Wasm Semantics (Zero Toy Shortcuts):**
   - Two's-complement `i32`/`i64` wrapping arithmetic and explicit deterministic traps (`DivByZero`, `IntOverflow`, `OutOfBoundsMem`, `OutOfFuel`, `HostContractViolation`, `Unreachable`).
   - `div_s(MIN, -1)` traps `IntOverflow`; `rem_s(MIN, -1)` yields `0` without trapping; effective address `addr + offset` checks in `u64` prevent 32-bit wrap-around memory escapes.
   - Multi-memory isolation (`MemId(u16)`) maps 1:1 to Wasm linear memories and independent SMT `Array<BV32, BV8>` instances.
   - Zero mocks or stubs of JIT/SMT failures.
3. **Paired Sub-Abstractions ("Strata"):**
   - Every promoted `Stratum` at Layer `k >= 1` bundles:
     1. A named typed `StratumOp` defined strictly as an acyclic composition over Layer `0 .. k-1` ops.
     2. At least one non-empty machine-proved `Law` (`Algebraic` or `MemoryFrame { untouched_mem }`) with non-zero `proof_digest`.
4. **Strict Phase Sequencing & Subagent File-Ownership Isolation:**
   - Phase 2 (`gnomon-mcp` runtime tools & flywheel benchmark) does NOT begin until 100% of Phase 1 automated tests, Kani harnesses, and Phase 1 Exit Gate metrics pass.
   - Parallel Phase 1 subagents own strictly disjoint crates; `gnomon-kernel` public interfaces remain frozen across Workstreams 1B–1D.

---

## 3. Workspace Layout & Locked Interfaces

```text
gnomon-rs/
├── Cargo.toml                  # Workspace manifest, forbidden unsafe_code, locked deps
├── ARCHITECTURE.md
└── crates/
    ├── gnomon-kernel/          # [TCB] #![no_std] + alloc IR, evaluator, VC splitter, Stratum gate
    │   └── src/{lib,ir,eval,vc,registry}.rs
    ├── gnomon-wasm/            # Workstream 1B: wasmparser/wasm-encoder <-> GnomonIR + wasmtime fuzzer
    ├── gnomon-sieve/           # Workstream 1C/2A: egglog eqsat + Bitwuzla QF_ABV + stitch_core
    ├── gnomon-mcp/             # Phase 2: rmcp + tokio MCP server exposing 6 atomic tools
    └── gnomon-bench/           # Workstream 1D (30+30 corpus) & Phase 2 (60-task 4-rung ablation)
```

### Locked Phase 1 Crate Contracts
- `gnomon-kernel`:
  - `ir`: `ValType`, `Val`, `TrapCode`, `MemId`, `ValId`, `GlobalId`, `FuncId`, `HostCallId`, `StratumId`, `MemWidth`, `UnOp`, `BinOp`, `Op`, `EffectOp`, `CallTarget`, `Stmt`, `Region`, `SliceBound`, `OffsetRange`, `HostContract`, `MemoryDef`, `GlobalDef`, `FuncDef`, `Module`.
  - `eval`: `MemoryState`, `HeapState`, `eval_func`, `eval_region`.
  - `vc`: `VcKind`, `VcObligation`, `LoopVcs`, `VcError`, `VcEvalResult`, `validate_read_only`, `remap_region_vals`, `split_invariant_loop`, `eval_vc`.
  - `registry`: `LawKind`, `Law`, `StratumOp`, `Stratum`, `RegistryError`, `StratumRegistry`.
- `gnomon-wasm`: `WasmError`, `FuzzConfig`, `ExecOutcome`, `Counterexample`, `FuzzOutcome`, `lift_wasm`, `emit_wasm`, `fuzz_equivalence`.
- `gnomon-sieve`: `SieveError`, `SmtModel`, `SmtResult`, `EqSatConfig`, `EqSatReport`, `SmtBackend` trait.
- `gnomon-mcp`: `MCP_TOOL_NAMES` (6 tools: `gnomon_lift_check`, `gnomon_run_trace`, `gnomon_define_op`, `gnomon_prove_law`, `gnomon_check_goal`, `gnomon_consolidate`).
- `gnomon-bench`: `CorpusCase`, `Phase1Scorecard` (`exit_gate_passed()`).
