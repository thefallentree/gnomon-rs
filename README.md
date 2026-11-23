# Project Gnomon (`gnomon-rs`)

**Gnomon** is a 100% Safe Rust (`#![forbid(unsafe_code)]`) formal verification, equivalence-checking, and recursive abstraction-discovery engine targeting deterministic **WebAssembly (`wasm32`)**, exposed via both a standalone CLI (`gnomon`) and a single stdio **MCP server** (`gnomon mcp`).

Instead of feeding monolithic programs directly into bit-blasting SMT solvers (where nonlinear arithmetic and multi-memory updates hit exponential timeouts), Gnomon lets AI agents and engineers build **layered, machine-proved abstractions ("Strata")** that bundle:
1. A typed, acyclic **op** (`Layer k >= 1`) over lower-layer ops, and
2. At least one **machine-proved algebraic or `MemoryFrame` law** admitted by a tiny `#![no_std]` Kani-verified Trusted Computing Base (`gnomon-kernel`).

During verification, `egglog` v3.0 cancels high-level Strata laws and Ackermann **Uninterpreted Function (UF) CEGAR** discharges surviving pure-total nonlinear Strata *before* residual `QF_ABV` constraints reach `Bitwuzla`.

---

## Proof 1 Benchmark Highlight (`proof1_cliff`, 10 s cap)

Measured on real 64-bit MurmurHash3 `fmix64` nonlinear chains and dual-memory packet-ring pipelines (3-layer Strata stack built & proved from scratch in `25.7 ms`):

| Benchmark | Flat Bitwuzla (Layer-0) | Gnomon (Strata + `egglog` + UF CEGAR) | Speedup |
| --- | --- | --- | ---: |
| `fmix64` round-trip (`N = 1, 2, 4`) | `TIMEOUT (>10,000 ms)` | **`PROVED` (`22.5 – 31.7 ms`)** | **>316x – >445x** |
| Surviving `fmix64^N` + `(x+y)(x-y) == x²-y²` (`N = 1..8`) | `TIMEOUT (>10,000 ms)` | **`PROVED` (`24.8 – 32.3 ms`)** | **>354x – >404x** |
| Dual-memory `MemId(1)` hoist across `N = 8` `MemId(0)` `fmix64` writes | `TIMEOUT (>10,000 ms)` | **`PROVED` (`505.4 ms`)** | **>20x** |
| Soundness control (1-bit bug injected at `N = 8`) | — | **`FALSIFIED` (`13.27 ms`, Wasmtime Stage-1)** | — |

---

## Quick Start (CLI & MCP)

### Build Environment (LLVM 23 + Static Bitwuzla)
```bash
export PATH="/usr/lib/llvm-23/bin:$HOME/.cargo/bin:$HOME/.local/bitwuzla/bin:$HOME/.local/bin:$PATH"
export PKG_CONFIG_PATH="$HOME/.local/bitwuzla/lib/pkgconfig${PKG_CONFIG_PATH:+:$PKG_CONFIG_PATH}"
export LIBCLANG_PATH="/usr/lib/llvm-23/lib"
export CC="/usr/lib/llvm-23/bin/clang"
export CXX="/usr/lib/llvm-23/bin/clang++"

cargo build --release -p gnomon-mcp --bin gnomon
```

### CLI Usage (`target/release/gnomon`)
Every input subcommand accepts files or **stdin** (`-` or omitted) and `-t / --type <auto|wasm|ir>`:

```bash
# Inspect .ir JSON wire format
gnomon schema

# Lift .wasm or .ir from disk or stdin
gnomon lift -t wasm --emit-ir module.wasm
cat module.wasm | gnomon lift -t wasm
cat region.ir   | gnomon lift -t ir

# Deterministic concrete execution (outputs, trap, fuel, sparse memory diff)
gnomon trace -t wasm module.wasm --inputs '[{"ty":"i32","val":42},{"ty":"i32","val":6}]'

# Layered Strata synthesis & verification loop
gnomon --state state.json -t ir define-op --name wrap_inc --layer 1 wrap_inc.ir
gnomon --state state.json -t ir prove-law --op wrap_inc --name mask_idem --lhs lhs.ir --rhs rhs.ir
gnomon --state state.json -t ir check-goal --candidate cand.ir --spec spec.ir
gnomon --state state.json consolidate
```

Exit codes: `0` = Success / `PROVED` / `OK`, `1` = `FALSIFIED` / `TRAP` / `UNKNOWN`, `2` = CLI / parse / TCB admission error.

### Single MCP Server (`gnomon mcp`)
Registered in `~/.gemini/config/mcp_config.json`:
```json
{
  "mcpServers": {
    "gnomon": {
      "command": "/home/sunyc/src/gnomon-rs/target/release/gnomon",
      "args": ["mcp"]
    }
  }
}
```
Exposes 6 atomic tools over stdio (`rmcp` + `tokio`): `gnomon_lift_check`, `gnomon_run_trace`, `gnomon_define_op`, `gnomon_prove_law`, `gnomon_check_goal`, `gnomon_consolidate`.

---

## Verification Commands

```bash
# Workspace lints & release tests (47 tests across 5 crates — never set ulimit -v on Wasmtime tests!)
cargo clippy --workspace --all-targets -- -D warnings
cargo test --workspace --release

# Phase 1 Gate (30+30 real no_std Wasm corpus) & Proof 1 Solver-Cliff Benchmark
cargo run --release -p gnomon-bench --bin phase1_gate
cargo run --release -p gnomon-bench --bin proof1_cliff

# All 12 Kani TCB proof harnesses (guarded with 4 GiB virtual cap, -j 1)
(ulimit -v 4194304; timeout 600 cargo kani -p gnomon-kernel -j 1)
```

See [ARCHITECTURE.md](./ARCHITECTURE.md), [AGENTS.md](./AGENTS.md), and [ROADMAP.md](./ROADMAP.md) for architecture details, agent engineering rules, and upcoming plans (IEEE-754 floating point, multi-memory extensions, register spilling, SIMD/GPU).
