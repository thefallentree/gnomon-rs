# Agent Instructions (`gnomon-rs`)

Guidelines for AI coding/verification agents operating on Project Gnomon.

## 1. Non-Negotiable Safety & TCB Rules
- **Workspace-wide `#![forbid(unsafe_code)]`**: Never introduce `unsafe` anywhere in any crate.
- **TCB Hygiene (`crates/gnomon-kernel`):**
  - Must remain `#![no_std]` (+ `alloc`) with **zero runtime dependencies**.
  - **Zero verification hacks:** Never add `#[kani::stub]`, `--unwindset`, `no-assertion-reach-checks`, `ManuallyDrop`, `core::mem::forget`, or `#[cfg(kani)]` shims outside `crates/gnomon-kernel/src/lib.rs`.
  - Any planned extension to `gnomon-kernel` (such as IEEE-754 FP, `v128` SIMD, or `memory64` in Phase 3) MUST preserve `12/12+` passing Kani harnesses with zero regressions and keep `IrSlot` compact for CBMC.
- **No stdout pollution in MCP code:** `gnomon mcp` speaks JSON-RPC 2.0 over stdio. Never call `println!` (or upstream `stitch_core::compression`) on MCP code paths; use `consolidate_registry` (`rewrite_with_invention`, 100% silent).

## 2. Mandatory Build & Verification Commands
Always export the LLVM 23 + static Bitwuzla toolchain variables before running Cargo or Kani:
```bash
export PATH="/usr/lib/llvm-23/bin:$HOME/.cargo/bin:$HOME/.local/bitwuzla/bin:$HOME/.local/bin:$PATH"
export PKG_CONFIG_PATH="$HOME/.local/bitwuzla/lib/pkgconfig${PKG_CONFIG_PATH:+:$PKG_CONFIG_PATH}"
export LIBCLANG_PATH="/usr/lib/llvm-23/lib"
export CC="/usr/lib/llvm-23/bin/clang"
export CXX="/usr/lib/llvm-23/bin/clang++"
```

- **Lint & tests:**
  ```bash
  cargo clippy --workspace --all-targets -- -D warnings
  cargo test --workspace --release
  ```
  - **CRITICAL:** Never apply `ulimit -v 4194304` to `wasmtime` tests (`gnomon-wasm`, `gnomon-mcp`, `gnomon-bench`), because Wasmtime reserves >4 GiB virtual `PROT_NONE` guard pages.
- **Kani verification:**
  ```bash
  (ulimit -v 4194304; timeout 600 cargo kani -p gnomon-kernel -j 1)
  ```
  - Always guard `cargo kani` / `cbmc` with `ulimit -v 4194304`, `timeout`, and `-j 1`.
  - Note: Kani compiles Rust MIR directly to CBMC GOTO (not `target/release`), so `--release` does not affect Kani proofs.
- **Benchmarks & CLI binary refresh:**
  ```bash
  cargo build --release -p gnomon-mcp --bin gnomon
  cargo run --release -p gnomon-bench --bin phase1_gate
  cargo run --release -p gnomon-bench --bin proof1_cliff
  ```

## 3. Using the `gnomon` CLI & MCP Server Effectively
- Run `gnomon schema` first when authoring `.ir` JSON manually.
- Use `--state <path.json>` across CLI commands to persist your verified Strata stack.
- **Decompose before proving:** Break nonlinear arithmetic, multi-round codecs/hashes, memory-isolated writers, and register-spilled kernels into small Layer-1 → Layer-2 Strata (`define-op`), prove local algebraic & `MemoryFrame` laws (`prove-law`), then discharge composite goals (`check-goal`) where `egglog` + Ackermann UF CEGAR avoid exponential bit-blasting.
- Always run `consolidate` after solving `>= 2` goals to prune single-use ops and redundant laws before reusing the `AutoDoc` in downstream prompts.
