# Agent Instructions (`gnomon-rs`)

Guidelines for AI coding/verification agents operating on Project Gnomon.

## 1. Non-Negotiable Safety & TCB Rules
- **Workspace-wide `#![forbid(unsafe_code)]`**: Never introduce `unsafe` anywhere in any crate.
- **TCB v2 Hygiene (`crates/gnomon-kernel`):**
  - Must remain `#![no_std]` (+ `alloc`) with **zero runtime dependencies**.
  - Supports Wasm32 core + IEEE-754 `f32`/`f64` + `v128` SIMD (`ValType` 5, `UnOp` 100, `BinOp` 141, `Op` 17) with **`15/15` passing Kani harnesses** and compact `IrSlot` layout for CBMC.
  - **Zero verification hacks:** Never add `#[kani::stub]`, `--unwindset`, `no-assertion-reach-checks`, `ManuallyDrop`, `core::mem::forget`, or `#[cfg(kani)]` shims outside `crates/gnomon-kernel/src/lib.rs`.
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
- **Kani verification (`15/15` harnesses):**
  ```bash
  (ulimit -v 4194304; timeout 900 cargo kani -p gnomon-kernel -j 1)
  ```
  - Always guard `cargo kani` / `cbmc` with `ulimit -v 4194304`, `timeout`, and `-j 1`.
  - Note: Kani compiles Rust MIR directly to CBMC GOTO (not `target/release`), so `--release` does not affect Kani proofs.
- **CLI binary refresh & benchmarks:**
  ```bash
  cargo build --release -p gnomon-mcp --bin gnomon
  cargo run --release -p gnomon-bench --bin phase1_gate
  cargo run --release -p gnomon-bench --bin proof1_cliff
  ```

## 3. All 8 Atomic MCP Tools & CLI Equivalents
`gnomon mcp` exposes **8 atomic tools** over stdio (matching `gnomon <subcommand>`):
1. **`gnomon_lift_check`** (`gnomon lift`): Lift `.wasm`, strict `#![no_std]` Rust (`-t rust`), or `.ir` JSON into typed `GnomonIR`, bind `stratum` imports, verify round-trip Wasm emission, and report static SMT-cliff warnings.
2. **`gnomon_run_trace`** (`gnomon trace`): Execute a lifted module, `.rs`, or `.ir` region on the deterministic `gnomon-kernel` interpreter, returning outputs, traps, fuel consumed, and sparse memory diff.
3. **`gnomon_define_op`** (`gnomon define-op`): Register a candidate Layer-`k` Stratum op after `gnomon-kernel` DAG acyclicity and type validation.
4. **`gnomon_prove_law`** (`gnomon prove-law`): Run the 3-stage sieve (Wasmtime JIT fuzz → Bitwuzla `QF_ABV`/`QF_ABVFP` → `gnomon-kernel` SHA-256 TCB admission) for algebraic or unconditional `MemoryFrame` laws.
5. **`gnomon_check_goal`** (`gnomon check-goal`): Prove equivalence (`candidate ≡ spec` under optional `pre`) or 3-way `InvariantLoop` VCs via bounded `egglog` cancellation + sound Ackermann UF CEGAR + Bitwuzla.
   - Supports **`--ignore-dead-stack`** (`ignore_dead_stack: true`) to ignore dead shadow-stack bytes below `SP_in` (`Global(0)`) while proving `SP_out == SP_in` and exact live-memory equivalence (essential for proving zero-copy `opt` kernels against stack-buffered `ref` kernels).
6. **`gnomon_consolidate`** (`gnomon consolidate`): Prune low-MDL ops (`stitch_core` across `>= 2` solutions) and redundant laws (`<= 3` `egglog` steps), emit compact `AutoDoc`, and optionally emit `#![no_std]` `strata.rs` bindings (`gnomon emit-rust`).
7. **`gnomon_check_contract`** (`gnomon check-contract`): Verify single-op pre/post contracts (`--requires`/`--ensures`), trap-freedom, inline `gnomon_assume`/`gnomon_assert` harnesses, or multi-op inductive state-invariant suites (`--init`, `--ops`, `--invariant`).
   - Supports **`--ignore-dead-stack`** and **`--slice-frame`** (`slice_frame` in MCP: `readonly`, `base=<param:N|U32>,len=<param:N|U32>`, `mem=M`, or shorthand `param:<N>:<LEN>`) to prove intra-memory write-frame isolation (e.g. RX buffer untouched, kill-switch zero live writes).
8. **`gnomon_profile`** (`gnomon profile`): Lower strict `#![no_std]` Rust to native **x86-64 (`skylake`)** and **ARM64 (`neoverse-v2`)** assembly via `rustc` + LLVM-23 `llc`, compute exact static hardware metrics (instructions, branches, `div`/`idiv`/`udiv`/`sdiv`, SIMD/NEON, stack frame bytes, register spills/reloads) + `llvm-mca` cycles/IPC/RThroughput, compare `ref` vs `opt` (`--compare` / `--opt-entry`), and run opt-in 1M-iteration native host microbenchmarks (`--bench`) with realistic hot-path inputs (`--bench-inputs '<JSON>'` or `--bench-preset default|ascii-digits|oms-valid`).

## 4. Strict Rust Strata Bridge (`-t rust`) & Decomposition Workflow
- Pass `-t rust` (or `input_type: "rust"` / `.rs` path with `-t auto`) directly to `lift`, `trace`, `define-op`, `prove-law`, `check-goal`, and `check-contract` to compile `#![no_std]` Rust to `wasm32-unknown-unknown` and bind `#[link(wasm_import_module = "stratum")]` calls automatically.
- Run `gnomon schema` first when authoring `.ir` JSON manually, and use `--state <path.json>` across CLI invocations to persist your verified Strata stack.
- **Decompose before proving:** Break nonlinear arithmetic, multi-round hashes/codecs, memory-isolated writers, and register-spilled kernels into Layer-1 → Layer-2 Strata (`define-op`), prove local algebraic & `MemoryFrame` laws (`prove-law`), then discharge composite goals (`check-goal`) where `egglog` + Ackermann UF CEGAR avoid exponential bit-blasting.
- Always run `consolidate` after solving `>= 2` goals to prune single-use ops and redundant laws before reusing the `AutoDoc` in downstream prompts.

## 5. Verified Reference Suites
- **15 OMS Strata (`examples/oms_strata/`, `Gnomon-T2T`):**
  - Layer 1 (`S1.1–S1.4`): checked notional/collar, Barrett tick/fee fastmod, bijective `fmix64` order-ID mix, branchless SWAR FIX digit parsing.
  - Layer 2 (`S2.1–S2.4`): SPSC ring, Stratum-linked order slab (`order_id_mix`), zero-copy ITCH RX decode & OUCH TX encode (`--ignore-dead-stack`, `--slice-frame`).
  - Layer 3 (`S3.1–S3.5`): 8-state child FSM, parent-child zero-overfill OMS, SEC 15c3-5 pre-trade risk gate (`checked_notional`, `price_collar_ok`), `v128` L2 book sweep, `f32x4` `QF_ABVFP` VWAP/VaR signal.
  - Layer 4 (`S4.1–S4.2` + `S4.3`): E2E inbound ExecReport pipeline (`s4_1_oms_on_exec_report.rs`), E2E Tick-to-Trade + OUCH pipeline (`s4_2_oms_on_tick_or_order.rs`), and 6 formally proved `ref -> opt` performance pairs (`s4_3_perf_opt_pairs.rs`) + 11 `*_buggy.rs` mutant files.
- **4 Non-Trading Vertical Packs (`examples/vertical_packs/`):**
  - **AI Inference (`ai_q8_0_quant.rs`):** `llama.cpp`/GGML `Q8_0` `f32x4` block quantization (`QF_ABVFP`).
  - **Columnar DB (`db_parquet_varint_slice.rs`):** 4-byte LEB128 varint slice decoder (`--ignore-dead-stack`, `SliceFrame readonly`) + Delta-ZigZag bijection.
  - **Networking (`net_wireguard_replay.rs`):** WireGuard/IPsec RFC 6479 64-bit sliding anti-replay window.
  - **Cloud Infrastructure (`cloud_quota_saga.rs`):** Multi-tenant 4-slot two-phase reservation quota saga.
- **Live Blind AI Closed-Loop Showcase (`examples/closed_loop_demo/`):**
  - 3 real-world OMS/trading kernels (`k1_fix_ascii_price.rs`, `k2_sor_venue_router.rs`, `k3_oms_tick_risk_fastpath.rs` + Layer-1 `strata_l1.rs` / `strata_l1_laws.rs`) autonomously optimized end-to-end using only `rustc` and `gnomon` (`REPORT.md`, `verify_and_profile.sh`).
