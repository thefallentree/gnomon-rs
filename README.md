# Project Gnomon (`gnomon-rs`)

**Gnomon** is a 100% Safe Rust (`#![forbid(unsafe_code)]`) formal verification, equivalence-checking, native hardware performance-profiling, and recursive abstraction-discovery engine targeting strict `#![no_std]` Rust & deterministic **WebAssembly (`wasm32`, `i32`/`i64`/`f32`/`f64`/`v128`)**, exposed via both a standalone CLI (`gnomon`) and a single stdio **MCP server** (`gnomon mcp`, 8 atomic tools).

Instead of feeding monolithic programs directly into bit-blasting SMT solvers (where nonlinear arithmetic, floating-point SIMD, and multi-memory updates hit exponential timeouts), Gnomon lets AI agents and engineers build **layered, machine-proved abstractions ("Strata")** that bundle:
1. A typed, acyclic **op** (`Layer k >= 1`) authored in strict `#![no_std]` Rust (`-t rust`) over lower-layer ops, and
2. At least one **machine-proved algebraic or `MemoryFrame` law** admitted by a tiny `#![no_std]` Kani-verified Trusted Computing Base (`gnomon-kernel`, **15/15 Kani proofs green**).

During verification, `egglog` v3.0 cancels high-level Strata laws and Ackermann **Uninterpreted Function (UF) CEGAR** discharges surviving pure-total nonlinear Strata *before* residual `QF_ABVFP` constraints reach `Bitwuzla`. Native x86-64 (`skylake`) and ARM64 (`neoverse-v2`) lowering + `llvm-mca` (`gnomon profile`) closes the loop on verified systems performance optimization.

---

## Measured Verification & Benchmark Highlights

### 1. Core TCB v2 & Differential Soundness Gates
- **TCB v2 (`gnomon-kernel`):** `#![no_std]`, `#![forbid(unsafe_code)]`, 24-byte `IrSlot`, 0 runtime deps, 0 stubs, **15/15 Kani proofs green** (`0` failures, `11m54.38s`, `-j 1`, `ulimit -v 4194304`).
- **3-Way Differential Fuzzer (`gnomon-wasm` vs `wasmtime 51`):** **27,768** 3-way bit-exact checks (including **13,896** IEEE-754 FP & `v128` SIMD corner cases), **0** mismatches.
- **`wasm-smith` Differential & Blowup Gate (`wasm_smith_fuzz --count 1000`):** **1,000/1,000** random modules lifted & round-tripped, **4,785** differential checks across `1,916` functions, **0** mismatches, `egglog` p99 `129.256 ms` (`0` blowups), **3** real `gnomon-sieve` bugs caught & fixed.
- **Full Workspace Suite:** **116** release tests across 5 crates (`gnomon-kernel`: 14, `gnomon-wasm`: 14, `gnomon-sieve`: 34, `gnomon-bench`: 9, `gnomon-mcp`: 45), `0` clippy warnings (`-D warnings`).

### 2. Proof 2 — Compute-Matched 3-Arm Ablation on `Gnomon-T2T` OMS (`proof2_oms_ablation`, `3,000 ms/task` cap)
Zero-trust Rung 1–2 training promoted 12 raw OMS Strata (13 laws UNSAT-verified in `1,934.9 ms`); `stitch_core` + `egglog` consolidation kept **11 Strata (11 laws)** and pruned 1 scratch Stratum (`331.4 ms`, **0** unsound admissions). Evaluated on 10 held-out Rung 3–4 OMS cliff tasks + 2 soundness-control mutants under an identical `3,000 ms/task` Bitwuzla cap:

| Metric | Arm A (Flat Layer-0) | Arm B (Modular Helpers) | Arm C (Full Gnomon Strata + `egglog` + UF CEGAR) | Exit Gate |
| --- | :---: | :---: | :---: | :---: |
| **Held-Out Cliff Tasks Solved** | `2 / 10` (`8` timeouts) | `2 / 10` (`8` timeouts) | **`10 / 10` (`0` timeouts — `5.0×` Arms A & B)** | `>= 2.0×` **PASS** |
| **Median SMT Speedup** | `1.0×` | `1.0×` | **`99.5×` vs A / `103.4×` vs B** (`27.0 – 515.8 ms`) | `>= 5.0×` **PASS** |
| **Cross-Rung Reuse Rate** | `0%` | `0%` | **`100.0%` (`10/10`) Strata / `70.0%` (`7/10`) R1–2 `egglog` laws** | `>= 30.0%` **PASS** |
| **Soundness Mutants (`M01`, `M02`)** | `2 / 2 FALSIFIED` | `2 / 2 FALSIFIED` | **`2 / 2 FALSIFIED` (`0` false `PROVED`, `0` unsound)** | `0` unsound **PASS** |

*(Proof 1 baseline `proof1_cliff`, 10 s cap: Flat Bitwuzla timed out on `8/10` nonlinear/dual-memory tasks while Gnomon proved `10/10` in `22.5 – 505.4 ms`, `>20× – >445×`, and falsified a 1-bit `N=8` bug in `13.27 ms`.)*

### 3. E2E Verified OMS (`Gnomon-T2T`, 15 Strata `S1.1–S4.2`) + Verified Native x64 & ARM64 Optimization (`S4.3`)
All **27** strict `#![no_std]` Rust OMS files (**15** Strata `S1.1–S4.2` + `S4.3` perf pairs + **11** separate `*_buggy.rs` mutant files; `S1.1`/`S1.2`/`S1.4` embed mutants inline) compile cleanly with `-D warnings` and round-trip lift via [`examples/oms_strata/build.sh`](examples/oms_strata/build.sh). Layer-4 E2E pipelines (`S4.1` Inbound ExecReport + `S4.2` Tick-to-Trade & OUCH Wire Out) achieved **24/24** exact verdicts (**17/17 `PROVED`**, **7/7 mutants `FALSIFIED`**). All 6 hot-path optimization pairs in [`examples/oms_strata/s4_3_perf_opt_pairs.rs`](examples/oms_strata/s4_3_perf_opt_pairs.rs) are proved bit-exact (**8/8 `PROVED`**) and profiled live via `gnomon profile --targets x64,arm64 --bench`:

| Pair (`ref -> opt`) | x64 (`skylake`) Key Delta & Cyc / RTh Speedup | ARM64 (`neoverse-v2`) Key Delta & Cyc / RTh Speedup | Host x64 `ns/op` |
| --- | --- | --- | --- |
| **1. Barrett Fastmod** (`oms_bucket`) | **div `1->0`** · **1.48×** cyc / **2.50×** RTh | **udiv `1->0`** · **6.24×** cyc / **6.50×** RTh | `18.72 -> 15.42` (**1.21×**) |
| **2. SWAR FIX Digits** (`oms_fix_digits`) | **br `7->0`**, inst `40->13` · **3.02×** cyc / **3.00×** RTh | **br `7->0`**, inst `47->10` · **1.31×** cyc / **4.59×** RTh | `5.58 -> 2.41` (**2.31×**, `preset:ascii-digits`) |
| **3. Hash Unroll** (`12x_spill -> 4x`) | **spills `19->0`**, stack `56B->0B` · **1.14×** cyc / **1.15×** RTh | **0 spills** (31 GPRs) · **1.02×** cyc / **1.02×** RTh | `39.02 -> 41.25` (`2x`: `36.80`) |
| **4. Branchless Risk FSM** (`oms_risk_fsm`) | **br `23->0`**, inst `128->91` · **1.66×** cyc / **1.52×** RTh | **br `45->0`**, inst `136->73` · **2.21×** cyc / **2.54×** RTh | `20.05 -> 10.38` (**1.93×**, `preset:oms-valid`) |
| **5. Zero-Copy OUCH 48B** (`oms_ouch_pack`) | **stack `56B->0B`**, spills `1->0` · **2.20×** cyc | **stack `64B->0B`** · **1.53×** cyc | `12.68 -> 5.91` (**2.15×**, `--bench-inputs`) |
| **6. 4-Lane VWAP SIMD** (`oms_vwap`) | **br `7->1`**, `mulps`/`addps` · **1.23×** cyc / **1.20×** RTh | **br `6->1`**, **NEON `0->14`** · **1.45×** cyc / **1.70×** RTh | `9.99 -> 3.24` (**3.09×**) |

### 4. Horizontal Generalization — 7 Non-Trading Vertical Packs (`examples/vertical_packs/`)
Verified and profiled across **7** distinct non-trading systems domains (**0** domain-specific engine changes, `14/14` round-trip lift valid, **55/55** live verdicts via [`examples/vertical_packs/verify_all.sh`](examples/vertical_packs/verify_all.sh): **38/38 `PROVED`**, **17/17 buggy mutants `FALSIFIED`**):

| Vertical Pack | Domain & Verified Properties | Live Verdicts | `gnomon profile` (`x64` / `arm64` / host) |
| --- | --- | :---: | --- |
| **`ai_q8_0_quant`** | AI Inference `Q8_0` 4-lane `f32x4` block quantizer (`QF_ABVFP`, no `0*Inf=NaN`, exact `nearest` rounding) | `3 PROVED` / `2 FALSIFIED` | x64 **2.61×** cyc (`-20` insns) · ARM64 **1.57×** cyc, **NEON `13->33`**, br `2->0` |
| **`db_parquet_varint_slice`** | Columnar DB zero-copy `&[u8]` LEB128 varint + ZigZag (`--ignore-dead-stack`, `SliceFrame readonly`, branchless equiv) | `6 PROVED` / `2 FALSIFIED` | x64 **br `4->0`**, `1.10×` RTh · ARM64 **br `3->0`**, **1.50×** cyc |
| **`net_wireguard_replay`** | Networking RFC 6479 / WireGuard 64-bit sliding anti-replay window (inductive invariant, large-jump reset, branchless equiv) | `4 PROVED` / `2 FALSIFIED` | x64 **br `2->0`**, `0` spills · ARM64 `0` br (`csel`), `0` spills |
| **`cloud_quota_saga`** | Cloud Distributed Quota Saga (`reserve`/`commit`/`cancel_reserve` inductive conservation, zero double-release/commit) | `3 PROVED` / `2 FALSIFIED` | Inductive stateful FSM (`globals=0`) |
| **`crypto_ct_tls_record`** | Cryptography Constant-Time PKCS#7 unpad (`--ignore-dead-stack`, `SliceFrame readonly`) + `v128` 16B MAC + ChaCha20 `u32x4` round (`SliceFrame param:0:64`) | `8 PROVED` / `3 FALSIFIED` | x64 **br `34->0`** (CT!), **3.38×** cyc / **3.72×** RTh · ARM64 **br `37->0`** (CT!), **3.30×** cyc / **4.17×** RTh · Host **1.39×** |
| **`robotics_flight_pid_mixer`** | Safety-Critical Robotics Stateful IEEE-754 `QF_ABVFP` PID + anti-windup + slew-rate + E-stop + `f32x4` 4-motor mixer (`2^23` magic-bias RNE proved bit-exact) | `7 PROVED` / `3 FALSIFIED` | x64 **br `17->0`**, **3.67×** cyc / **2.89×** RTh · ARM64 **br `17->0`**, **NEON `0->35`**, **1.50×** RTh · Host **1.93×** |
| **`os_mmu_wx_tlb`** | OS Kernel / Hypervisor 4-region `W^X` MMU (inductive `W^X`, 4 KiB align, zero wrap, disjointness, global `W^X` non-interference, unmap revocation) + `v128` 4-way TLB | `7 PROVED` / `3 FALSIFIED` | x64 **br `20->0`**, **AVX2 `0->20`**, **2.16×** RTh · ARM64 **br `18->0`**, **NEON `0->18`**, **2.38×** RTh · Host **1.53×** |

### 5. Step 7: Live Blind AI Closed-Loop Optimization (`examples/closed_loop_demo/`)
A blind AI optimization agent using **only `rustc` and `gnomon`** (`define-op`, `prove-law`, `check-goal`, `check-contract`, `profile --targets x64,arm64 --bench`) autonomously hill-climbed 3 slow trading/OMS reference kernels to `PROVED` (`0` divs, `0` register spills on both x64 & ARM64) while catching **3 real correctness bugs** and **2 hardware regressions** mid-loop (see [examples/closed_loop_demo/REPORT.md](./examples/closed_loop_demo/REPORT.md)):

| Kernel (`ref -> opt`) | Formal Gate (`gnomon`) | x64 (`skylake`) Cyc / RTh | ARM64 (`neoverse-v2`) Cyc / RTh | Host `ns/op` | Bug / Regression Caught Mid-Loop |
| --- | --- | --- | --- | --- | --- |
| **K1: 8B FIX ASCII** | `PROVED` (`9.38 s`, all `2^64`) | **2.58×** cyc / **2.67×** RTh (`72->27` insns, br `8->1`) | **3.17×** cyc / **3.21×** RTh (`81->25` insns) | `8.99 -> 5.05` (**1.78×**) | SWAR carry-bleed (`"+*780031"`) in `181.7 ms`; ARM64 `csinv` stall (`0.72×`) |
| **K2: 4-Venue SOR** | `PROVED` (`2.83 s`, TCB `sor-div-10k-fold`) | **5.66×** cyc / **2.55×** RTh (**div `4->0`**, br `3->0`) | **4.06×** cyc / **6.00×** RTh (**udiv `4->0`**, br `4->0`) | `18.01 -> 15.46` (**1.16×**) | 40-bit reciprocal off-by-one (`499_059_999`); x64 spill (`1->0`) |
| **K3: Tick-Risk** | `PROVED` (`124.0 ms`, UF CEGAR) | **18.57×** cyc / **5.39×** RTh (**div `2->0`**, br `6->0`) | **3.00×** cyc / **9.13×** RTh (**udiv `1->0`**, br `8->0`) | `6.46 -> 4.84` (**1.33×**) | Non-boolean `kill_switch = 0x4000_0000` bypass; UF CEGAR `>15s -> 124 ms` |

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
Every input subcommand accepts files or **stdin** (`-` or omitted) and `-t / --type <auto|wasm|ir|rust>`:

```bash
# Inspect .ir JSON wire format
gnomon schema

# Lift strict no_std Rust, .wasm, or .ir (with static SMT-cliff diagnostics)
gnomon lift -t rust examples/oms_strata/s1_1_notional_collar.rs
gnomon lift -t wasm --emit-ir module.wasm

# Deterministic concrete execution (outputs, trap, fuel, sparse memory diff)
gnomon trace -t wasm module.wasm --inputs '[{"ty":"i32","val":42},{"ty":"i32","val":6}]'

# Verify pre/post contracts, inline assume/assert, SliceFrame isolation, or inductive FSM suites
gnomon check-contract -t rust --entry checked_notional --requires req_notional --ensures ens_notional \
  examples/oms_strata/s1_1_notional_collar.rs
gnomon check-contract -t rust --init init_empty \
  --ops submit_new,on_ack,request_cancel,request_replace,on_fill,on_cancel_ack,on_replace_ack,on_reject \
  --invariant inv_child_fsm examples/oms_strata/s3_1_child_fsm.rs

# Layered Strata synthesis, equivalence checking (--ignore-dead-stack), Rust bindings, & consolidation
gnomon --state state.json -t rust define-op --name order_id_mix --layer 1 examples/oms_strata/s1_3_order_id_mix.rs
gnomon --state state.json emit-rust -o strata.rs
gnomon --state state.json -t rust check-goal --candidate opt.rs --spec ref.rs --ignore-dead-stack
gnomon --state state.json consolidate

# Native x86-64 (skylake) & ARM64 (neoverse-v2) performance oracle + host microbench
gnomon profile examples/oms_strata/s4_3_perf_opt_pairs.rs \
  --entry oms_bucket_ref --opt-entry oms_bucket_opt --targets x64,arm64 --bench
gnomon profile examples/oms_strata/s4_3_perf_opt_pairs.rs \
  --entry oms_fix_digits_ref --opt-entry oms_fix_digits_opt --targets x64,arm64 --bench --bench-preset ascii-digits
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
Exposes **8 atomic tools** over stdio (`rmcp` + `tokio`): `gnomon_lift_check`, `gnomon_run_trace`, `gnomon_define_op`, `gnomon_prove_law`, `gnomon_check_goal`, `gnomon_check_contract`, `gnomon_consolidate`, `gnomon_profile`.

---

## Verification & Benchmark Commands

```bash
# Workspace lints & release tests (116 tests across 5 crates — never set ulimit -v on Wasmtime tests!)
cargo clippy --workspace --all-targets -- -D warnings
cargo test --workspace --release

# Build & round-trip lift all 27 OMS Strata fixtures (S1.1-S4.3 + all buggy mutants)
./examples/oms_strata/build.sh

# Build, round-trip lift, verify (55/55 verdicts) & profile all 7 non-trading vertical packs
./examples/vertical_packs/verify_all.sh

# Live blind AI closed-loop verification & x64/ARM64 hardware profiling showcase
./examples/closed_loop_demo/verify_and_profile.sh

# Benchmarks & Fuzz Gates
cargo run --release -p gnomon-bench --bin phase1_gate
cargo run --release -p gnomon-bench --bin proof1_cliff
cargo run --release -p gnomon-bench --bin wasm_smith_fuzz -- --count 1000
cargo run --release -p gnomon-bench --bin proof2_oms_ablation

# All 15 Kani TCB v2 proof harnesses (guarded with 4 GiB virtual cap, -j 1)
(ulimit -v 4194304; timeout 900 cargo kani -p gnomon-kernel -j 1)
```

See [ARCHITECTURE.md](./ARCHITECTURE.md), [ROADMAP.md](./ROADMAP.md), [AGENTS.md](./AGENTS.md), [examples/oms_strata/README.md](./examples/oms_strata/README.md), [examples/vertical_packs/README.md](./examples/vertical_packs/README.md), and [examples/closed_loop_demo/REPORT.md](./examples/closed_loop_demo/REPORT.md) for architecture details, complete measured tables, and reproduction scripts.
