# Closed-Loop AI Performance Engineering Showcase (`examples/closed_loop_demo/`)

This showcase demonstrates an autonomous **Blind AI Performance Optimization Agent** using **only `rustc` and the `gnomon` CLI** (`define-op`, `prove-law`, `check-goal`, `check-contract`, `profile --compare --targets x64,arm64 --bench`) as its formal equivalence oracle and dual-architecture microarchitectural profiler.

Every candidate optimization was iteratively synthesized, formally verified against its reference specification and application contract, profiled on both **`x86_64` (`skylake`)** and **`aarch64` (`neoverse-v2`)** via `llvm-mca` plus live host `ns/op` microbenchmarks, and refined whenever Bitwuzla returned a counterexample (`FALSIFIED`), hit a nonlinear SMT cliff (`UNKNOWN`), or `llvm-mca` revealed a microarchitectural regression or register spill.

---

## Executive Summary — Final Verified Results

All 3 `#![no_std]` Rust kernels (plus their Layer-1 Strata helpers) compile with **0 warnings (`-D warnings`)** on both `wasm32-unknown-unknown` and native `x86_64`, are **100% `PROVED`** (`opt ≡ ref` + application contract + 0 traps), and cleanly beat their references on **both `x86_64 (skylake)` and `aarch64 (neoverse-v2)`** with **0 `div` instructions** and **0 register spills**.

### Verification Summary (`gnomon`)

| Kernel | File | Equivalence Gate (`check-goal`) | Contract Gate (`check-contract`) | Layer-1 Strata / Laws Used |
| --- | --- | --- | --- | --- |
| **K1: 8-Byte FIX ASCII Price Parser** | `k1_fix_ascii_price.rs` | **`PROVED`** (`9,375.7 ms`, all `2^64` inputs, 0 preconditions) | **`PROVED`** (`45.9 ms`, trap-free, `-1` or `0..=99_999_999`) | Standalone (no `--state`) |
| **K2: 4-Venue Smart Order Router** | `k2_sor_venue_router.rs` | **`PROVED`** (`2,834.3 ms`, under `req_sor`, `350 -> 266` SSA nodes) | **`PROVED`** (`30.1 ms`, `0 <= best_venue <= 3`, `0 <= alloc_qty <= min(parent_qty, best_qty)`) | `define-op sor_div_10k` + **`prove-law sor-div-10k-fold`** (`PROVED`, `1,654.7 ms`, TCB-admitted digest `e668c7ee...`) |
| **K3: Tick-Align + Pre-Trade Risk** | `k3_oms_tick_risk_fastpath.rs` | **`PROVED`** (`124.0 ms`, under `req_tick_risk`, `138 -> 112` SSA nodes) | **`PROVED`** (`27.3 ms`, kill-switch dominance `=> 0`, tick-aligned, 0 traps) | `define-op notional_le`, `define-op collar_le` (UF-CEGAR congruence) |

### Dual-Architecture Hardware & Live Host Speedups (`gnomon profile --compare --targets x64,arm64 --bench`)

| Kernel (`ref -> opt`) | Target / CPU | Insns | Branches | `div`s | Spills | Cycles / Iter | Cycle Speedup | Block RThroughput | RT Speedup | Live Host `ns/op` |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| **K1: FIX 8-Byte ASCII** (`fix_parse_8_ref -> _opt`) | `x64` (`skylake`) | `72 -> 27` (`-45`) | `8 -> 1` (`-7`) | `0 -> 0` | `0 -> 0` | `18.34 -> 7.10` | **2.58x** | `12.8 -> 4.8` | **2.67x** | `8.99 -> 5.05` (**1.78x**, `preset:ascii-digits`) |
| **K1: FIX 8-Byte ASCII** (`fix_parse_8_ref -> _opt`) | `arm64` (`neoverse-v2`) | `81 -> 25` (`-56`) | `8 -> 1` (`-7`) | `0 -> 0` | `0 -> 0` | `13.68 -> 4.32` | **3.17x** | `13.5 -> 4.2` | **3.21x** | — |
| **K2: 4-Venue SOR** (`sor_route_4_ref -> _opt`) | `x64` (`skylake`) | `97 -> 76` (`-21`) | `3 -> 0` (`-3`) | **`4 -> 0`** | **`0 -> 0`** | `103.60 -> 18.30` | **5.66x** | `40.8 -> 16.0` | **2.55x** | `18.01 -> 15.46` (**1.16x**, 4 realistic books) |
| **K2: 4-Venue SOR** (`sor_route_4_ref -> _opt`) | `arm64` (`neoverse-v2`) | `66 -> 48` (`-18`) | `4 -> 0` (`-4`) | **`4 -> 0`** | **`0 -> 0`** | `49.07 -> 12.10` | **4.06x** | `48.0 -> 8.0` | **6.00x** | — |
| **K3: Tick-Risk Fast Path** (`oms_tick_risk_ref -> _opt`) | `x64` (`skylake`) | `54 -> 20` (`-34`) | `6 -> 0` (`-6`) | **`2 -> 0`** | **`0 -> 0`** | `94.71 -> 5.10` | **18.57x** | `20.5 -> 3.8` | **5.39x** | `6.46 -> 4.84` (**1.33x**, 4 realistic orders) |
| **K3: Tick-Risk Fast Path** (`oms_tick_risk_ref -> _opt`) | `arm64` (`neoverse-v2`) | `32 -> 14` (`-18`) | `8 -> 0` (`-8`) | **`1 -> 0`** | **`0 -> 0`** | `21.13 -> 7.04` | **3.00x** | `21.0 -> 2.3` | **9.13x** | — |

---

## Detailed Closed-Loop Optimization Trajectories

### Kernel 1: 8-Byte FIX ASCII Fixed-Point Integer Parser (`k1_fix_ascii_price.rs`)

**Reference (`fix_parse_8_ref`):** Idiomatic byte-by-byte branchy loops checking every byte in `'0'..='9'` with early `-1` exit and serial decimal accumulation (`72` insns / `8` branches on x64; `81` insns / `8` branches on ARM64).

| Iteration | Candidate Transformation | `gnomon` Verification Result | Hardware Profile (`x64` / `arm64`) | Root Cause & Action Taken |
| --- | --- | --- | --- | --- |
| **Iter 1** | Naive SWAR validator `((u - 0x3030...) + 0x0606...) & 0xF0F0... == 0` + 3-stage SWAR parser | **`FALSIFIED`** (`181.7 ms`) | — *(rejected before profiling)* | **Bitwuzla caught classic inter-byte borrow/carry-bleed bug!** Counterexample: `word = 3545230315330415147` (`0x3133_3030_3837_2a2b`, ASCII `"+*780031"`). Bytes `'+'` (`0x2b`) and `'*'` (`0x2a`) borrow from byte 2 during `- 0x30` and carry back during `+ 0x06`, falsely passing validation (`opt = 199_770_031` vs `ref = -1`)! |
| **Iter 2** | Carry-free Lemire/simdjson SWAR validator `(hi_nibbles \| shifted_plus6) == 0x3333...` + 64-bit 3-stage SWAR parser (`if valid { s3 } else { -1 }`) | Contract **`PROVED`** (`60.1 ms`); monolithic `check-goal` `UNKNOWN` (`15s`, 7-deep 64-bit Horner chain in `ref`) | `x64`: `7.37` cyc (`2.53x`), `1` br; `arm64`: `4.68` cyc (`2.42x`), `1` br | Carry-bleed fixed; LLVM emitted 1 guard branch on `valid`. Also noticed `ref`'s single 7-deep 64-bit multiply chain triggered Bitwuzla's nonlinear chain cliff. |
| **Iter 3** | Force 0 branches via bitmask select `(((s3 + 1) & mask) - 1)` + `u & 0x0F0F...` + 32-bit Stage 3 (`u32 * 10_000`) | Contract **`PROVED`** (`46.7 ms`) | `x64`: `7.11` cyc (`2.58x`), `0` br; **`arm64`: `16.04` cyc (`0.72x` regression!)**, RT `3.8` (`2.84x`) | **Hardware discovery via `llvm-mca`:** Eliminating the single validity branch on ARM64 merged `x0 -> ... -> csinv x0` into a single basic block, exposing the full 16-cycle serial dependency chain on `neoverse-v2`! |
| **Iter 4** | Split even/odd lanes for ARM64 `madd` fusion, and parallel dual-32-bit halves (`lo`/`hi`) with 0 branches | — | `even/odd`: `arm64` `13.19` cyc (`0.87x`); `dual32`: `arm64` `13.04` cyc (`0.88x`), `x64` `8.81` cyc (`2.08x`) | Still worse than the guarded single-branch SWAR on BOTH x64 and ARM64. |
| **Iter 5 (Winner)** | Carry-free Lemire SWAR validator with fast-path guard (`8 -> 1` branch, 99.99%+ not-taken on valid FIX wire payloads) + `u & 0x0F0F...` + 3-stage SWAR (`10*a+b` -> `100*ab+cd` -> 32-bit `10_000*q0+q1`); factor `ref` into two 4-byte loops (`hi4 * 10_000 + lo4`) so Bitwuzla exploits the 4-byte/32-bit structure | **`check-goal` `PROVED`** (`9,375.7 ms`, ALL `2^64` inputs!) + **`check-contract` `PROVED`** (`45.9 ms`) | **`x64`: `7.10` cyc (`2.58x`), RT `2.67x`, `27` insns; `arm64`: `4.32` cyc (`3.17x`), RT `3.21x`, `25` insns; Host: `1.78x`** | Clean win on every metric on both architectures with 0 divs and 0 spills! |

---

### Kernel 2: 4-Venue Smart Order Router (`k2_sor_venue_router.rs`)

**Reference (`sor_route_4_ref`):** Computes all 4 venue fees via runtime unsigned division `(p_i * f_i) / bps_denom` (`4` hardware `div`s on both x64 and ARM64) and selects the best BUY/SELL venue with nested `if` chains (`97` insns / `103.60` cyc on x64; `66` insns / `49.07` cyc on ARM64).

| Iteration | Candidate Transformation | `gnomon` Verification Result | Hardware Profile (`x64` / `arm64`) | Root Cause & Action Taken |
| --- | --- | --- | --- | --- |
| **Iter 1** | Naive 40-bit multiply-shift reciprocal `((x * 109_951_163) >> 40)` + unified BUY/SELL min-tree | **`FALSIFIED`** (`864.2 ms` on 1-venue check / `340.9 ms` on Euclidean division spec) | `x64`: `16.49` cyc (`7.53x`), `0` div; `arm64`: `9.14` cyc (`5.27x`), `0` div | **Bitwuzla caught subtle reciprocal precision overflow!** Counterexamples: `x = 499_059_999` (`opt = 49_906 != ref = 49_905`) and `x = 495_219_999` (`49_522 != 49_521`) — `2^40 / 10_000` only stays exact up to `494_384_724 < 500_000_000`! |
| **Iter 2** | Exact pre-shifted reciprocal `(((x & 0x00FF_FFFF) >> 4) * 54_975_582) >> 35` (exact for all `x <= 16_777_215`, covering `1 <= p_i <= 32_000, 0 <= f_i <= 500`); prove Layer-1 law `sor-div-10k-uncond` (`stratum -> mul`) | Law **`PROVED`** (`1,691.2 ms`), but monolithic 4-venue `check-goal` `UNKNOWN` (`10s`) | `x64`: `29.26` cyc (`3.54x`), `2` br; `arm64`: `9.49` cyc (`5.17x`), `0` br | Expanding `stratum -> mul` left 4 64-bit multiplies in the SMT query. **Solution:** Reverse the law to **`sor-div-10k-fold` (`mul -> stratum`)** so egglog folds all 4 reciprocals in `opt` into the Layer-1 Stratum `sor_div_10k`! |
| **Iter 3** | Pre-negate all 4 prices `p0s..p3s` up front before fee computation | `sor-div-10k-fold` didn't fire (LLVM hoisted `block/br_if` before `fee0..fee3`) | **`x64`: `register_spills: 1`** (`18.24` cyc, `1` br); `arm64`: `12.10` cyc, `0` spills | **`llvm-mca` caught an x86-64 register spill** caused by keeping all 4 negated prices live across the 4 fee multiplications! |
| **Iter 4** | Pair venues `(0, 1)` then `(2, 3)` with `if side != 0 { fee - p } else { p + fee }` and `sor-div-10k-fold` | **`check-goal` `PROVED`** (`2,801.9 ms`, `sor-div-10k-fold` fired!) | `x64`: `19.56` cyc (`5.30x`), `0` spills, **`3` branches**; `arm64`: `15.10` cyc (`3.25x`), `0` br | Register spill eliminated (`1 -> 0`), but x64 still emitted 3 conditional branches around stack-passed `q1..q3` loads. |
| **Iter 5 (Winner)** | **Packed `(venue << 32 \| qty)` bitmask min-tree** interleaved by pairs `(0, 1)` and `(2, 3)` + verified exact reciprocal folded by TCB-admitted law `sor-div-10k-fold` | **`prove-law` `PROVED`** (`1,654.7 ms`, TCB digest `e668c7ee...`) + **`check-goal` `PROVED`** (`2,834.3 ms`, `350 -> 266` nodes, 0 cliff warnings) + **`check-contract` `PROVED`** (`30.1 ms`) | **`x64`: `18.30` cyc (`5.66x`), `0` br, `0` div, `0` spills; `arm64`: `12.10` cyc (`4.06x`), RT `6.00x`, `0` br, `0` div, `0` spills; Host: `1.16x`** | Zero branches, zero divs, and zero register spills on **both** x64 and ARM64! |

---

### Kernel 3: Combined Tick-Size Alignment + Pre-Trade Risk Fast Path (`k3_oms_tick_risk_fastpath.rs`)

**Reference (`oms_tick_risk_ref`):** Uses runtime unsigned remainder `u_price % u_tick` (`2` hardware `div`s on x64 including the 32/64-bit fast-path split, `1` `udiv` on ARM64) and nested risk branches (`54` insns / `6` br / `94.71` cyc on x64; `32` insns / `8` br / `21.13` cyc on ARM64).

| Iteration | Candidate Transformation | `gnomon` Verification Result | Hardware Profile (`x64` / `arm64`) | Root Cause & Action Taken |
| --- | --- | --- | --- | --- |
| **Iter 1** | Replace `% tick` with `price & !(tick - 1)`, branchless XOR `abs_diff`, bitwise conjunction of all gates, using `kill_switch != 1` | **`FALSIFIED`** on BOTH `check-goal` (`497.2 ms`) AND `check-contract` (`96.4 ms`)! | — *(rejected before profiling)* | **Bitwuzla caught non-boolean kill-switch bypass!** Counterexample: `kill_switch = 1_073_741_824` (`0x4000_0000`, e.g., a bitmask halt flag), `price = 750_847_743`, `tick = 1`: `opt` accepted and returned `750_847_743`, whereas `ref` and `ens_tick_risk` mandate `0` for ALL `kill_switch != 0`! |
| **Iter 2** | Fix `ok_kill = kill_switch == 0`; keep inline 64-bit `aligned * qty` and `diff * 10_000 <= ref_price * collar_bps` | `UNKNOWN` (`15s` on `price, qty <= 10^9`); `check-contract` **`PROVED`** (`261.4 ms`) at `1M` bounds | `x64`: `9.06` cyc (`10.45x`), `0` br, `0` div; `arm64`: `7.04` cyc (`3.00x`), `0` br, `0` div | Monolithic Bitwuzla could not CSE `aligned_ref * qty` with `aligned_opt * qty` before bit-blasting two 64x64 multipliers. Gnomon's own cliff diagnostic recommended extracting nonlinear sub-expressions into Layer-1 Strata. |
| **Iter 3 (Winner)** | Extract pure total `notional_le` and `collar_le` into Layer-1 Strata (`strata_l1.rs`, bit-for-bit identical to native `#[inline(always)]` bodies); flatten `oms_tick_risk_opt` to `price & !(tick - 1)` + bitwise conjunction `ok_kill & ok_pos & ok_notional & ok_collar` | **`check-goal` `PROVED`** (`124.0 ms`, full `price, qty <= 10^9`, all 7 pow2 ticks `{1..64}`, `138 -> 112` nodes, 0 cliff warnings!) + **`check-contract` `PROVED`** (`27.3 ms`) | **`x64`: `5.10` cyc (`18.57x`), RT `5.39x`, `20` insns, `0` br, `0` div, `0` spills; `arm64`: `7.04` cyc (`3.00x`), RT `9.13x`, `14` insns, `0` br, `0` div, `0` spills; Host: `1.33x`** | UF-CEGAR congruence collapses the verification time by >120x (`>15s -> 124 ms`) while native inlining unlocks `18.57x` x64 and `3.00x` ARM64 (`9.13x` RT) cycle speedups! |

---

## Reproducing All Checks & Benchmarks

Run the standalone verification and profiling script (uses only `rustc` and `target/release/gnomon`, zero `cargo` invocations):

```bash
./examples/closed_loop_demo/verify_and_profile.sh
```

Files in `examples/closed_loop_demo/`:
- `strata_l1.rs` — Pure, total Layer-1 Strata primitives (`sor_div_10k`, `notional_le`, `collar_le`).
- `strata_l1_laws.rs` — Unconditional Layer-1 folding law harness (`sor-div-10k-fold`).
- `k1_fix_ascii_price.rs` — Kernel 1 (`fix_parse_8_ref`, `fix_parse_8_opt`, `ens_fix_parse_8`).
- `k2_sor_venue_router.rs` — Kernel 2 (`sor_route_4_ref`, `sor_route_4_opt`, `req_sor`, `ens_sor`).
- `k3_oms_tick_risk_fastpath.rs` — Kernel 3 (`oms_tick_risk_ref`, `oms_tick_risk_opt`, `req_tick_risk`, `ens_tick_risk`).
- `verify_and_profile.sh` — Full dual-target compile (`-D warnings`), `define-op`, `prove-law`, `check-goal`, `check-contract`, and `profile --compare --targets x64,arm64 --bench` runner.
- `.gitignore` — Ignores `out/` and `*.wasm`.
