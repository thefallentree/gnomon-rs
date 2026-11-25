# Project Gnomon Roadmap — Completed 7-Step Execution Report

## 1. North Star: Specialize Deeply First (Trading / OMS) → Generalize Cleanly Next

Project Gnomon is a **Verified AI Systems & Performance Engineering Engine** targeting native **x86-64 and ARM64** systems code written in **strict `#![no_std]` Rust** (with `rustc`/LLVM trusted for native lowering, and deterministic `wasm32` / `GnomonIR` serving as the tiny, Kani-verified semantic verification layer).

**Status: ALL 7 STEPS COMPLETE & VERIFIED GREEN.**
- **Vertical Beachhead Completed:** E2E Verified, Ultra-Low-Latency OMS + Tick-to-Trade Core (`Gnomon-T2T`, all **15 Strata `S1.1–S4.2`** + **6 verified perf-opt pairs `S4.3`** + **11 separate `*_buggy.rs` files**, `27` `.rs` files total).
- **Zero Domain Lock-In Proved:** Not a single line of `gnomon-kernel`, `gnomon-wasm`, `gnomon-sieve`, or `gnomon-mcp` is hard-coded to trading. Step 6 verified and profiled **4 real-world non-trading vertical packs** (`24/24` live verdicts) on the 100% unmodified engine.

---

## 2. Completed Foundation & Step-by-Step Measured Results

| Step | Engine & Artifact Deliverables | Hard Exit Gate & Live Measured Results | Status |
| --- | --- | --- | :---: |
| **Foundation** *(Phase 1 + 2A)* | `#![no_std]` `#![forbid(unsafe_code)]` `gnomon-kernel` (24B `IrSlot`), `gnomon-wasm` lifter + Wasmtime Stage-1 fuzzer, `egglog` v3.0 + Bitwuzla + Ackermann UF CEGAR, `stitch_core` consolidation, CLI & MCP. | **30/30** corpus round-trip, **30/30** mutants falsified (median `3.63 ms`), **Proof 1 (`proof1_cliff`, 10 s cap)**: Gnomon `10/10` (`22.5–505.4 ms`, `>20×–>445×`) vs Flat Bitwuzla `2/10` (`8` timeouts), 1-bit `N=8` bug `FALSIFIED` in `13.27 ms`. | **DONE** |
| **Step 1a** | `gnomon check-contract` (CLI + MCP): `requires ⇒ !trap ∧ ensures`, inductive multi-op `I(s) ⇒ I(op(s))`, inline `gnomon_assume`/`gnomon_assert`. *(Zero TCB churn)* | **`S1.1`** (`checked_notional`, `price_collar_ok`) + **`S3.1`** (`child_fsm_step`, 8-state lifecycle): zero overflow bypass, zero terminal resurrection, zero dropped fills during `PendingCancel`; all mutants `FALSIFIED`. | **DONE** |
| **Step 1b** | Strict Rust → Strata Bridge (`-t rust`, Wasm `import "stratum"` → `CallTarget::Stratum`, `emit-rust` → `strata.rs`, `lift --lower`). *(Zero TCB churn)* | **`S1.2`–`S1.4`**, **`S2.1`** (`spsc_ring`), **`S2.2`** (`order_slab_table`), **`S3.2`** (`parent_child_oms`), **`S3.3`** (`pretrade_risk_gate`): 100% strict `#![no_std]` Rust proved `PROVED` for **zero over-fill**, **zero credit leak**, and **kill-switch enforcement**. | **DONE** |
| **Step 2** | `--ignore-dead-stack` (`SP_out == SP_in`), intra-memory **`SliceFrame`**, **`wasm-smith`** differential & blowup fuzzer (`wasm_smith_fuzz`), static SMT-cliff estimator. *(Zero TCB churn)* | **`S2.3`** (`wire_rx_decode`, ITCH/ExecReport) + **`S2.4`** (`wire_tx_encode`, OUCH): zero-copy `&[u8] → &mut [u8]` refined to stack-using Rust, `SliceFrame`-isolated, panic-free on truncated packets. **`wasm-smith` Gate:** **1,000/1,000** lifted & round-tripped, **4,785** 3-way diff checks (`0` mismatches), `egglog` p99 `129.256 ms` (`0` blowups), **3** real `gnomon-sieve` bugs caught & fixed. | **DONE** |
| **Step 3** | **TCB v2:** `ValType::{F32, F64, V128}`, `MemWidth::B16`, 100 `UnOp`s, 141 `BinOp`s, pure `#![no_std]` IEEE-754 `fp.rs`, Bitwuzla `QF_ABVFP`/`BV128`, `gnomon-wasm` FP/SIMD lifter/fuzzer. | **15/15 Kani proofs green** (`0` failures, `11m54.38s`, 0 stubs/unwindsets); **`gnomon-wasm`:** **27,768** 3-way bit-exact differential checks (incl. **13,896** FP/SIMD corner cases), **0** mismatches; **`S3.4`** (`l2_book_sweep_v128`) & **`S3.5`** (`signal_vwap_var_v128`) proved `!is_nan`, `-0.0` safe, `bid_tick < ask_tick`, 5/5 mutants `FALSIFIED`. | **DONE** |
| **Step 4** | Layer-4 E2E OMS (`S4.1` + `S4.2`) + Native **x64 & ARM64 Performance Oracle** (`gnomon profile` CLI + 8th MCP tool `gnomon_profile`: `rustc -O3 --emit=asm` + `llc` + `llvm-mca` + spill/branch/div/SIMD counters + `--bench`). | **`S4.1` & `S4.2`:** **24/24** exact verdicts (**17/17 `PROVED`**, **7/7 mutants `FALSIFIED`**) with genuine `stratum::*` composition (`order_id_mix`, `checked_notional`, `price_collar_ok`), `SliceFrame` RX isolation, and `--ignore-dead-stack`. **`S4.3` (6 perf pairs):** **8/8 `PROVED`**, `1.14×–3.02×` x64 cycles, `1.02×–6.24×` ARM64 cycles, `div 1->0`, `br 7->0/23->0/45->0`, x64 `spills 19->0`, stack `56B/64B->0B`, ARM64 `NEON 0->14`, host VWAP **`3.09×`** (`9.99->3.24 ns/op`). | **DONE** |
| **Step 5** | **Proof 2 — Compute-Matched 3-Arm Ablation (`proof2_oms_ablation` + `proof2_ablation_gate`)** on `Gnomon-T2T` OMS (`3,000 ms/task` cap): Arm A (Flat L0) vs Arm B (Modular Helpers) vs Arm C (Full Gnomon). | **Arm C `10/10` (`5.0×` Arms A & B `2/10`)** (gate `>= 2.0×`); median SMT speedup **`99.5×` vs A / `103.4×` vs B** (gate `>= 5.0×`); cross-rung reuse **`100.0%` (`10/10`)** Strata / **`70.0%` (`7/10`)** R1–2 `egglog` laws (gate `>= 30%`); **2/2** soundness mutants `FALSIFIED`, **0** unsound admissions. | **DONE** |
| **Step 6** | **Horizontal Generalization (`examples/vertical_packs/`):** Zero engine changes — 4 real-world non-trading `#![no_std]` Rust vertical packs + buggy mutants. | **4/4 packs** (`ai_q8_0_quant`, `db_parquet_varint_slice`, `net_wireguard_replay`, `cloud_quota_saga`): `8/8` `-D warnings` clean & round-trip lifted, **24/24** live verdicts (**16/16 `PROVED`**, **8/8 `FALSIFIED`**), live `gnomon profile` x64 (`skylake`) & ARM64 (`neoverse-v2`) speedups up to **2.61×** x64 / **1.57×** ARM64 (`NEON 13->33`). | **DONE** |
| **Step 7** | **Realistic Hot-Path Benchmarking + Live Blind AI Closed-Loop Opt + Full CI Lock-In:** `--bench-inputs` / `--bench-preset` (`default \| ascii-digits \| oms-valid`) in `gnomon profile`, `e2e_s4_and_verticals.rs` CI lock-in (**111** workspace tests), `AGENTS.md` sync, & `examples/closed_loop_demo/` showcase. | Realistic host speedups on `S4.3` (SWAR **2.31×**, FSM **1.93×**, OUCH **2.15×**); blind AI agent autonomously proved & sped up K1 FIX 8B (**2.58×** x64 / **3.17×** ARM64 / **1.78×** host), K2 4-Venue SOR (**5.66×** x64 / **4.06×** ARM64 / `div 4->0` / **1.16×** host), and K3 Tick-Risk (**18.57×** x64 / **3.00×** ARM64 / `div ->0` / **1.33×** host), catching 3 real correctness bugs & 2 microarch regressions mid-loop. | **DONE** |

---

## 3. E2E Verified OMS (`Gnomon-T2T`): All 15 Delivered Strata + `S4.3` Perf Pairs

All 27 fixtures live in [`examples/oms_strata/`](examples/oms_strata/README.md) and are built & round-trip verified by [`examples/oms_strata/build.sh`](examples/oms_strata/build.sh).

### Layer 1 — Pure Fixed-Point, Barrett, Hash & SWAR Strata *(Pure total, zero memory)*
| Stratum | OMS Role | Verified Contract (`requires ⇒ !trap ∧ ensures`) | Step 4 Native Hardware Delta (`S4.3`) |
| --- | --- | --- | --- |
| **`S1.1`** [`s1_1_notional_collar.rs`](examples/oms_strata/s1_1_notional_collar.rs) | Overflow-safe `price * qty` & bps price collar | Zero `i64` wraparound; exact collar bounds; `ref_price == 0` safe | Composed as Layer-1 Stratum in `S3.3` & `S4.2` |
| **`S1.2`** [`s1_2_barrett_tick_fee.rs`](examples/oms_strata/s1_2_barrett_tick_fee.rs) | Tick-size rounding, fee-bps, & Barrett hash-bucket `fastmod` | Exact equivalence to `div`/`rem` under `req_barrett` / `req_barrett_pow2` | **Pair 1:** `div/udiv 1->0`; x64 **1.48×** cyc (**2.50×** RTh), ARM64 **6.24×** cyc (**6.50×** RTh), host **1.21×** |
| **`S1.3`** [`s1_3_order_id_mix.rs`](examples/oms_strata/s1_3_order_id_mix.rs) | Bijective 64-bit order-ID hash (`fmix64`) | Bijection round-trip & UF congruence across probes *(past SMT cliff)* | **Pair 3:** x64 `12x_spill -> 4x` **spills `19->0`**, stack `56B->0B`, **1.14×** cyc; ARM64 **0 spills** |
| **`S1.4`** [`s1_4_swar_fix_price.rs`](examples/oms_strata/s1_4_swar_fix_price.rs) | 8-byte parallel ASCII FIX digit validator & 4-byte parser | Exact equivalence to byte loop (`0` carry-bleed) | **Pair 2:** **br `7->0`** on x64 & ARM64; x64 **3.02×** cyc / **3.00×** RTh, ARM64 **4.59×** RTh |

### Layer 2 — Zero-Copy Ring, Slab & Wire Strata *(Linear memory, slices, `SliceFrame` isolation)*
| Stratum | OMS Role | Verified Contract | Step 4 Native Hardware Delta (`S4.3`) |
| --- | --- | --- | --- |
| **`S2.1`** [`s2_1_spsc_ring.rs`](examples/oms_strata/s2_1_spsc_ring.rs) | Lock-free RX / TX / Journal ring buffer | Power-of-2 mask, `tail - head <= cap`, no OOB/overwrite | Composed in `S4.1` journal & `S4.2` TX ring |
| **`S2.2`** [`s2_2_order_slab_table.rs`](examples/oms_strata/s2_2_order_slab_table.rs) | Flat order slab + open-addressing map (`stratum::order_id_mix`) | Zero `malloc`, `live + free == CAP`, unique `cl_ord_id`, no double-free | Composed in `S4.1` ExecReport pipeline |
| **`S2.3`** [`s2_3_wire_rx_decode.rs`](examples/oms_strata/s2_3_wire_rx_decode.rs) | Zero-copy `&[u8]` ITCH / ExecReport decoder | Panic-free on truncated packets; `opt ≡ ref --ignore-dead-stack`; RX `SliceFrame` | Zero shadow-stack direct BE loads |
| **`S2.4`** [`s2_4_wire_tx_encode.rs`](examples/oms_strata/s2_4_wire_tx_encode.rs) | Zero-copy `&mut [u8]` OUCH 48B outbound encoder | Exact BE wire layout; `opt ≡ ref --ignore-dead-stack`; `SliceFrame` TX-only | **Pair 5:** stack **`56B->0B`** (x64) / **`64B->0B`** (ARM64), spills `1->0`, **2.20×** x64 / **1.53×** ARM64 cyc |

### Layer 3 — Inductive OMS FSMs, SEC 15c3-5 Risk, `v128` Book & `f32x4` Signal Strata
| Stratum | OMS Role | Verified Contract (`I(s) ⇒ I(op(s))`) | Step 4 Native Hardware Delta (`S4.3`) |
| --- | --- | --- | --- |
| **`S3.1`** [`s3_1_child_fsm.rs`](examples/oms_strata/s3_1_child_fsm.rs) | 8-state child order lifecycle FSM | No terminal resurrection; fills during `PendingCancel` never dropped; pessimistic `worst_case_leaves` | **Pair 4:** **br `23->0`** (x64) / **`45->0`** (ARM64); **1.66×** x64 / **2.21×** ARM64 cyc |
| **`S3.2`** [`s3_2_parent_child_oms.rs`](examples/oms_strata/s3_2_parent_child_oms.rs) | Parent → `Child[K]` hierarchy | **Zero Over-Fill:** `parent.cum + sum(worst_case_leaves) <= target`; exact fill roll-up | Composed in `S4.1` & `S4.2` |
| **`S3.3`** [`s3_3_pretrade_risk_gate.rs`](examples/oms_strata/s3_3_pretrade_risk_gate.rs) | SEC 15c3-5 / MiFID II risk firewall (`S1.1` Strata) | `kill_switch ⇒ reject`; `open_notional == sum(live)`; zero double cancel release | Combined branchless risk+FSM in **Pair 4** |
| **`S3.4`** [`s3_4_l2_book_sweep_v128.rs`](examples/oms_strata/s3_4_l2_book_sweep_v128.rs) | Fixed-depth L2 Order Book + `v128` price-level sweep | Never crossed (`best_bid < best_ask`); `i32x4`/`i64x2` bit-exact equivalence to scalar ref | Composed in `S4.2` (`sweep_fair_v128 ≡ _scalar`) |
| **`S3.5`** [`s3_5_signal_vwap_var_v128.rs`](examples/oms_strata/s3_5_signal_vwap_var_v128.rs) | `f32x4` VWAP quote calc + portfolio notional/VaR | `QF_ABVFP` proved `!is_nan`, `-0.0` safe, `bid_tick < ask_tick` | **Pair 6:** br `7->1`/`6->1`, **NEON `0->14`**, **1.23×** x64 / **1.45×** ARM64 cyc, host **`3.09×`** (`3.24 ns/op`) |

### Layer 4 — E2E Verified OMS Pipelines
| Stratum | OMS Pipeline | Verified Global E2E Results (`24/24` Exact Verdicts) |
| --- | --- | --- |
| **`S4.1`** [`s4_1_oms_on_exec_report.rs`](examples/oms_strata/s4_1_oms_on_exec_report.rs) | `S2.3` decode → `S2.2` slab (`stratum::order_id_mix`) → `S3.1`/`S3.2` FSM → `S3.3` risk → `S2.1` journal | **8/8 `PROVED`** (`inv_oms_e2e`, `PendingCancel` fills preserved, zero double cancel credit, `opt ≡ ref --ignore-dead-stack` in `87.3 ms`, RX `SliceFrame` in `71.0 ms`); **3/3 mutants `FALSIFIED`** (`33.0–53.3 ms`). |
| **`S4.2`** [`s4_2_oms_on_tick_or_order.rs`](examples/oms_strata/s4_2_oms_on_tick_or_order.rs) | `S2.3` decode → `S3.4`/`S3.5` book & fair → `S3.2`/`S3.3` (`S1.1` Strata) → `S2.4` OUCH → `S2.1` TX | **9/9 `PROVED`** (`inv_t2t_oms`, kill-switch `readonly` `SliceFrame`, RX `SliceFrame`, `sweep_fair_v128 ≡ _scalar` in `687.5 ms`, `opt ≡ ref --ignore-dead-stack` in `14.0 s`); **4/4 mutants `FALSIFIED`**. |

---

## 4. Proof 2 (`proof2_oms_ablation`) Held-Out Rung 3–4 Detail (`3,000 ms/task` Cap)

| Held-Out OMS Task | Rung | Arm A (Flat L0) | Arm B (Helpers) | Arm C (Full Gnomon) | R1–2 Laws | C vs A | C vs B |
| --- | :---: | --- | --- | --- | ---: | ---: | ---: |
| `T01_oms_order_id_roundtrip_d2` | R3 | `TMO (>3000ms)` | `TMO (>3000ms)` | **`PROVED (27.0ms)`** | 1 | `>114.6×` | `>113.6×` |
| `T02_oms_order_id_roundtrip_d4` | R4 | `TMO (>3000ms)` | `TMO (>3000ms)` | **`PROVED (28.5ms)`** | 1 | `>110.5×` | `>111.0×` |
| `T03_oms_premix_diff_sq_d2` | R3 | `TMO (>3000ms)` | `TMO (>3000ms)` | **`PROVED (29.0ms)`** | 0 (UF) | `>114.1×` | `>113.7×` |
| `T04_oms_premix_diff_sq_d4` | R4 | `TMO (>3000ms)` | `TMO (>3000ms)` | **`PROVED (30.4ms)`** | 0 (UF) | `>106.6×` | `>105.7×` |
| `T05_oms_multikey_slab_barrett_lookup` | R3 | `TMO (>3000ms)` | `TMO (>3000ms)` | **`PROVED (44.5ms)`** | 1 | `>70.0×` | `>70.2×` |
| `T06_oms_multikey_slab_roundtrip_probe` | R4 | `TMO (>3000ms)` | `TMO (>3000ms)` | **`PROVED (31.2ms)`** | 2 | `>100.3×` | `>101.1×` |
| `T07_oms_dual_mem_rx_journal_hoist_d4` | R3 | `PROVED (1806.9ms)` | `PROVED (1716.2ms)` | **`PROVED (113.8ms)`** | 1 | `15.9×` | `15.1×` |
| `T08_oms_dual_mem_rx_journal_hoist_d8` | R4 | `TMO (>3000ms)` | `TMO (>3000ms)` | **`PROVED (515.8ms)`** | 1 | `>6.1×` | `>6.2×` |
| `T09_oms_risk_notional_mix_pipe` | R3 | `TMO (>3000ms)` | `TMO (>3000ms)` | **`PROVED (31.8ms)`** | 0 (UF) | `>98.6×` | `>105.7×` |
| `T10_oms_vwap_v128_book_hoist` | R4 | `PROVED (504.8ms)` | `PROVED (485.4ms)` | **`PROVED (51.7ms)`** | 1 | `9.8×` | `9.4×` |
| `M01_buggy_order_id_1bit_flip` *(control)* | R4 | `FALSIF (11.1ms)` | `FALSIF (10.7ms)` | **`FALSIF (24.2ms)`** | 1 | kernel-confirmed | — |
| `M02_buggy_notional_wraparound_bypass` *(control)* | R4 | `FALSIF (381.1ms)` | `FALSIF (386.0ms)` | **`FALSIF (1174.4ms)`** | 0 | kernel-confirmed | — |

---

## 5. Step 6 Horizontal Generalization (`examples/vertical_packs/`)

Zero engine changes — all 4 non-trading vertical packs compiled cleanly (`-D warnings`), round-trip lifted (`8/8`), and verified live against `target/release/gnomon` (**24/24** exact verdicts: **16/16 `PROVED`**, **8/8 `FALSIFIED`**):
1. **AI Inference (`ai_q8_0_quant.rs`):** 4-lane `f32x4` `Q8_0` quantizer (`q8_0_quant_4_v128 ≡ _ref` `112.1 ms`, finite/no-NaN safety `98.9 ms`, inline contract `122.1 ms`; zero-block `NaN` & `trunc`-bias mutants `FALSIFIED`; `gnomon profile`: **2.61×** x64 cyc, **1.57×** ARM64 cyc with **NEON `13->33`** and br `2->0`).
2. **Columnar DB / Parquet (`db_parquet_varint_slice.rs`):** Zero-copy `&[u8]` LEB128 varint + ZigZag (`opt ≡ ref --ignore-dead-stack` `373.9 ms`, `SliceFrame readonly` `8.3 ms`, ZigZag roundtrip `29.6 ms`, branchless equiv `88.1 ms`; short-read & shift-overflow mutants `FALSIFIED`; `gnomon profile`: x64 br `4->0` / `1.10×` RTh, ARM64 br `3->0` / **1.50×** cyc).
3. **Networking / WireGuard (`net_wireguard_replay.rs`):** RFC 6479 64-bit sliding anti-replay window (`init_replay`+`accept_nonce` inductive suite `13.3 ms`, duplicate-rejection `107.4 ms`, large-jump clear `196.6 ms`, branchless equiv `55.9 ms`; shift-64 wrap mutant `FALSIFIED`; `gnomon profile`: x64 br `2->0`, ARM64 `0` br `csel`).
4. **Cloud Distributed Quota Saga (`cloud_quota_saga.rs`):** 4-slot quota reservation/commit/cancel saga (inductive conservation suite `11.0 s`, no-double-release `7.5 s`, no-double-commit `1.4 s`; double-release mutant `FALSIFIED`).

---

## 6. Architectural Scope Boundaries Preserved

- **No x86-64 / ARM64 binary lifters:** `rustc`/LLVM is trusted for native lowering; exact x64 (`skylake`) & ARM64 (`neoverse-v2`) instruction, cycle, RTh, branch, `div`, stack, register-spill, and SIMD feedback comes directly from `rustc --emit=asm` / `--emit=llvm-ir` + LLVM-23 `llc` + `llvm-mca`.
- **Deterministic single-threaded verification semantics:** State contracts target data-structure invariants, trap-freedom, relational pre/postconditions, and `MemoryFrame`/`SliceFrame` isolation.
- **Strict `#![no_std]` Rust authoring:** Engineers and AI agents write Rust (`-t rust` + `emit-rust` `strata.rs` bindings); `.ir` JSON remains the canonical wire/debug schema.
