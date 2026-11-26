# OMS Strata Suite (`Gnomon-T2T`: `S1.1–S4.2` + `S4.3` Perf Pairs)

Strict `#![no_std]` Rust fixtures targeting `wasm32-unknown-unknown` (and portable native `x86_64` / `aarch64` for `gnomon profile`) implementing the complete **15-Stratum E2E Verified OMS (`Gnomon-T2T`)** (`S1.1–S1.4` [4] + `S2.1–S2.4` [4] + `S3.1–S3.5` [5] + `S4.1–S4.2` [2]) plus **6 formally verified performance-optimization pairs (`S4.3`)** and **11 separate `*_buggy.rs` mutant files** (`S1.1`/`S1.2`/`S1.4` embed mutants inline; `15 + 1 + 11 = 27` `.rs` files total).

## Build & Round-Trip Lift Verification

```bash
./build.sh
```

`build.sh` compiles all **27** `.rs` files (`s1_1` through `s4_3` + all `*_buggy.rs`) with `rustc --target wasm32-unknown-unknown --crate-type=cdylib -O -C panic=abort -D warnings` (adding `-C target-feature=+simd128` for `s3_4`, `s3_5`, `s4_2`, `s4_3`), registers the Layer-1 Strata (`order_id_mix`, `checked_notional`, `price_collar_ok`) into `out/oms_strata_state.json`, and validates every `.wasm` with `gnomon lift --emit-wasm` (`--lower` for Stratum-linked Layer 2–4 modules). Outputs are written to `out/` (git-ignored).

---

## Layer-1 Strata Registration (Required for `S2.2`, `S3.3`, `S4.1`, `S4.2`)

Layer 2–4 modules compose Layer-1 Strata via `#[link(wasm_import_module = "stratum")]` (`CallTarget::Stratum` in `GnomonIR`). Populate a state file once from the repo root:

```bash
GNOMON=./target/release/gnomon
DIR=examples/oms_strata
STATE=$DIR/out/oms_strata_state.json
rm -f "$STATE"

$GNOMON --state "$STATE" define-op --name order_id_mix --layer 1 "$DIR/s1_3_order_id_mix.rs"
$GNOMON --state "$STATE" define-op --name checked_notional --entry checked_notional --layer 1 "$DIR/s1_1_notional_collar.rs"
$GNOMON --state "$STATE" define-op --name price_collar_ok --entry price_collar_ok --layer 1 "$DIR/s1_1_notional_collar.rs"
```

---

## Complete Catalog of All 15 OMS Strata (`S1.1–S4.2`) + `S4.3`

### Layer 1 — Pure Fixed-Point, Barrett, Hash & SWAR Strata

| Stratum | File(s) | Key Exports & Verified Properties | Buggy Mutants (`FALSIFIED`) |
| --- | --- | --- | --- |
| **`S1.1`** | [`s1_1_notional_collar.rs`](s1_1_notional_collar.rs) | `checked_notional`, `price_collar_ok` + `req_*`/`ens_*` — zero `i64` wraparound, exact bps collar, `ref_price == 0` safe | `checked_notional_buggy_overflow`, `price_collar_buggy_div0`, `price_collar_buggy_overflow` |
| **`S1.2`** | [`s1_2_barrett_tick_fee.rs`](s1_2_barrett_tick_fee.rs) | `tick_round_down`, `fee_bps_calc`, `bucket_index_barrett_u32` + `req_*`/`ens_*` — exact `div`/`rem` equivalence under `req_barrett` / `req_barrett_pow2` | `tick_round_down_buggy_offbytick`, `fee_bps_calc_buggy_overflow`, `bucket_index_barrett_buggy_offbyone` |
| **`S1.3`** | [`s1_3_order_id_mix.rs`](s1_3_order_id_mix.rs) | `order_id_mix` (`fmix64`), `order_id_unmix`, `order_id_roundtrip`, `post_identity_i64` — bijective 64-bit order-ID hash Stratum | — *(used as Layer-1 Stratum across `S2.2`, `S4.1`, and UF CEGAR cliffs)* |
| **`S1.4`** | [`s1_4_swar_fix_price.rs`](s1_4_swar_fix_price.rs) | `is_8_ascii_digits_swar ≡ is_8_ascii_digits_ref`, `parse_4_ascii_digits_swar ≡ parse_4_ascii_digits_ref` — zero carry-bleed branchless SWAR | `is_8_ascii_digits_swar_buggy_carry` |

### Layer 2 — Zero-Copy Ring, Slab & Wire Codec Strata

| Stratum | File(s) | Key Exports & Verified Properties | Buggy Mutants (`FALSIFIED`) |
| --- | --- | --- | --- |
| **`S2.1`** | [`s2_1_spsc_ring.rs`](s2_1_spsc_ring.rs), [`_buggy.rs`](s2_1_spsc_ring_buggy.rs) | `init_ring`, `ring_push`, `ring_pop`, `inv_spsc_ring`, `contract_push_full_rejected`, `contract_push_pop_roundtrip` — `tail - head <= cap`, no overwrite | `ring_push_buggy_overwrite`, `ring_push_buggy_bad_mask` |
| **`S2.2`** | [`s2_2_order_slab_table.rs`](s2_2_order_slab_table.rs), [`_buggy.rs`](s2_2_order_slab_table_buggy.rs) | `init_slab`, `slab_insert`, `slab_lookup`, `slab_free`, `inv_slab`, `contract_insert_lookup_free_roundtrip`, `contract_double_free_rejected` *(imports `stratum::order_id_mix`)* | `slab_free_buggy_double_free`, `slab_insert_buggy_duplicate_id` |
| **`S2.3`** | [`s2_3_wire_rx_decode.rs`](s2_3_wire_rx_decode.rs), [`_buggy.rs`](s2_3_wire_rx_decode_buggy.rs) | `itch_decode_opt ≡ itch_decode_ref` (`--ignore-dead-stack`), `itch_validate_header`, `SliceFrame` RX read-only isolation, panic-free on truncated packets | `itch_decode_buggy_short_pkt`, `itch_decode_buggy_endian`, `itch_decode_buggy_clobber_rx` |
| **`S2.4`** | [`s2_4_wire_tx_encode.rs`](s2_4_wire_tx_encode.rs), [`_buggy.rs`](s2_4_wire_tx_encode_buggy.rs) | `ouch_encode_opt ≡ ouch_encode_ref` (`--ignore-dead-stack`), exact BE wire layout, `SliceFrame` proves only TX slice modified | `ouch_encode_buggy_overrun`, `ouch_encode_buggy_endian`, `ouch_encode_buggy_short_buf` |

### Layer 3 — Inductive OMS FSMs, SEC 15c3-5 Risk, `v128` Book & `f32x4` Signal Strata

| Stratum | File(s) | Key Exports & Verified Properties | Buggy Mutants (`FALSIFIED`) |
| --- | --- | --- | --- |
| **`S3.1`** | [`s3_1_child_fsm.rs`](s3_1_child_fsm.rs), [`_buggy.rs`](s3_1_child_fsm_buggy.rs) | 8-state child lifecycle (`init_empty`, `submit_new`, `on_ack`, `request_cancel`, `request_replace`, `on_fill`, `on_cancel_ack`, `on_replace_ack`, `on_reject`), `inv_child_fsm` — no terminal resurrection, fills during `PendingCancel` never dropped, pessimistic `worst_case_leaves` | `on_fill_buggy_drops_pending_cancel`, `on_cancel_ack_buggy_resurrects_or_overwrites_filled`, `request_replace_buggy_optimistic_leaves` |
| **`S3.2`** | [`s3_2_parent_child_oms.rs`](s3_2_parent_child_oms.rs), [`_buggy.rs`](s3_2_parent_child_oms_buggy.rs) | Parent → `Child[K]` hierarchy (`init_parent`, `route_child`, `on_child_*`, `request_child_*`), `inv_parent_child_oms` — **Zero Over-Fill** (`parent.cum + sum(worst_case_leaves) <= target`) & exact fill roll-up | `request_child_cancel_buggy_optimistic` + `contract_no_inflight_overfill_buggy` |
| **`S3.3`** | [`s3_3_pretrade_risk_gate.rs`](s3_3_pretrade_risk_gate.rs), [`_buggy.rs`](s3_3_pretrade_risk_gate_buggy.rs) | SEC 15c3-5 / MiFID II firewall (`init_risk`, `submit_order`, `cancel_replace_order`, `on_fill`, `on_cancel`, `trip_kill_switch`, `inv_risk_gate`) *(imports `stratum::{checked_notional, price_collar_ok}`)* — kill-switch blocks new/replace, zero credit leak, zero overflow bypass | `cancel_replace_buggy_bypasses_kill_switch`, `on_cancel_buggy_double_release`, `submit_order_buggy_notional_overflow` |
| **`S3.4`** | [`s3_4_l2_book_sweep_v128.rs`](s3_4_l2_book_sweep_v128.rs), [`_buggy.rs`](s3_4_l2_book_sweep_v128_buggy.rs) | `v128` L2 order book (`sweep_ask_4_v128 ≡ _ref`, `sweep_ask_4_notional_v128 ≡ _ref`, `book_sweep_ask_8_v128 ≡ _ref`, `init_l2_book`, `book_set_bid`, `book_set_ask`, `inv_l2_book`) — never crossed (`best_bid < best_ask`), exact `i32x4`/`i64x2` sweep | `sweep_ask_4_v128_buggy_strict_lt`, `book_set_bid_buggy_allows_cross` |
| **`S3.5`** | [`s3_5_signal_vwap_var_v128.rs`](s3_5_signal_vwap_var_v128.rs), [`_buggy.rs`](s3_5_signal_vwap_var_v128_buggy.rs) | `f32x4` IEEE-754 SIMD VWAP/VaR (`vwap_4_v128 ≡ _ref`, `portfolio_notional_4_v128 ≡ _ref`, `quote_ticks_from_fair`, `signal_dir_safe`) — `QF_ABVFP` proved `!is_nan`, `-0.0` safe, `bid_tick < ask_tick` | `vwap_4_buggy_nan_empty`, `signal_dir_buggy_neg_zero`, `quote_ticks_buggy_trunc_cross` |

### Layer 4 — E2E Verified OMS Pipelines (`S4.1`, `S4.2`) & Perf-Opt Pairs (`S4.3`)

| Stratum | File(s) | Pipeline & Verified Global Theorems | Buggy Mutants (`FALSIFIED`) |
| --- | --- | --- | --- |
| **`S4.1`** | [`s4_1_oms_on_exec_report.rs`](s4_1_oms_on_exec_report.rs), [`_buggy.rs`](s4_1_oms_on_exec_report_buggy.rs) | Inbound ExecReport pipeline (`S2.3` → `S2.2` + `stratum::order_id_mix` → `S3.1`/`S3.2` → `S3.3` → `S2.1` journal): `inv_oms_e2e` across `init_oms_state`/`oms_route_order`/`oms_request_cancel`/`oms_on_exec_report_opt`, `opt ≡ ref --ignore-dead-stack`, RX `SliceFrame`, fills during `PendingCancel` never dropped, no double cancel credit (**8/8 `PROVED`**, **3/3 `FALSIFIED`**) | `oms_on_exec_report_buggy_drops_pending_cancel_fill`, `oms_on_exec_report_buggy_double_cancel_credit` |
| **`S4.2`** | [`s4_2_oms_on_tick_or_order.rs`](s4_2_oms_on_tick_or_order.rs), [`_buggy.rs`](s4_2_oms_on_tick_or_order_buggy.rs) | Tick-to-Trade + OUCH pipeline (`S2.3` → `S3.4`/`S3.5` `v128`/`f32x4` → `S3.2`/`S3.3` + `stratum::{checked_notional, price_collar_ok}` → `S2.4` → `S2.1` TX): `inv_t2t_oms`, kill-switch `readonly` `SliceFrame`, RX `SliceFrame`, `sweep_fair_v128 ≡ _scalar`, `oms_on_tick_opt ≡ _ref --ignore-dead-stack` (**9/9 `PROVED`**, **4/4 `FALSIFIED`**) | `oms_on_tick_buggy_bypasses_kill_switch`, `oms_on_tick_buggy_clobbers_rx`, `oms_on_tick_buggy_crossed_quote` |
| **`S4.3`** | [`s4_3_perf_opt_pairs.rs`](s4_3_perf_opt_pairs.rs) | 6 portable `#![no_std]` OMS hot-path `ref` vs `opt` pairs (**8/8 `PROVED`** via `gnomon check-goal -t rust`, profiled live on x64 `skylake` & ARM64 `neoverse-v2` + host `--bench`) | — *(paired equivalence proofs + hardware profiling)* |

---

## Exact CLI Verification Commands

Run from the repository root:

```bash
GNOMON=./target/release/gnomon
DIR=examples/oms_strata
STATE=$DIR/out/oms_strata_state.json

# 1. Layer 1 — Contracts & SWAR Equivalence (direct strict no_std Rust via -t rust)
$GNOMON check-contract -t rust --entry checked_notional --requires req_notional --ensures ens_notional "$DIR/s1_1_notional_collar.rs"
$GNOMON check-contract -t rust --entry price_collar_ok --requires req_price_collar --ensures ens_price_collar "$DIR/s1_1_notional_collar.rs"
$GNOMON check-contract -t rust --entry bucket_index_barrett_u32 --requires req_barrett --ensures ens_barrett "$DIR/s1_2_barrett_tick_fee.rs"
$GNOMON check-goal -t rust --candidate "$DIR/s1_4_swar_fix_price.rs" --candidate-entry is_8_ascii_digits_swar --spec "$DIR/s1_4_swar_fix_price.rs" --spec-entry is_8_ascii_digits_ref

# 2. Layer 2 — Ring, Stratum-Linked Slab, & Zero-Copy Wire SliceFrame / Shadow-Stack Refinement
$GNOMON check-contract -t rust --init init_ring --ops ring_push,ring_pop --invariant inv_spsc_ring "$DIR/s2_1_spsc_ring.rs"
$GNOMON --state "$STATE" check-contract -t rust --init init_slab --ops slab_insert,slab_free --invariant inv_slab "$DIR/s2_2_order_slab_table.rs"
$GNOMON check-goal -t rust --candidate "$DIR/s2_3_wire_rx_decode.rs" --candidate-entry itch_decode_opt --spec "$DIR/s2_3_wire_rx_decode.rs" --spec-entry itch_decode_ref --pre "$DIR/s2_3_wire_rx_decode.rs" --pre-entry req_itch_decode --ignore-dead-stack
$GNOMON check-contract -t rust --entry itch_decode_opt --requires req_itch_decode --slice-frame base=param:2,len=32 "$DIR/s2_3_wire_rx_decode.rs"
$GNOMON check-goal -t rust --candidate "$DIR/s2_4_wire_tx_encode.rs" --candidate-entry ouch_encode_opt --spec "$DIR/s2_4_wire_tx_encode.rs" --spec-entry ouch_encode_ref --pre "$DIR/s2_4_wire_tx_encode.rs" --pre-entry req_ouch_encode --ignore-dead-stack

# 3. Layer 3 — Inductive FSMs, SEC 15c3-5 Risk Gate, v128 Book, & f32x4 Signal/VWAP
$GNOMON check-contract -t rust --init init_empty --ops submit_new,on_ack,request_cancel,request_replace,on_fill,on_cancel_ack,on_replace_ack,on_reject --invariant inv_child_fsm "$DIR/s3_1_child_fsm.rs"
$GNOMON check-contract -t rust --init init_parent --ops route_child,on_child_ack,request_child_cancel,request_child_replace,on_child_fill,on_child_cancel_ack,on_child_replace_ack,on_child_reject --invariant inv_parent_child_oms "$DIR/s3_2_parent_child_oms.rs"
$GNOMON --state "$STATE" check-contract -t rust --init init_risk --ops submit_order,cancel_replace_order,on_fill,on_cancel,trip_kill_switch --invariant inv_risk_gate "$DIR/s3_3_pretrade_risk_gate.rs"
$GNOMON check-goal -t rust --candidate "$DIR/s3_4_l2_book_sweep_v128.rs" --candidate-entry sweep_ask_4_v128 --spec "$DIR/s3_4_l2_book_sweep_v128.rs" --spec-entry sweep_ask_4_ref
$GNOMON check-contract -t rust --init init_l2_book --ops book_set_bid,book_set_ask --invariant inv_l2_book "$DIR/s3_4_l2_book_sweep_v128.rs"
$GNOMON check-goal -t rust --candidate "$DIR/s3_5_signal_vwap_var_v128.rs" --candidate-entry vwap_4_v128 --spec "$DIR/s3_5_signal_vwap_var_v128.rs" --spec-entry vwap_4_ref
$GNOMON check-contract -t rust --entry quote_ticks_from_fair --requires req_fair_valid --ensures ens_quotes_non_crossed "$DIR/s3_5_signal_vwap_var_v128.rs"
$GNOMON check-contract -t rust --entry signal_dir_safe --ensures ens_signal_dir "$DIR/s3_5_signal_vwap_var_v128.rs"

# 4. Layer 4 — E2E Verified OMS Pipelines (S4.1 Inbound ExecReport + S4.2 Tick-to-Trade + OUCH)
$GNOMON --state "$STATE" check-contract --entry oms_on_exec_report_opt --requires req_rx_slice --invariant inv_oms_e2e --timeout-ms 25000 "$DIR/out/s4_1_oms_on_exec_report.wasm"
$GNOMON --state "$STATE" check-goal --candidate "$DIR/out/s4_1_oms_on_exec_report.wasm" --candidate-entry oms_on_exec_report_opt --spec "$DIR/out/s4_1_oms_on_exec_report.wasm" --spec-entry oms_on_exec_report_ref --pre "$DIR/out/s4_1_oms_on_exec_report.wasm" --pre-entry req_rx_slice --ignore-dead-stack
$GNOMON --state "$STATE" check-contract --entry oms_on_exec_report_opt --requires req_rx_slice --slice-frame base=1048576,len=4096 "$DIR/out/s4_1_oms_on_exec_report.wasm"

$GNOMON --state "$STATE" check-contract --entry oms_on_tick_opt --requires req_t2t_slices --invariant inv_t2t_oms --timeout-ms 25000 "$DIR/out/s4_2_oms_on_tick_or_order.wasm"
$GNOMON --state "$STATE" check-contract --entry oms_on_tick_opt --requires req_t2t_kill_switch_tripped --ensures ens_t2t_blocked --slice-frame readonly --timeout-ms 15000 "$DIR/out/s4_2_oms_on_tick_or_order.wasm"
$GNOMON --state "$STATE" check-goal --candidate "$DIR/out/s4_2_oms_on_tick_or_order.wasm" --candidate-entry sweep_fair_v128 --spec "$DIR/out/s4_2_oms_on_tick_or_order.wasm" --spec-entry sweep_fair_scalar --timeout-ms 15000
$GNOMON --state "$STATE" check-goal --candidate "$DIR/out/s4_2_oms_on_tick_or_order.wasm" --candidate-entry oms_on_tick_opt --spec "$DIR/out/s4_2_oms_on_tick_or_order.wasm" --spec-entry oms_on_tick_ref --pre "$DIR/out/s4_2_oms_on_tick_or_order.wasm" --pre-entry req_t2t_slices --ignore-dead-stack --timeout-ms 25000
```

---

## `S4.3` — 6 Verified Performance Optimization Pairs (`gnomon check-goal` + `gnomon profile`)

Every pair in [`s4_3_perf_opt_pairs.rs`](s4_3_perf_opt_pairs.rs) is formally proved bit-exact (`8/8 PROVED` via `gnomon check-goal -t rust`) and profiled live across **x86-64 (`skylake`)** and **ARM64 (`neoverse-v2`)** via `gnomon profile --targets x64,arm64 --bench`:

```bash
P=examples/oms_strata/s4_3_perf_opt_pairs.rs
G=./target/release/gnomon

# Pair 1: Barrett Fastmod (eliminates hardware div/udiv)
$G check-goal -t rust --candidate "$P" --candidate-entry oms_bucket_opt --spec "$P" --spec-entry oms_bucket_ref --pre "$P" --pre-entry req_oms_bucket
$G profile "$P" --entry oms_bucket_ref --opt-entry oms_bucket_opt --targets x64,arm64 --bench

# Pair 2: SWAR 8-Byte FIX Digit Validator (7 branches -> 0 branches; --bench-preset ascii-digits)
$G check-goal -t rust --candidate "$P" --candidate-entry oms_fix_digits_opt --spec "$P" --spec-entry oms_fix_digits_ref
$G profile "$P" --entry oms_fix_digits_ref --opt-entry oms_fix_digits_opt --targets x64,arm64 --bench --bench-preset ascii-digits

# Pair 3: Register-Pressure / Unroll Study (x64 19 spills -> 0 spills; ARM64 31 GPRs 0 spills)
$G check-goal -t rust --candidate "$P" --candidate-entry oms_hash_mix_4x --spec "$P" --spec-entry oms_hash_mix_12x_spill
$G profile "$P" --entry oms_hash_mix_12x_spill --opt-entry oms_hash_mix_4x --targets x64,arm64 --bench

# Pair 4: Branchless Child Order FSM + Pre-Trade Risk (x64 23->0 br, ARM64 45->0 br; --bench-preset oms-valid)
$G check-goal -t rust --candidate "$P" --candidate-entry oms_risk_fsm_opt --spec "$P" --spec-entry oms_risk_fsm_ref
$G profile "$P" --entry oms_risk_fsm_ref --opt-entry oms_risk_fsm_opt --targets x64,arm64 --bench --bench-preset oms-valid

# Pair 5: Zero-Copy OUCH 48B Frame Builder (56B/64B stack -> 0B, --ignore-dead-stack)
$G check-goal -t rust --candidate "$P" --candidate-entry oms_ouch_pack_opt --spec "$P" --spec-entry oms_ouch_pack_ref --pre "$P" --pre-entry req_oms_ouch_pack --ignore-dead-stack
$G profile "$P" --entry oms_ouch_pack_ref --opt-entry oms_ouch_pack_opt --targets x64,arm64 --bench --bench-preset oms-valid

# Pair 6: 4-Lane Portfolio VWAP SIMD (QF_ABVFP proved, SSE mulps/addps + ARM64 NEON 0->14)
$G check-goal -t rust --candidate "$P" --candidate-entry oms_vwap_vec_opt --spec "$P" --spec-entry oms_vwap_scalar_ref --pre "$P" --pre-entry req_oms_vwap
$G profile "$P" --entry oms_vwap_scalar_ref --opt-entry oms_vwap_vec_opt --targets x64,arm64 --bench --bench-preset oms-valid
```

### Measured `gnomon profile` Results (`skylake` + `neoverse-v2` + 1M-iter x64 Host `--bench` w/ Realistic Presets)

| Pair (`ref -> opt`) | x64 (`skylake`) Inst / Br / Div / Stack / Spills | x64 Cyc & RTh Speedup | ARM64 (`neoverse-v2`) Inst / Br / Div / SIMD / Spills | ARM64 Cyc & RTh Speedup | Host x64 `ns/op` |
| --- | --- | --- | --- | --- | --- |
| **1. Barrett Fastmod** (`oms_bucket_ref -> _opt`) | `9->15` / br `1->1` / **div `1->0`** / `0B` / `0->0` | **1.48×** (`1616->1095`) / **2.50×** (`8.0->3.2`) | `6->12` / br `1->1` / **udiv `1->0`** / `0` / `0->0` | **6.24×** (`1304->209`) / **6.50×** (`13.0->2.0`) | `18.72` -> **`15.42`** (**1.21×**) |
| **2. SWAR FIX Digits** (`oms_fix_digits_ref -> _opt`) | `40->13` / **br `7->0`** / `0` / `0B` / `0->0` | **3.02×** (`1011->335`) / **3.00×** (`7.5->2.5`) | `47->10` / **br `7->0`** / `0` / `0` / `0->0` | **1.31×** (`790->604`) / **4.59×** (`7.8->1.7`) | `5.58` -> **`2.41`** (**2.31×**, `preset:ascii-digits`) |
| **3. Hash Unroll** (`12x_spill -> 4x`) | `342->300` / `0` / `0` / **`56B->0B`** / **spills `19->0` (rel `16->0`)** | **1.14×** (`8712->7667`) / **1.15×** (`61.3->53.3`) | `261->259` / `0` / `0` / `0` / **spills `0->0` (31 GPRs)** | **1.02×** (`4411->4344`) / **1.02×** (`44.0->43.2`) | `39.02` -> `41.25` (`2x`: `36.80`) |
| **4. Branchless Risk FSM** (`oms_risk_fsm_ref -> _opt`) | `128->91` / **br `23->0`** / `0` / `0B->4B` / `0->1` | **1.66×** (`3760->2264`) / **1.52×** (`28.5->18.7`) | `136->73` / **br `45->0`** / `0` / `0` / `0->0` | **2.21×** (`3104->1406`) / **2.54×** (`31.0->12.2`) | `20.05` -> **`10.38`** (**1.93×**, `preset:oms-valid`) |
| **5. Zero-Copy OUCH 48B** (`oms_ouch_pack_ref -> _opt`) | `36->28` / `4->4` / `0` / **`56B->0B`** / **`1->0`** | **2.20×** (`2207->1005`) / `0.83×` (`8.3->10.0`) | `28->32` / `4->4` / `0` / `0` (stack **`64B->0B`**) / `0->0` | **1.53×** (`1078->705`) / `0.76×` (`5.3->7.0`) | `12.68` -> **`5.91`** (**2.15×**, `--bench-inputs`) |
| **6. 4-Lane VWAP SIMD** (`oms_vwap_scalar_ref -> _vec_opt`) | `37->16` / **br `7->1`** / `0` / `0B` / `0->0` | **1.23×** (`952->775`) / **1.20×** (`7.2->6.0`) | `32->22` / **br `6->1`** / `0` / **NEON `0->14`** / `0->0` | **1.45×** (`660->456`) / **1.70×** (`6.3->3.7`) | `9.99` -> **`3.24`** (**3.09×**) |
