# Gnomon Horizontal Generalization — 4 Real-World Non-Trading Vertical Packs

Strict `#![no_std]` Rust fixtures (`0` warnings under `rustc -D warnings`) demonstrating that the **100% unmodified Gnomon engine** (`gnomon lift`, `check-goal`, `check-contract`, `profile --compare --targets x64,arm64`) generalizes directly beyond financial OMS/trading to 4 distinct systems domains:

1. **AI Inference (`ai_q8_0_quant.rs` / `_buggy.rs`):** `llama.cpp` / GGML `Q8_0` 4-lane `f32x4` block quantization (`QF_ABVFP` equivalence, NaN/Inf/subnormal safety, zero-block determinism, portable native SIMD profiling).
2. **Columnar DB / Apache Parquet (`db_parquet_varint_slice.rs` / `_buggy.rs`):** Branchless 4-byte LEB128 varint slice decoder (shadow-stack `&[u8]` ref vs zero-stack wide-load opt under `--ignore-dead-stack`, `SliceFrame readonly`, zero panics on truncated slices) + Delta-ZigZag bijection round-trip.
3. **Networking / Security Dataplane (`net_wireguard_replay.rs` / `_buggy.rs`):** WireGuard / IPsec RFC 6479 64-bit sliding anti-replay window (`globals: 0` via `AtomicI64`/`AtomicU8`, inductive window invariant, duplicate-rejection & large-jump contracts, zero shift-64 UB, branchy vs branchless profiling).
4. **Distributed Cloud Quota / Reservation Saga (`cloud_quota_saga.rs` / `_buggy.rs`):** Multi-tenant 4-slot two-phase reservation saga generalizing OMS `S3.2`/`S3.3` (`globals: 0`, zero over-commit `committed + reserved <= limit`, exact conservation `reserved == sum(active r_qty)`, no double-release on duplicate cancel, no double-commit).

---

## 1. Build All 8 Wasm Modules (`rustc -D warnings`)

Run from the repository root (`/home/sunyc/src/gnomon-rs`):

```bash
VP=examples/vertical_packs
OUT=$VP/out
mkdir -p "$OUT"

# Pack 1 (requires Wasm SIMD128 for f32x4 / i32x4)
rustc --target wasm32-unknown-unknown --crate-type=cdylib -O -C panic=abort -C target-feature=+simd128 -D warnings "$VP/ai_q8_0_quant.rs" -o "$OUT/ai_q8_0_quant.wasm"
rustc --target wasm32-unknown-unknown --crate-type=cdylib -O -C panic=abort -C target-feature=+simd128 -D warnings "$VP/ai_q8_0_quant_buggy.rs" -o "$OUT/ai_q8_0_quant_buggy.wasm"

# Packs 2–4 (core Wasm32)
for f in db_parquet_varint_slice db_parquet_varint_slice_buggy net_wireguard_replay net_wireguard_replay_buggy cloud_quota_saga cloud_quota_saga_buggy; do
  rustc --target wasm32-unknown-unknown --crate-type=cdylib -O -C panic=abort -D warnings "$VP/${f}.rs" -o "$OUT/${f}.wasm"
done
```

### Lift & Round-Trip Validation (`target/release/gnomon lift`)

| Artifact | Size | `globals` | `host_contracts` | `roundtrip_wasm_valid` |
| --- | ---: | ---: | ---: | :---: |
| `out/ai_q8_0_quant.wasm` | 3,419 B | `0` | `2` | `true` |
| `out/ai_q8_0_quant_buggy.wasm` | 1,538 B | `0` | `0` | `true` |
| `out/db_parquet_varint_slice.wasm` | 2,060 B | `1` *(ref shadow stack)* | `1` | `true` |
| `out/db_parquet_varint_slice_buggy.wasm` | 1,017 B | `0` | `0` | `true` |
| `out/net_wireguard_replay.wasm` | 2,257 B | `0` | `2` | `true` |
| `out/net_wireguard_replay_buggy.wasm` | 1,451 B | `0` | `2` | `true` |
| `out/cloud_quota_saga.wasm` | 3,324 B | `0` | `2` | `true` |
| `out/cloud_quota_saga_buggy.wasm` | 3,070 B | `0` | `2` | `true` |

---

## 2. Exact Live Verification Commands & Measured Results

All **24** checks (**16/16 `PROVED`**, **8/8 buggy mutants `FALSIFIED`**) were executed live on `./target/release/gnomon`:

```bash
GN=./target/release/gnomon
OUT=examples/vertical_packs/out

# Pack 1: AI Inference — llama.cpp / GGML Q8_0 4-Lane Block Quantization (QF_ABVFP)
$GN check-goal --candidate "$OUT/ai_q8_0_quant.wasm" --candidate-entry q8_0_quant_4_v128 --spec "$OUT/ai_q8_0_quant.wasm" --spec-entry q8_0_quant_4_ref --timeout-ms 15000
$GN check-contract "$OUT/ai_q8_0_quant.wasm" --entry q8_0_quant_4_v128 --requires req_finite_block --ensures ens_q8_0_safe --timeout-ms 15000
$GN check-contract "$OUT/ai_q8_0_quant.wasm" --entry contract_q8_0_quant_4 --timeout-ms 15000
$GN check-contract "$OUT/ai_q8_0_quant_buggy.wasm" --entry q8_0_buggy_zero_nan --requires req_finite_block --ensures ens_q8_0_safe --timeout-ms 15000
$GN check-goal --candidate "$OUT/ai_q8_0_quant_buggy.wasm" --candidate-entry q8_0_buggy_trunc_bias --spec "$OUT/ai_q8_0_quant.wasm" --spec-entry q8_0_quant_4_ref --timeout-ms 15000

# Pack 2: Columnar DB / Parquet — 4-Byte LEB128 Varint Slice + Delta-ZigZag
$GN check-goal --candidate "$OUT/db_parquet_varint_slice.wasm" --candidate-entry varint_decode_opt --spec "$OUT/db_parquet_varint_slice.wasm" --spec-entry varint_decode_ref --pre "$OUT/db_parquet_varint_slice.wasm" --pre-entry req_varint_slice --ignore-dead-stack
$GN check-contract "$OUT/db_parquet_varint_slice.wasm" --entry varint_decode_opt --requires req_varint_slice --slice-frame readonly
$GN check-contract "$OUT/db_parquet_varint_slice.wasm" --entry varint_decode_ref --requires req_varint_slice --slice-frame readonly --ignore-dead-stack
$GN check-goal --candidate "$OUT/db_parquet_varint_slice.wasm" --candidate-entry zigzag_enc_dec_roundtrip --spec "$OUT/db_parquet_varint_slice.wasm" --spec-entry identity_i64
$GN check-contract "$OUT/db_parquet_varint_slice.wasm" --entry contract_zigzag_roundtrip
$GN check-goal --candidate "$OUT/db_parquet_varint_slice.wasm" --candidate-entry varint_decode_branchless_opt --spec "$OUT/db_parquet_varint_slice.wasm" --spec-entry varint_decode_branchy_ref
$GN check-contract "$OUT/db_parquet_varint_slice_buggy.wasm" --entry varint_decode_buggy_short_read --requires req_varint_slice
$GN check-goal --candidate "$OUT/db_parquet_varint_slice_buggy.wasm" --candidate-entry varint_decode_buggy_shift_overflow --spec "$OUT/db_parquet_varint_slice.wasm" --spec-entry varint_decode_ref --pre "$OUT/db_parquet_varint_slice.wasm" --pre-entry req_varint_slice --ignore-dead-stack

# Pack 3: Networking / Security Dataplane — WireGuard / IPsec 64-Bit Anti-Replay Window
$GN check-contract "$OUT/net_wireguard_replay.wasm" --init init_replay --ops accept_nonce --invariant inv_replay_window
$GN check-contract "$OUT/net_wireguard_replay.wasm" --entry contract_duplicate_always_rejected
$GN check-contract "$OUT/net_wireguard_replay.wasm" --entry contract_large_jump_clears_stale
$GN check-goal --candidate "$OUT/net_wireguard_replay.wasm" --candidate-entry replay_check_branchless --spec "$OUT/net_wireguard_replay.wasm" --spec-entry replay_check_branchy
$GN check-contract "$OUT/net_wireguard_replay_buggy.wasm" --entry contract_large_jump_clears_stale
$GN check-goal --candidate "$OUT/net_wireguard_replay_buggy.wasm" --candidate-entry accept_nonce_buggy_shift64_wrap --spec "$OUT/net_wireguard_replay.wasm" --spec-entry accept_nonce

# Pack 4: Distributed Cloud Quota / Reservation Saga (4-Slot Two-Phase Saga)
$GN check-contract "$OUT/cloud_quota_saga.wasm" --init init_quota --ops reserve,commit,cancel_reserve --invariant inv_quota_saga --timeout-ms 15000
$GN check-contract "$OUT/cloud_quota_saga.wasm" --entry contract_no_double_release --timeout-ms 15000
$GN check-contract "$OUT/cloud_quota_saga.wasm" --entry contract_no_double_commit --timeout-ms 15000
$GN check-contract "$OUT/cloud_quota_saga_buggy.wasm" --init init_quota --ops reserve,commit,cancel_reserve_buggy_double_release --invariant inv_quota_saga --timeout-ms 15000
$GN check-contract "$OUT/cloud_quota_saga_buggy.wasm" --entry contract_no_double_release --timeout-ms 15000
```

### Verification Results Table

| Pack | Check | Property / Mutant | Verdict | Elapsed |
| --- | --- | --- | :---: | ---: |
| **1. AI (`Q8_0`)** | `P1.1` | `q8_0_quant_4_v128 ≡ q8_0_quant_4_ref` (`QF_ABVFP`) | **PROVED** | 112.1 ms |
| **1. AI (`Q8_0`)** | `P1.2` | `req_finite_block => ens_q8_0_safe` (finite scale, no `NaN`, `q in [-127,127]`, zero-block `(0.0,0)`) | **PROVED** | 98.9 ms |
| **1. AI (`Q8_0`)** | `P1.3` | `contract_q8_0_quant_4` (inline equivalence + safety) | **PROVED** | 122.1 ms |
| **1. AI (`Q8_0`)** | `P1.BUG1` | `q8_0_buggy_zero_nan` (missing `amax == 0.0` guard -> `0.0 * Inf = NaN`) | **FALSIFIED** | 172.6 ms |
| **1. AI (`Q8_0`)** | `P1.BUG2` | `q8_0_buggy_trunc_bias` (`trunc` instead of `f32x4.nearest`) | **FALSIFIED** | 4,601.0 ms |
| **2. DB (Parquet)** | `P2.1` | `varint_decode_opt ≡ varint_decode_ref` (`--ignore-dead-stack`) | **PROVED** | 373.9 ms |
| **2. DB (Parquet)** | `P2.2` | `varint_decode_opt` trap-free (incl. `len < 4`) + `SliceFrame readonly` | **PROVED** | 8.3 ms |
| **2. DB (Parquet)** | `P2.3` | `varint_decode_ref` trap-free + `SliceFrame readonly --ignore-dead-stack` | **PROVED** | 184.8 ms |
| **2. DB (Parquet)** | `P2.4` | `zigzag_enc_dec_roundtrip ≡ identity_i64` (all `2^64` `i64`) | **PROVED** | 29.6 ms |
| **2. DB (Parquet)** | `P2.5` | `contract_zigzag_roundtrip` (inline bijection) | **PROVED** | 4.4 ms |
| **2. DB (Parquet)** | `P2.6` | `varint_decode_branchless_opt ≡ varint_decode_branchy_ref` | **PROVED** | 88.1 ms |
| **2. DB (Parquet)** | `P2.BUG1` | `varint_decode_buggy_short_read` (OOB trap on `len < 4`) | **FALSIFIED** | 8.7 ms |
| **2. DB (Parquet)** | `P2.BUG2` | `varint_decode_buggy_shift_overflow` (continuation bleed + bad shift) | **FALSIFIED** | 179.4 ms |
| **3. Net (WireGuard)** | `P3.1` | Inductive suite: `init_replay` + `accept_nonce` preserves `inv_replay_window` | **PROVED** | 13.3 ms |
| **3. Net (WireGuard)** | `P3.2` | `contract_duplicate_always_rejected` (2nd call NEVER accepts duplicate) | **PROVED** | 107.4 ms |
| **3. Net (WireGuard)** | `P3.3` | `contract_large_jump_clears_stale` (`delta >= 64` resets `bitmap = 1`, rejects stale) | **PROVED** | 196.6 ms |
| **3. Net (WireGuard)** | `P3.4` | `replay_check_branchless ≡ replay_check_branchy` (all `2^192` inputs) | **PROVED** | 55.9 ms |
| **3. Net (WireGuard)** | `P3.BUG1` | `accept_nonce_buggy_shift64_wrap` (`contract_large_jump_clears_stale`) | **FALSIFIED** | 19.4 ms |
| **3. Net (WireGuard)** | `P3.BUG2` | `accept_nonce_buggy_shift64_wrap` vs `accept_nonce` (`check-goal`) | **FALSIFIED** | 174.2 ms |
| **4. Cloud Quota** | `P4.1` | Inductive suite: `init_quota` + `reserve,commit,cancel_reserve` preserves `inv_quota_saga` | **PROVED** | 11,015.5 ms |
| **4. Cloud Quota** | `P4.2` | `contract_no_double_release` (duplicate `cancel_reserve` idempotent, 0 quota leak) | **PROVED** | 7,510.5 ms |
| **4. Cloud Quota** | `P4.3` | `contract_no_double_commit` (duplicate `commit` idempotent) | **PROVED** | 1,385.1 ms |
| **4. Cloud Quota** | `P4.BUG1` | `cancel_reserve_buggy_double_release` (inductive suite: 3/4 `PROVED`, buggy cancel `FALSIFIED`) | **FALSIFIED** | 9,107.4 ms |
| **4. Cloud Quota** | `P4.BUG2` | `cancel_reserve_buggy_double_release` (`contract_no_double_release`) | **FALSIFIED** | 31.5 ms |

---

## 3. Native Cross-Architecture Hardware Profiling (`gnomon profile --compare --targets x64,arm64`)

```bash
GN=./target/release/gnomon
VP=examples/vertical_packs

$GN profile "$VP/ai_q8_0_quant.rs" --compare "$VP/ai_q8_0_quant.rs" --entry q8_0_scale_scalar --opt-entry q8_0_scale_vec --targets x64,arm64
$GN profile "$VP/db_parquet_varint_slice.rs" --compare "$VP/db_parquet_varint_slice.rs" --entry varint_decode_branchy_ref --opt-entry varint_decode_branchless_opt --targets x64,arm64
$GN profile "$VP/net_wireguard_replay.rs" --compare "$VP/net_wireguard_replay.rs" --entry replay_check_branchy --opt-entry replay_check_branchless --targets x64,arm64
```

### Measured `x64` (`skylake`) & `arm64` (`neoverse-v2`) Results

| Pack & Pair (`ref -> opt`) | x64 (`skylake`) Inst / Br / SIMD / Stack / Spills | x64 Cyc & RTh Speedup | ARM64 (`neoverse-v2`) Inst / Br / SIMD / Stack / Spills | ARM64 Cyc & RTh Speedup |
| --- | --- | --- | --- | --- |
| **1. AI `Q8_0`** (`q8_0_scale_scalar -> q8_0_scale_vec`) | `101 -> 81` (`-20`) / br `2 -> 2` / simd `64 -> 63` / `0B` / `0 -> 0` | **2.61×** (`79.06 -> 30.33`) / **1.01×** (`20.2 -> 20.0`) | `89 -> 52` (`-37`) / **br `2 -> 0` (`-2`)** / **NEON `13 -> 33` (`+20`)** / `0B` / `0 -> 0` | **1.57×** (`19.73 -> 12.59`) / **1.71×** (`16.2 -> 9.5`) |
| **2. DB Varint** (`varint_decode_branchy_ref -> _branchless_opt`) | `38 -> 42` (`+4`) / **br `4 -> 0` (`-4`)** / `0` / `0B` / `0 -> 0` | **1.02×** (`10.59 -> 10.36`) / **1.10×** (`8.0 -> 7.3`) | `23 -> 26` (`+3`) / **br `3 -> 0` (`-3`)** / `0` / `0B` / `0 -> 0` | **1.50×** (`15.03 -> 10.04`) / `0.88×` (`3.8 -> 4.3`) |
| **3. Net Replay** (`replay_check_branchy -> _branchless`) | `10 -> 11` (`+1`) / **br `2 -> 0` (`-2`)** / `0` / `0B` / `0 -> 0` | `0.99×` (`2.60 -> 2.62`) / `0.91×` (`2.0 -> 2.2`) | `9 -> 9` (`0`) / br `0 -> 0` *(LLVM `csel` if-conv)* / `0` / `0B` / `0 -> 0` | `1.00×` (`5.03 -> 5.03`) / `1.00×` (`1.5 -> 1.5`) |
