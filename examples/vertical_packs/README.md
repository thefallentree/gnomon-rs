# Gnomon Horizontal Generalization — 7 Real-World Non-Trading Vertical Packs

Strict `#![no_std]` Rust fixtures (`0` warnings under `rustc -D warnings` on both `wasm32-unknown-unknown` and native `x86_64`) demonstrating that Gnomon (`gnomon lift`, `check-goal`, `check-contract`, `profile --compare --targets x64,arm64 --bench`) generalizes directly beyond financial OMS/trading across **7 distinct high-impact systems domains** (with zero domain-specific engine code):

1. **AI Inference (`ai_q8_0_quant.rs` / `_buggy.rs`):** `llama.cpp` / GGML `Q8_0` 4-lane `f32x4` block quantization (`QF_ABVFP` equivalence, NaN/Inf/subnormal safety, zero-block determinism, portable native SIMD profiling).
2. **Columnar DB / Apache Parquet (`db_parquet_varint_slice.rs` / `_buggy.rs`):** Branchless 4-byte LEB128 varint slice decoder (shadow-stack `&[u8]` ref vs zero-stack wide-load opt under `--ignore-dead-stack`, `SliceFrame readonly`, zero panics on truncated slices) + Delta-ZigZag bijection round-trip.
3. **Networking / Security Dataplane (`net_wireguard_replay.rs` / `_buggy.rs`):** WireGuard / IPsec RFC 6479 64-bit sliding anti-replay window (`globals: 0` via `AtomicI64`/`AtomicU8`, inductive window invariant, duplicate-rejection & large-jump contracts, zero shift-64 UB, branchy vs branchless profiling).
4. **Distributed Cloud Quota / Reservation Saga (`cloud_quota_saga.rs` / `_buggy.rs`):** Multi-tenant 4-slot two-phase reservation saga generalizing OMS `S3.2`/`S3.3` (`globals: 0`, zero over-commit `committed + reserved <= limit`, exact conservation `reserved == sum(active r_qty)`, no double-release on duplicate cancel, no double-commit).
5. **Cryptography / Constant-Time Security Dataplane (`crypto_ct_tls_record.rs` / `_buggy.rs`):** Constant-time RFC 5652 16-byte PKCS#7 unpadding (`--ignore-dead-stack`, `SliceFrame readonly`, complete postcondition, dual-arch zero-branch constant-time hardware audit eliminating Lucky 13 / CVE-2013-0169 timing branches on BOTH `x64` & `arm64`) + `v128` 16-byte AEAD MAC verification (1-bit forgery rejection) + RFC 8439 ChaCha20 4-lane `u32x4` SIMD column round (`SliceFrame param:0:64`).
6. **Safety-Critical Robotics / Aerospace Control (`robotics_flight_pid_mixer.rs` / `_buggy.rs`):** Stateful inductive IEEE-754 `QF_ABVFP` flight PID + anti-windup + slew-rate + latching E-stop controller (`globals: 0`, zero `NaN` integrator poisoning across arbitrary `NaN`/`±Inf`/subnormal sensors) + quadrotor X-frame 4-motor PWM mixer (formally proving the IEEE-754 `2^23` magic-bias vector float-to-int RNE conversion bit-identical to `f32x4.nearest` & scalar ref across all `2^160` inputs, eliminating `NaN`-to-full-throttle crashes).
7. **OS Kernel / Hypervisor Memory Protection (`os_mmu_wx_tlb.rs` / `_buggy.rs`):** 4-region `W^X` MMU/MPU page-protection manager (`globals: 0`, inductive `W^X` + 4 KiB page alignment + zero `u32` wraparound + pairwise disjointness, global virtual-address `W^X` non-interference, immediate unmap access revocation) + `v128` `u32x4` 4-way parallel TLB permission check (`SliceFrame readonly`, AVX2/NEON vectorization).

---

## 1. One-Command Build, Round-Trip Lift, Verification & Profiling (`verify_all.sh`)

Run all **14** modules (`-D warnings`), round-trip lifts, **55/55** formal verification checks (**38/38 `PROVED`**, **17/17 `FALSIFIED`**), and **6** native `x64` + `arm64` hardware profiles in one command from the repository root:

```bash
./examples/vertical_packs/verify_all.sh
```

### Build All 14 Wasm Modules Manually (`rustc -D warnings`)

```bash
VP=examples/vertical_packs
OUT=$VP/out
mkdir -p "$OUT"

# Packs 1, 5, 6, 7 (require Wasm SIMD128 for f32x4 / i32x4 / v128)
for f in ai_q8_0_quant ai_q8_0_quant_buggy \
         crypto_ct_tls_record crypto_ct_tls_record_buggy \
         robotics_flight_pid_mixer robotics_flight_pid_mixer_buggy \
         os_mmu_wx_tlb os_mmu_wx_tlb_buggy; do
  rustc --target wasm32-unknown-unknown --crate-type=cdylib -O -C panic=abort -C target-feature=+simd128 -D warnings "$VP/${f}.rs" -o "$OUT/${f}.wasm"
done

# Packs 2–4 (core Wasm32)
for f in db_parquet_varint_slice db_parquet_varint_slice_buggy \
         net_wireguard_replay net_wireguard_replay_buggy \
         cloud_quota_saga cloud_quota_saga_buggy; do
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
| `out/crypto_ct_tls_record.wasm` | 4,023 B | `1` *(ref shadow stack)* | `2` | `true` |
| `out/crypto_ct_tls_record_buggy.wasm` | 2,256 B | `0` | `2` | `true` |
| `out/robotics_flight_pid_mixer.wasm` | 4,047 B | `0` | `2` | `true` |
| `out/robotics_flight_pid_mixer_buggy.wasm` | 2,405 B | `0` | `2` | `true` |
| `out/os_mmu_wx_tlb.wasm` | 4,288 B | `0` | `2` | `true` |
| `out/os_mmu_wx_tlb_buggy.wasm` | 3,322 B | `0` | `2` | `true` |

---

## 2. Exact Live Verification Commands & Measured Results

All **55** checks (**38/38 `PROVED`**, **17/17 buggy mutants `FALSIFIED`**) were executed live via `./examples/vertical_packs/verify_all.sh` against `./target/release/gnomon`:

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
$GN check-contract "$OUT/cloud_quota_saga.wasm" --init init_quota --ops reserve,commit,cancel_reserve --invariant inv_quota_saga --timeout-ms 20000
$GN check-contract "$OUT/cloud_quota_saga.wasm" --entry contract_no_double_release --timeout-ms 15000
$GN check-contract "$OUT/cloud_quota_saga.wasm" --entry contract_no_double_commit --timeout-ms 15000
$GN check-contract "$OUT/cloud_quota_saga_buggy.wasm" --init init_quota --ops reserve,commit,cancel_reserve_buggy_double_release --invariant inv_quota_saga --timeout-ms 20000
$GN check-contract "$OUT/cloud_quota_saga_buggy.wasm" --entry contract_no_double_release --timeout-ms 15000

# Pack 5: Cryptography / Constant-Time TLS & AEAD Security (PKCS#7 + 16B MAC + ChaCha20 v128)
$GN check-goal --candidate "$OUT/crypto_ct_tls_record.wasm" --candidate-entry pkcs7_unpad16_opt --spec "$OUT/crypto_ct_tls_record.wasm" --spec-entry pkcs7_unpad16_ref --pre "$OUT/crypto_ct_tls_record.wasm" --pre-entry req_block16_slice --ignore-dead-stack --timeout-ms 15000
$GN check-contract "$OUT/crypto_ct_tls_record.wasm" --entry pkcs7_unpad16_opt --requires req_block16_slice --ensures ens_pkcs7_unpad16 --slice-frame readonly --timeout-ms 15000
$GN check-contract "$OUT/crypto_ct_tls_record.wasm" --entry pkcs7_unpad16_ref --requires req_block16_slice --slice-frame readonly --ignore-dead-stack --timeout-ms 15000
$GN check-goal --candidate "$OUT/crypto_ct_tls_record.wasm" --candidate-entry pkcs7_unpad16_branchless --spec "$OUT/crypto_ct_tls_record.wasm" --spec-entry pkcs7_unpad16_branchy --timeout-ms 15000
$GN check-goal --candidate "$OUT/crypto_ct_tls_record.wasm" --candidate-entry ct_mac16_eq_v128 --spec "$OUT/crypto_ct_tls_record.wasm" --spec-entry ct_mac16_eq_ref --timeout-ms 15000
$GN check-contract "$OUT/crypto_ct_tls_record.wasm" --entry contract_mac16_1bit_flip_rejected --timeout-ms 15000
$GN check-goal --candidate "$OUT/crypto_ct_tls_record.wasm" --candidate-entry chacha20_col_round_v128 --spec "$OUT/crypto_ct_tls_record.wasm" --spec-entry chacha20_col_round_ref --pre "$OUT/crypto_ct_tls_record.wasm" --pre-entry req_chacha_state --timeout-ms 15000
$GN check-contract "$OUT/crypto_ct_tls_record.wasm" --entry chacha20_col_round_v128 --requires req_chacha_state --slice-frame param:0:64 --timeout-ms 15000
$GN check-contract "$OUT/crypto_ct_tls_record_buggy.wasm" --entry pkcs7_unpad16_buggy_zero_pad_oracle --requires req_block16_slice --ensures ens_pkcs7_unpad16 --timeout-ms 15000
$GN check-contract "$OUT/crypto_ct_tls_record_buggy.wasm" --entry contract_mac16_1bit_flip_rejected --timeout-ms 15000
$GN check-goal --candidate "$OUT/crypto_ct_tls_record_buggy.wasm" --candidate-entry chacha20_col_round_buggy_rot --spec "$OUT/crypto_ct_tls_record.wasm" --spec-entry chacha20_col_round_ref --pre "$OUT/crypto_ct_tls_record.wasm" --pre-entry req_chacha_state --timeout-ms 15000

# Pack 6: Safety-Critical Robotics / Aerospace Control (Stateful IEEE-754 PID + Quadrotor Mixer)
$GN check-contract "$OUT/robotics_flight_pid_mixer.wasm" --init init_pid --ops step_pid,clear_estop --invariant inv_pid_safe --timeout-ms 20000
$GN check-contract "$OUT/robotics_flight_pid_mixer.wasm" --entry contract_estop_forces_zero --timeout-ms 15000
$GN check-contract "$OUT/robotics_flight_pid_mixer.wasm" --entry contract_nan_sensor_never_poisons --timeout-ms 15000
$GN check-contract "$OUT/robotics_flight_pid_mixer.wasm" --entry contract_slew_rate_bounded --timeout-ms 20000
$GN check-goal --candidate "$OUT/robotics_flight_pid_mixer.wasm" --candidate-entry quad_mixer_4_opt --spec "$OUT/robotics_flight_pid_mixer.wasm" --spec-entry quad_mixer_4_v128 --timeout-ms 15000
$GN check-goal --candidate "$OUT/robotics_flight_pid_mixer.wasm" --candidate-entry quad_mixer_4_opt --spec "$OUT/robotics_flight_pid_mixer.wasm" --spec-entry quad_mixer_4_scalar --timeout-ms 15000
$GN check-contract "$OUT/robotics_flight_pid_mixer.wasm" --entry quad_mixer_4_opt --ensures ens_quad_mixer_safe --timeout-ms 15000
$GN check-contract "$OUT/robotics_flight_pid_mixer_buggy.wasm" --init init_pid --ops step_pid_buggy_nan_clamp,clear_estop --invariant inv_pid_safe --timeout-ms 15000
$GN check-contract "$OUT/robotics_flight_pid_mixer_buggy.wasm" --entry contract_nan_sensor_never_poisons --timeout-ms 15000
$GN check-contract "$OUT/robotics_flight_pid_mixer_buggy.wasm" --entry quad_mixer_buggy_nan_full_throttle --ensures ens_quad_mixer_safe --timeout-ms 15000

# Pack 7: OS Kernel / Hypervisor Memory Protection (4-Region W^X MMU + 4-Way Parallel TLB)
$GN check-contract "$OUT/os_mmu_wx_tlb.wasm" --init init_mmu --ops map_region,mprotect_region,unmap_region --invariant inv_mmu_wx --timeout-ms 20000
$GN check-contract "$OUT/os_mmu_wx_tlb.wasm" --entry contract_no_wx_escalation --timeout-ms 15000
$GN check-contract "$OUT/os_mmu_wx_tlb.wasm" --entry contract_unmap_revokes_access --timeout-ms 15000
$GN check-goal --candidate "$OUT/os_mmu_wx_tlb.wasm" --candidate-entry tlb_check_4_v128 --spec "$OUT/os_mmu_wx_tlb.wasm" --spec-entry tlb_check_4_ref --pre "$OUT/os_mmu_wx_tlb.wasm" --pre-entry req_tlb_tables --timeout-ms 15000
$GN check-goal --candidate "$OUT/os_mmu_wx_tlb.wasm" --candidate-entry tlb_check_4_branchless --spec "$OUT/os_mmu_wx_tlb.wasm" --spec-entry tlb_check_4_ref --pre "$OUT/os_mmu_wx_tlb.wasm" --pre-entry req_tlb_tables --timeout-ms 15000
$GN check-contract "$OUT/os_mmu_wx_tlb.wasm" --entry tlb_check_4_branchless --requires req_tlb_tables --slice-frame readonly --timeout-ms 15000
$GN check-contract "$OUT/os_mmu_wx_tlb.wasm" --entry tlb_check_4_v128 --requires req_tlb_tables --slice-frame readonly --timeout-ms 15000
$GN check-contract "$OUT/os_mmu_wx_tlb_buggy.wasm" --init init_mmu --ops map_region_buggy_wrap_overlap,unmap_region --invariant inv_mmu_wx --timeout-ms 15000
$GN check-contract "$OUT/os_mmu_wx_tlb_buggy.wasm" --entry contract_no_wx_escalation --timeout-ms 15000
$GN check-goal --candidate "$OUT/os_mmu_wx_tlb_buggy.wasm" --candidate-entry tlb_check_4_buggy_signed_cmp --spec "$OUT/os_mmu_wx_tlb.wasm" --spec-entry tlb_check_4_ref --pre "$OUT/os_mmu_wx_tlb.wasm" --pre-entry req_tlb_tables --timeout-ms 15000
```

### Verification Results Table (`55 / 55` Exact Verdicts)

| Pack | Check | Property / Mutant | Verdict | Elapsed |
| --- | --- | --- | :---: | ---: |
| **1. AI (`Q8_0`)** | `P1.1` | `q8_0_quant_4_v128 ≡ q8_0_quant_4_ref` (`QF_ABVFP`) | **PROVED** | 115.2 ms |
| **1. AI (`Q8_0`)** | `P1.2` | `req_finite_block => ens_q8_0_safe` (finite scale, no `NaN`, `q in [-127,127]`, zero-block `(0.0,0)`) | **PROVED** | 101.2 ms |
| **1. AI (`Q8_0`)** | `P1.3` | `contract_q8_0_quant_4` (inline equivalence + safety) | **PROVED** | 115.7 ms |
| **1. AI (`Q8_0`)** | `P1.BUG1` | `q8_0_buggy_zero_nan` (missing `amax == 0.0` guard -> `0.0 * Inf = NaN`) | **FALSIFIED** | 178.2 ms |
| **1. AI (`Q8_0`)** | `P1.BUG2` | `q8_0_buggy_trunc_bias` (`trunc` instead of `f32x4.nearest`) | **FALSIFIED** | 4,558.1 ms |
| **2. DB (Parquet)** | `P2.1` | `varint_decode_opt ≡ varint_decode_ref` (`--ignore-dead-stack`) | **PROVED** | 389.6 ms |
| **2. DB (Parquet)** | `P2.2` | `varint_decode_opt` trap-free (incl. `len < 4`) + `SliceFrame readonly` | **PROVED** | 10.0 ms |
| **2. DB (Parquet)** | `P2.3` | `varint_decode_ref` trap-free + `SliceFrame readonly --ignore-dead-stack` | **PROVED** | 186.6 ms |
| **2. DB (Parquet)** | `P2.4` | `zigzag_enc_dec_roundtrip ≡ identity_i64` (all `2^64` `i64`) | **PROVED** | 30.8 ms |
| **2. DB (Parquet)** | `P2.5` | `contract_zigzag_roundtrip` (inline bijection) | **PROVED** | 6.5 ms |
| **2. DB (Parquet)** | `P2.6` | `varint_decode_branchless_opt ≡ varint_decode_branchy_ref` | **PROVED** | 84.0 ms |
| **2. DB (Parquet)** | `P2.BUG1` | `varint_decode_buggy_short_read` (OOB trap on `len < 4`) | **FALSIFIED** | 6.0 ms |
| **2. DB (Parquet)** | `P2.BUG2` | `varint_decode_buggy_shift_overflow` (continuation bleed + bad shift) | **FALSIFIED** | 176.4 ms |
| **3. Net (WireGuard)** | `P3.1` | Inductive suite: `init_replay` + `accept_nonce` preserves `inv_replay_window` | **PROVED** | 16.5 ms |
| **3. Net (WireGuard)** | `P3.2` | `contract_duplicate_always_rejected` (2nd call NEVER accepts duplicate) | **PROVED** | 104.1 ms |
| **3. Net (WireGuard)** | `P3.3` | `contract_large_jump_clears_stale` (`delta >= 64` resets `bitmap = 1`, rejects stale) | **PROVED** | 198.0 ms |
| **3. Net (WireGuard)** | `P3.4` | `replay_check_branchless ≡ replay_check_branchy` (all `2^192` inputs) | **PROVED** | 51.6 ms |
| **3. Net (WireGuard)** | `P3.BUG1` | `accept_nonce_buggy_shift64_wrap` (`contract_large_jump_clears_stale`) | **FALSIFIED** | 19.8 ms |
| **3. Net (WireGuard)** | `P3.BUG2` | `accept_nonce_buggy_shift64_wrap` vs `accept_nonce` (`check-goal`) | **FALSIFIED** | 169.8 ms |
| **4. Cloud Quota** | `P4.1` | Inductive suite: `init_quota` + `reserve,commit,cancel_reserve` preserves `inv_quota_saga` | **PROVED** | 11,860.0 ms |
| **4. Cloud Quota** | `P4.2` | `contract_no_double_release` (duplicate `cancel_reserve` idempotent, 0 quota leak) | **PROVED** | 7,528.6 ms |
| **4. Cloud Quota** | `P4.3` | `contract_no_double_commit` (duplicate `commit` idempotent) | **PROVED** | 1,385.8 ms |
| **4. Cloud Quota** | `P4.BUG1` | `cancel_reserve_buggy_double_release` (inductive suite: 3/4 `PROVED`, buggy cancel `FALSIFIED`) | **FALSIFIED** | 9,155.2 ms |
| **4. Cloud Quota** | `P4.BUG2` | `cancel_reserve_buggy_double_release` (`contract_no_double_release`) | **FALSIFIED** | 32.9 ms |
| **5. Crypto (TLS/AEAD)** | `P5.1` | `pkcs7_unpad16_opt ≡ pkcs7_unpad16_ref` (`--ignore-dead-stack`) | **PROVED** | 325.1 ms |
| **5. Crypto (TLS/AEAD)** | `P5.2` | `pkcs7_unpad16_opt` complete RFC 5652 postcondition + `SliceFrame readonly` | **PROVED** | 58.6 ms |
| **5. Crypto (TLS/AEAD)** | `P5.3` | `pkcs7_unpad16_ref` trap-free + `SliceFrame readonly --ignore-dead-stack` | **PROVED** | 30.5 ms |
| **5. Crypto (TLS/AEAD)** | `P5.4` | `pkcs7_unpad16_branchless ≡ pkcs7_unpad16_branchy` (all `2^128` 16B blocks) | **PROVED** | 411.8 ms |
| **5. Crypto (TLS/AEAD)** | `P5.5` | `ct_mac16_eq_v128 ≡ ct_mac16_eq_ref` (`v128.xor` + `v128.any_true`, all `2^256`) | **PROVED** | 29.2 ms |
| **5. Crypto (TLS/AEAD)** | `P5.6` | `contract_mac16_1bit_flip_rejected` (all 128 MAC tag bits) | **PROVED** | 7.5 ms |
| **5. Crypto (TLS/AEAD)** | `P5.7` | `chacha20_col_round_v128 ≡ chacha20_col_round_ref` (RFC 8439, all `2^512` state bits) | **PROVED** | 1,594.8 ms |
| **5. Crypto (TLS/AEAD)** | `P5.8` | `chacha20_col_round_v128` `SliceFrame param:0:64` write containment | **PROVED** | 437.4 ms |
| **5. Crypto (TLS/AEAD)** | `P5.BUG1` | `pkcs7_unpad16_buggy_zero_pad_oracle` (`pad == 0` accepted — padding oracle CVE) | **FALSIFIED** | 40.2 ms |
| **5. Crypto (TLS/AEAD)** | `P5.BUG2` | `ct_mac16_buggy_off_by_one` (15-of-16B tag check -> 1-bit forgery at bit 127) | **FALSIFIED** | 6.1 ms |
| **5. Crypto (TLS/AEAD)** | `P5.BUG3` | `chacha20_col_round_buggy_rot` (RFC 8439 `rotl(15)` typo vs `rotl(16)`) | **FALSIFIED** | 537.5 ms |
| **6. Robotics (Flight PID)** | `P6.1` | Inductive stateful IEEE-754 `QF_ABVFP` suite: `init_pid` + `step_pid,clear_estop` -> `inv_pid_safe` | **PROVED** | 173.3 ms |
| **6. Robotics (Flight PID)** | `P6.2` | `contract_estop_forces_zero` (`estop != 0 => +0.0` under `NaN`/`±Inf` + latched persistence on next `estop=0` tick) | **PROVED** | 10.6 ms |
| **6. Robotics (Flight PID)** | `P6.3` | `contract_nan_sensor_never_poisons` (`NaN`/`±Inf` glitch leaves `INTEGRATOR` untainted) | **PROVED** | 5.3 ms |
| **6. Robotics (Flight PID)** | `P6.4` | `contract_slew_rate_bounded` (sharp 1-ULP IEEE-754 bound `\|out - old_prev\| <= 0.25 + 2^-25` & `\|out\| <= 1.0`) | **PROVED** | 3,194.0 ms |
| **6. Robotics (Flight PID)** | `P6.5` | `quad_mixer_4_opt` (`2^23` magic-bias RNE) `≡ quad_mixer_4_v128` (`f32x4.nearest`, all `2^160`) | **PROVED** | 2,758.8 ms |
| **6. Robotics (Flight PID)** | `P6.6` | `quad_mixer_4_opt ≡ quad_mixer_4_scalar` (portable RNE ref, all `2^160`) | **PROVED** | 4,959.3 ms |
| **6. Robotics (Flight PID)** | `P6.7` | `quad_mixer_4_opt` `ens_quad_mixer_safe` (`[0..=4095]`, E-stop/NaN/Inf -> `0`) | **PROVED** | 3,300.6 ms |
| **6. Robotics (Flight PID)** | `P6.BUG1a` | `step_pid_buggy_nan_clamp` (inductive: naive clamp passes `NaN` into `INTEGRATOR`) | **FALSIFIED** | 182.6 ms |
| **6. Robotics (Flight PID)** | `P6.BUG1b` | `step_pid_buggy_nan_clamp` (`contract_nan_sensor_never_poisons`) | **FALSIFIED** | 189.3 ms |
| **6. Robotics (Flight PID)** | `P6.BUG2` | `quad_mixer_buggy_nan_full_throttle` (`NaN` sensor -> `4095` full-throttle crash!) | **FALSIFIED** | 282.9 ms |
| **7. OS Kernel (`W^X` MMU)** | `P7.1` | Inductive suite: `init_mmu` + `map_region,mprotect_region,unmap_region` -> `inv_mmu_wx` | **PROVED** | 1,699.4 ms |
| **7. OS Kernel (`W^X` MMU)** | `P7.2` | `contract_no_wx_escalation` (global virtual-address `W^X` non-interference across all `2^32`) | **PROVED** | 2,897.3 ms |
| **7. OS Kernel (`W^X` MMU)** | `P7.3` | `contract_unmap_revokes_access` (immediate revocation, zero alias leaks) | **PROVED** | 7,709.6 ms |
| **7. OS Kernel (`W^X` MMU)** | `P7.4` | `tlb_check_4_v128 ≡ tlb_check_4_ref` (4-way `u32x4` parallel TLB lookup) | **PROVED** | 122.9 ms |
| **7. OS Kernel (`W^X` MMU)** | `P7.5` | `tlb_check_4_branchless ≡ tlb_check_4_ref` (exact native-profiled branchless TLB) | **PROVED** | 109.6 ms |
| **7. OS Kernel (`W^X` MMU)** | `P7.6` | `tlb_check_4_branchless` trap-free + `SliceFrame readonly` | **PROVED** | 6.8 ms |
| **7. OS Kernel (`W^X` MMU)** | `P7.7` | `tlb_check_4_v128` trap-free + `SliceFrame readonly` | **PROVED** | 6.7 ms |
| **7. OS Kernel (`W^X` MMU)** | `P7.BUG1` | `map_region_buggy_wrap_overlap` (`base + len` `u32` wraparound overlap CVE) | **FALSIFIED** | 589.2 ms |
| **7. OS Kernel (`W^X` MMU)** | `P7.BUG2` | `mprotect_buggy_wx_escalation` (`RWX` privilege escalation caught by global `W^X` contract) | **FALSIFIED** | 36.2 ms |
| **7. OS Kernel (`W^X` MMU)** | `P7.BUG3` | `tlb_check_4_buggy_signed_cmp` (signed addr compare fails at `>= 0x8000_0000`) | **FALSIFIED** | 155.0 ms |

---

## 3. Native Cross-Architecture Hardware Profiling (`gnomon profile --compare --targets x64,arm64 --bench`)

```bash
GN=./target/release/gnomon
VP=examples/vertical_packs

$GN profile "$VP/ai_q8_0_quant.rs" --compare "$VP/ai_q8_0_quant.rs" --entry q8_0_scale_scalar --opt-entry q8_0_scale_vec --targets x64,arm64
$GN profile "$VP/db_parquet_varint_slice.rs" --compare "$VP/db_parquet_varint_slice.rs" --entry varint_decode_branchy_ref --opt-entry varint_decode_branchless_opt --targets x64,arm64
$GN profile "$VP/net_wireguard_replay.rs" --compare "$VP/net_wireguard_replay.rs" --entry replay_check_branchy --opt-entry replay_check_branchless --targets x64,arm64
$GN profile "$VP/crypto_ct_tls_record.rs" --compare "$VP/crypto_ct_tls_record.rs" --entry pkcs7_unpad16_branchy --opt-entry pkcs7_unpad16_branchless --targets x64,arm64 --bench --bench-inputs '[["0x4142434445464748","0x04040404494a4b4c"],["0x1122334455667788","0x0808080808080808"],["0x0c0c0c0c41424344","0x0c0c0c0c0c0c0c0c"],["0x1010101010101010","0x1010101010101010"],["0x10101010101010ff","0x1010101010101010"]]'
$GN profile "$VP/robotics_flight_pid_mixer.rs" --compare "$VP/robotics_flight_pid_mixer.rs" --entry quad_mixer_4_scalar --opt-entry quad_mixer_4_opt --targets x64,arm64 --bench --bench-inputs '[[0.65,0.08,-0.05,0.02,0],[0.50,-0.12,0.10,-0.04,0],[0.85,0.20,0.15,0.05,0],[0.20,-0.25,-0.10,0.08,0]]'
$GN profile "$VP/os_mmu_wx_tlb.rs" --compare "$VP/os_mmu_wx_tlb.rs" --entry tlb_check_4_ref --opt-entry tlb_check_4_branchless --targets x64,arm64 --bench --bench-inputs '[[[4096,65536,131072,262144],[4096,8192,16384,32768],[5,3,1,5],266240,4],[[4096,65536,131072,262144],[4096,8192,16384,32768],[5,3,1,5],135168,1],[[4096,65536,131072,262144],[4096,8192,16384,32768],[5,3,1,5],524288,1],[[4096,65536,131072,262144],[4096,8192,16384,32768],[5,3,1,5],270336,2]]'
```

### Measured `x64` (`skylake`), `arm64` (`neoverse-v2`) & Live Host Results

| Pack & Pair (`ref -> opt`) | x64 (`skylake`) Inst / Br / SIMD / Stack / Spills | x64 Cyc & RTh Speedup | ARM64 (`neoverse-v2`) Inst / Br / SIMD / Stack / Spills | ARM64 Cyc & RTh Speedup | Host `ns/op` |
| --- | --- | --- | --- | --- | --- |
| **1. AI `Q8_0`** (`q8_0_scale_scalar -> q8_0_scale_vec`) | `101 -> 81` (`-20`) / br `2 -> 2` / simd `64 -> 63` / `0B` / `0 -> 0` | **2.61×** (`79.06 -> 30.33`) / **1.01×** (`20.2 -> 20.0`) | `89 -> 52` (`-37`) / **br `2 -> 0` (`-2`)** / **NEON `13 -> 33` (`+20`)** / `0B` / `0 -> 0` | **1.57×** (`19.73 -> 12.59`) / **1.71×** (`16.2 -> 9.5`) | — |
| **2. DB Varint** (`varint_decode_branchy_ref -> _branchless_opt`) | `38 -> 42` (`+4`) / **br `4 -> 0` (`-4`)** / `0` / `0B` / `0 -> 0` | **1.02×** (`10.59 -> 10.36`) / **1.10×** (`8.0 -> 7.3`) | `23 -> 26` (`+3`) / **br `3 -> 0` (`-3`)** / `0` / `0B` / `0 -> 0` | **1.50×** (`15.03 -> 10.04`) / `0.88×` (`3.8 -> 4.3`) | — |
| **3. Net Replay** (`replay_check_branchy -> _branchless`) | `10 -> 11` (`+1`) / **br `2 -> 0` (`-2`)** / `0` / `0B` / `0 -> 0` | `0.99×` (`2.60 -> 2.62`) / `0.91×` (`2.0 -> 2.2`) | `9 -> 9` (`0`) / br `0 -> 0` *(LLVM `csel`)* / `0` / `0B` / `0 -> 0` | `1.00×` (`5.03 -> 5.03`) / `1.00×` (`1.5 -> 1.5`) | — |
| **5. Crypto PKCS#7** (`pkcs7_unpad16_branchy -> _branchless`) | `132 -> 39` (`-93`) / **br `34 -> 0`** *(CT audit!)* / `0` / `0B` / `0 -> 0` | **3.38×** (`33.34 -> 9.85`) / **3.72×** (`29.0 -> 7.8`) | `101 -> 29` (`-72`) / **br `37 -> 0`** *(CT audit!)* / `0` / `0B` / `0 -> 0` | **3.30×** (`20.05 -> 6.08`) / **4.17×** (`20.0 -> 4.8`) | `7.49 -> 5.39` (**1.39×**) |
| **6. Robotics Mixer** (`quad_mixer_4_scalar -> _opt`) | `121 -> 51` (`-70`) / **br `17 -> 0`** / simd `60 -> 38` / `0B` / `0 -> 0` | **3.67×** (`54.22 -> 14.78`) / **2.89×** (`27.5 -> 9.5`) | `116 -> 71` (`-45`) / **br `17 -> 0`** / **NEON `0 -> 35` (`+35`)** / `0B` / `0 -> 0` | **1.08×** (`27.19 -> 25.16`) / **1.50×** (`20.0 -> 13.3`) | `17.28 -> 8.95` (**1.93×**) |
| **7. OS 4-Way TLB** (`tlb_check_4_ref -> _branchless`) | `53 -> 27` (`-26`) / **br `20 -> 0`** / **AVX2 `0 -> 20` (`+20`)** / `0B` / `0 -> 0` | `0.65×` cyc\* / **2.16×** RTh (`10.8 -> 5.0`) | `49 -> 24` (`-25`) / **br `18 -> 0`** / **NEON `0 -> 18` (`+18`)** / `0B` / `0 -> 0` | `0.39×` cyc\* / **2.38×** RTh (`10.0 -> 4.2`) | `7.49 -> 4.89` (**1.53×**) |

*\*For Pack 7 (`tlb_check_4_ref -> tlb_check_4_branchless`), `llvm-mca` reports higher `cycles_per_iter` on `branchless` both because `llvm-mca` omits branch-misprediction penalties on the 20/18 early-exit jumps of `ref` AND because `llvm-mca`'s 100-iteration loop introduces synthetic cross-iteration register dependencies where `branchless` overwrites an input register (`dec r8d` on x64; return `w0` aliasing `x0` on ARM64). Real issue throughput (`RThroughput`) improves **2.16× (x64) / 2.38× (ARM64)** and live host execution speeds up **1.53×–1.72×**.*
