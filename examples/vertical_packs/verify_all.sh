#!/usr/bin/env bash
set -euo pipefail

export PATH="/usr/lib/llvm-23/bin:$HOME/.cargo/bin:$HOME/.local/bitwuzla/bin:$HOME/.local/bin:$PATH"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
OUT_DIR="$SCRIPT_DIR/out"
GNOMON="${GNOMON:-$REPO_ROOT/target/release/gnomon}"

if ! command -v rustc >/dev/null 2>&1; then
    echo "error: rustc not found in PATH" >&2
    exit 1
fi
if [ ! -x "$GNOMON" ]; then
    echo "error: gnomon binary not found or not executable at $GNOMON" >&2
    exit 1
fi

mkdir -p "$OUT_DIR"
rm -f "$OUT_DIR"/*.wasm "$OUT_DIR"/*.rlib

SIMD_FIXTURES=(
    "ai_q8_0_quant"
    "ai_q8_0_quant_buggy"
    "crypto_ct_tls_record"
    "crypto_ct_tls_record_buggy"
    "robotics_flight_pid_mixer"
    "robotics_flight_pid_mixer_buggy"
    "os_mmu_wx_tlb"
    "os_mmu_wx_tlb_buggy"
)

CORE_FIXTURES=(
    "db_parquet_varint_slice"
    "db_parquet_varint_slice_buggy"
    "net_wireguard_replay"
    "net_wireguard_replay_buggy"
    "cloud_quota_saga"
    "cloud_quota_saga_buggy"
)

NATIVE_PORTABLE_FIXTURES=(
    "ai_q8_0_quant"
    "db_parquet_varint_slice"
    "net_wireguard_replay"
    "cloud_quota_saga"
    "crypto_ct_tls_record"
    "robotics_flight_pid_mixer"
    "os_mmu_wx_tlb"
)

build_and_lift() {
    local name="$1"
    local simd="$2"
    local src="$SCRIPT_DIR/${name}.rs"
    local wasm="$OUT_DIR/${name}.wasm"
    local rt="$OUT_DIR/${name}.roundtrip.wasm"
    local flags=(--target wasm32-unknown-unknown --crate-type=cdylib -O -C panic=abort -D warnings)
    if [ "$simd" = "1" ]; then
        flags+=(-C target-feature=+simd128)
    fi

    rustc "${flags[@]}" "$src" -o "$wasm"
    local lift_json
    lift_json="$("$GNOMON" lift "$wasm" --emit-wasm "$rt")"
    if [[ "$lift_json" != *'"roundtrip_wasm_valid": true'* ]]; then
        echo "error: round-trip validation failed for $name" >&2
        echo "$lift_json" >&2
        exit 1
    fi
    "$GNOMON" lift "$rt" >/dev/null
    rm -f "$rt"

    local bytes globals contracts
    bytes="$(wc -c < "$wasm")"
    globals="$(printf '%s\n' "$lift_json" | sed -n 's/.*"globals": \([0-9]*\).*/\1/p' | head -n 1)"
    contracts="$(printf '%s\n' "$lift_json" | sed -n 's/.*"host_contracts": \([0-9]*\).*/\1/p' | head -n 1)"
    echo "[lift-ok] ${name}.wasm (${bytes} B, globals=${globals}, host_contracts=${contracts}, roundtrip=true)"
}

PROVED_COUNT=0
FALSIFIED_COUNT=0

run_expect() {
    local label="$1"
    local expected_exit="$2"
    local expected_status="$3"
    shift 3

    local out=""
    local rc=0
    out="$("$GNOMON" "$@" 2>&1)" || rc=$?
    if [ "$rc" -ne "$expected_exit" ]; then
        echo "[FAIL] $label: exit=$rc (expected $expected_exit)" >&2
        echo "$out" >&2
        exit 1
    fi
    if [[ "$out" != *"\"status\": \"$expected_status\""* ]]; then
        echo "[FAIL] $label: status mismatch (expected $expected_status)" >&2
        echo "$out" >&2
        exit 1
    fi
    local elapsed
    elapsed="$(printf '%s\n' "$out" | sed -n 's/.*"elapsed_ms": \([0-9.]*\).*/\1/p' | head -n 1)"
    echo "[${expected_status}] ${label} (${elapsed} ms)"
    if [ "$expected_status" = "PROVED" ]; then
        PROVED_COUNT=$((PROVED_COUNT + 1))
    else
        FALSIFIED_COUNT=$((FALSIFIED_COUNT + 1))
    fi
}

echo "=== 1. Compile (-D warnings) & Round-Trip Lift All 14 Vertical Pack Modules ==="
for name in "${SIMD_FIXTURES[@]}"; do
    build_and_lift "$name" 1
done
for name in "${CORE_FIXTURES[@]}"; do
    build_and_lift "$name" 0
done

echo ""
echo "=== 2. Native x86_64 Compile Check (-D warnings, 7 Portable Packs) ==="
for name in "${NATIVE_PORTABLE_FIXTURES[@]}"; do
    rustc --crate-type=lib -O -D warnings "$SCRIPT_DIR/${name}.rs" -o "$OUT_DIR/${name}.rlib"
    rm -f "$OUT_DIR/${name}.rlib"
    echo "[native-ok] ${name}.rs (0 warnings)"
done

echo ""
echo "=== 3. Pack 1: AI Inference (llama.cpp / GGML Q8_0 Quantization) ==="
run_expect "P1.1 q8_0_quant_4_v128 === q8_0_quant_4_ref" 0 PROVED \
    check-goal --candidate "$OUT_DIR/ai_q8_0_quant.wasm" --candidate-entry q8_0_quant_4_v128 \
    --spec "$OUT_DIR/ai_q8_0_quant.wasm" --spec-entry q8_0_quant_4_ref --timeout-ms 15000
run_expect "P1.2 req_finite_block => ens_q8_0_safe" 0 PROVED \
    check-contract "$OUT_DIR/ai_q8_0_quant.wasm" --entry q8_0_quant_4_v128 \
    --requires req_finite_block --ensures ens_q8_0_safe --timeout-ms 15000
run_expect "P1.3 contract_q8_0_quant_4" 0 PROVED \
    check-contract "$OUT_DIR/ai_q8_0_quant.wasm" --entry contract_q8_0_quant_4 --timeout-ms 15000
run_expect "P1.BUG1 q8_0_buggy_zero_nan" 1 FALSIFIED \
    check-contract "$OUT_DIR/ai_q8_0_quant_buggy.wasm" --entry q8_0_buggy_zero_nan \
    --requires req_finite_block --ensures ens_q8_0_safe --timeout-ms 15000
run_expect "P1.BUG2 q8_0_buggy_trunc_bias" 1 FALSIFIED \
    check-goal --candidate "$OUT_DIR/ai_q8_0_quant_buggy.wasm" --candidate-entry q8_0_buggy_trunc_bias \
    --spec "$OUT_DIR/ai_q8_0_quant.wasm" --spec-entry q8_0_quant_4_ref --timeout-ms 15000

echo ""
echo "=== 4. Pack 2: Columnar DB / Parquet Varint Slice + Delta-ZigZag ==="
run_expect "P2.1 varint_decode_opt === varint_decode_ref (--ignore-dead-stack)" 0 PROVED \
    check-goal --candidate "$OUT_DIR/db_parquet_varint_slice.wasm" --candidate-entry varint_decode_opt \
    --spec "$OUT_DIR/db_parquet_varint_slice.wasm" --spec-entry varint_decode_ref \
    --pre "$OUT_DIR/db_parquet_varint_slice.wasm" --pre-entry req_varint_slice --ignore-dead-stack
run_expect "P2.2 varint_decode_opt SliceFrame readonly" 0 PROVED \
    check-contract "$OUT_DIR/db_parquet_varint_slice.wasm" --entry varint_decode_opt \
    --requires req_varint_slice --slice-frame readonly
run_expect "P2.3 varint_decode_ref SliceFrame readonly --ignore-dead-stack" 0 PROVED \
    check-contract "$OUT_DIR/db_parquet_varint_slice.wasm" --entry varint_decode_ref \
    --requires req_varint_slice --slice-frame readonly --ignore-dead-stack
run_expect "P2.4 zigzag_enc_dec_roundtrip === identity_i64" 0 PROVED \
    check-goal --candidate "$OUT_DIR/db_parquet_varint_slice.wasm" --candidate-entry zigzag_enc_dec_roundtrip \
    --spec "$OUT_DIR/db_parquet_varint_slice.wasm" --spec-entry identity_i64
run_expect "P2.5 contract_zigzag_roundtrip" 0 PROVED \
    check-contract "$OUT_DIR/db_parquet_varint_slice.wasm" --entry contract_zigzag_roundtrip
run_expect "P2.6 varint_decode_branchless_opt === varint_decode_branchy_ref" 0 PROVED \
    check-goal --candidate "$OUT_DIR/db_parquet_varint_slice.wasm" --candidate-entry varint_decode_branchless_opt \
    --spec "$OUT_DIR/db_parquet_varint_slice.wasm" --spec-entry varint_decode_branchy_ref
run_expect "P2.BUG1 varint_decode_buggy_short_read" 1 FALSIFIED \
    check-contract "$OUT_DIR/db_parquet_varint_slice_buggy.wasm" --entry varint_decode_buggy_short_read \
    --requires req_varint_slice
run_expect "P2.BUG2 varint_decode_buggy_shift_overflow" 1 FALSIFIED \
    check-goal --candidate "$OUT_DIR/db_parquet_varint_slice_buggy.wasm" --candidate-entry varint_decode_buggy_shift_overflow \
    --spec "$OUT_DIR/db_parquet_varint_slice.wasm" --spec-entry varint_decode_ref \
    --pre "$OUT_DIR/db_parquet_varint_slice.wasm" --pre-entry req_varint_slice --ignore-dead-stack

echo ""
echo "=== 5. Pack 3: Networking / WireGuard RFC 6479 Anti-Replay Window ==="
run_expect "P3.1 init_replay + accept_nonce -> inv_replay_window" 0 PROVED \
    check-contract "$OUT_DIR/net_wireguard_replay.wasm" --init init_replay --ops accept_nonce --invariant inv_replay_window
run_expect "P3.2 contract_duplicate_always_rejected" 0 PROVED \
    check-contract "$OUT_DIR/net_wireguard_replay.wasm" --entry contract_duplicate_always_rejected
run_expect "P3.3 contract_large_jump_clears_stale" 0 PROVED \
    check-contract "$OUT_DIR/net_wireguard_replay.wasm" --entry contract_large_jump_clears_stale
run_expect "P3.4 replay_check_branchless === replay_check_branchy" 0 PROVED \
    check-goal --candidate "$OUT_DIR/net_wireguard_replay.wasm" --candidate-entry replay_check_branchless \
    --spec "$OUT_DIR/net_wireguard_replay.wasm" --spec-entry replay_check_branchy
run_expect "P3.BUG1 accept_nonce_buggy_shift64_wrap (contract)" 1 FALSIFIED \
    check-contract "$OUT_DIR/net_wireguard_replay_buggy.wasm" --entry contract_large_jump_clears_stale
run_expect "P3.BUG2 accept_nonce_buggy_shift64_wrap (goal)" 1 FALSIFIED \
    check-goal --candidate "$OUT_DIR/net_wireguard_replay_buggy.wasm" --candidate-entry accept_nonce_buggy_shift64_wrap \
    --spec "$OUT_DIR/net_wireguard_replay.wasm" --spec-entry accept_nonce

echo ""
echo "=== 6. Pack 4: Distributed Cloud Quota / Reservation Saga ==="
run_expect "P4.1 init_quota + reserve,commit,cancel_reserve -> inv_quota_saga" 0 PROVED \
    check-contract "$OUT_DIR/cloud_quota_saga.wasm" --init init_quota \
    --ops reserve,commit,cancel_reserve --invariant inv_quota_saga --timeout-ms 20000
run_expect "P4.2 contract_no_double_release" 0 PROVED \
    check-contract "$OUT_DIR/cloud_quota_saga.wasm" --entry contract_no_double_release --timeout-ms 15000
run_expect "P4.3 contract_no_double_commit" 0 PROVED \
    check-contract "$OUT_DIR/cloud_quota_saga.wasm" --entry contract_no_double_commit --timeout-ms 15000
run_expect "P4.BUG1 cancel_reserve_buggy_double_release (inductive)" 1 FALSIFIED \
    check-contract "$OUT_DIR/cloud_quota_saga_buggy.wasm" --init init_quota \
    --ops reserve,commit,cancel_reserve_buggy_double_release --invariant inv_quota_saga --timeout-ms 20000
run_expect "P4.BUG2 cancel_reserve_buggy_double_release (contract)" 1 FALSIFIED \
    check-contract "$OUT_DIR/cloud_quota_saga_buggy.wasm" --entry contract_no_double_release --timeout-ms 15000

echo ""
echo "=== 7. Pack 5: Cryptography / Constant-Time TLS & AEAD Security ==="
run_expect "P5.1 pkcs7_unpad16_opt === pkcs7_unpad16_ref (--ignore-dead-stack)" 0 PROVED \
    check-goal --candidate "$OUT_DIR/crypto_ct_tls_record.wasm" --candidate-entry pkcs7_unpad16_opt \
    --spec "$OUT_DIR/crypto_ct_tls_record.wasm" --spec-entry pkcs7_unpad16_ref \
    --pre "$OUT_DIR/crypto_ct_tls_record.wasm" --pre-entry req_block16_slice --ignore-dead-stack --timeout-ms 15000
run_expect "P5.2 pkcs7_unpad16_opt RFC 5652 contract + SliceFrame readonly" 0 PROVED \
    check-contract "$OUT_DIR/crypto_ct_tls_record.wasm" --entry pkcs7_unpad16_opt \
    --requires req_block16_slice --ensures ens_pkcs7_unpad16 --slice-frame readonly --timeout-ms 15000
run_expect "P5.3 pkcs7_unpad16_ref SliceFrame readonly --ignore-dead-stack" 0 PROVED \
    check-contract "$OUT_DIR/crypto_ct_tls_record.wasm" --entry pkcs7_unpad16_ref \
    --requires req_block16_slice --slice-frame readonly --ignore-dead-stack --timeout-ms 15000
run_expect "P5.4 pkcs7_unpad16_branchless === pkcs7_unpad16_branchy (all 2^128)" 0 PROVED \
    check-goal --candidate "$OUT_DIR/crypto_ct_tls_record.wasm" --candidate-entry pkcs7_unpad16_branchless \
    --spec "$OUT_DIR/crypto_ct_tls_record.wasm" --spec-entry pkcs7_unpad16_branchy --timeout-ms 15000
run_expect "P5.5 ct_mac16_eq_v128 === ct_mac16_eq_ref (all 2^256)" 0 PROVED \
    check-goal --candidate "$OUT_DIR/crypto_ct_tls_record.wasm" --candidate-entry ct_mac16_eq_v128 \
    --spec "$OUT_DIR/crypto_ct_tls_record.wasm" --spec-entry ct_mac16_eq_ref --timeout-ms 15000
run_expect "P5.6 contract_mac16_1bit_flip_rejected (all 128 bits)" 0 PROVED \
    check-contract "$OUT_DIR/crypto_ct_tls_record.wasm" --entry contract_mac16_1bit_flip_rejected --timeout-ms 15000
run_expect "P5.7 chacha20_col_round_v128 === chacha20_col_round_ref (all 2^512)" 0 PROVED \
    check-goal --candidate "$OUT_DIR/crypto_ct_tls_record.wasm" --candidate-entry chacha20_col_round_v128 \
    --spec "$OUT_DIR/crypto_ct_tls_record.wasm" --spec-entry chacha20_col_round_ref \
    --pre "$OUT_DIR/crypto_ct_tls_record.wasm" --pre-entry req_chacha_state --timeout-ms 15000
run_expect "P5.8 chacha20_col_round_v128 SliceFrame param:0:64" 0 PROVED \
    check-contract "$OUT_DIR/crypto_ct_tls_record.wasm" --entry chacha20_col_round_v128 \
    --requires req_chacha_state --slice-frame param:0:64 --timeout-ms 15000
run_expect "P5.BUG1 pkcs7_unpad16_buggy_zero_pad_oracle" 1 FALSIFIED \
    check-contract "$OUT_DIR/crypto_ct_tls_record_buggy.wasm" --entry pkcs7_unpad16_buggy_zero_pad_oracle \
    --requires req_block16_slice --ensures ens_pkcs7_unpad16 --timeout-ms 15000
run_expect "P5.BUG2 ct_mac16_buggy_off_by_one (1-bit forgery)" 1 FALSIFIED \
    check-contract "$OUT_DIR/crypto_ct_tls_record_buggy.wasm" --entry contract_mac16_1bit_flip_rejected --timeout-ms 15000
run_expect "P5.BUG3 chacha20_col_round_buggy_rot" 1 FALSIFIED \
    check-goal --candidate "$OUT_DIR/crypto_ct_tls_record_buggy.wasm" --candidate-entry chacha20_col_round_buggy_rot \
    --spec "$OUT_DIR/crypto_ct_tls_record.wasm" --spec-entry chacha20_col_round_ref \
    --pre "$OUT_DIR/crypto_ct_tls_record.wasm" --pre-entry req_chacha_state --timeout-ms 15000

echo ""
echo "=== 8. Pack 6: Safety-Critical Robotics / Aerospace Flight PID + 4-Motor Mixer ==="
run_expect "P6.1 init_pid + step_pid,clear_estop -> inv_pid_safe (QF_ABVFP)" 0 PROVED \
    check-contract "$OUT_DIR/robotics_flight_pid_mixer.wasm" --init init_pid \
    --ops step_pid,clear_estop --invariant inv_pid_safe --timeout-ms 20000
run_expect "P6.2 contract_estop_forces_zero" 0 PROVED \
    check-contract "$OUT_DIR/robotics_flight_pid_mixer.wasm" --entry contract_estop_forces_zero --timeout-ms 15000
run_expect "P6.3 contract_nan_sensor_never_poisons" 0 PROVED \
    check-contract "$OUT_DIR/robotics_flight_pid_mixer.wasm" --entry contract_nan_sensor_never_poisons --timeout-ms 15000
run_expect "P6.4 contract_slew_rate_bounded" 0 PROVED \
    check-contract "$OUT_DIR/robotics_flight_pid_mixer.wasm" --entry contract_slew_rate_bounded --timeout-ms 20000
run_expect "P6.5 quad_mixer_4_opt (2^23 magic bias) === quad_mixer_4_v128" 0 PROVED \
    check-goal --candidate "$OUT_DIR/robotics_flight_pid_mixer.wasm" --candidate-entry quad_mixer_4_opt \
    --spec "$OUT_DIR/robotics_flight_pid_mixer.wasm" --spec-entry quad_mixer_4_v128 --timeout-ms 15000
run_expect "P6.6 quad_mixer_4_opt === quad_mixer_4_scalar (all 2^160)" 0 PROVED \
    check-goal --candidate "$OUT_DIR/robotics_flight_pid_mixer.wasm" --candidate-entry quad_mixer_4_opt \
    --spec "$OUT_DIR/robotics_flight_pid_mixer.wasm" --spec-entry quad_mixer_4_scalar --timeout-ms 15000
run_expect "P6.7 quad_mixer_4_opt ens_quad_mixer_safe" 0 PROVED \
    check-contract "$OUT_DIR/robotics_flight_pid_mixer.wasm" --entry quad_mixer_4_opt \
    --ensures ens_quad_mixer_safe --timeout-ms 15000
run_expect "P6.BUG1a step_pid_buggy_nan_clamp (inductive)" 1 FALSIFIED \
    check-contract "$OUT_DIR/robotics_flight_pid_mixer_buggy.wasm" --init init_pid \
    --ops step_pid_buggy_nan_clamp,clear_estop --invariant inv_pid_safe --timeout-ms 15000
run_expect "P6.BUG1b contract_nan_sensor_never_poisons (buggy)" 1 FALSIFIED \
    check-contract "$OUT_DIR/robotics_flight_pid_mixer_buggy.wasm" --entry contract_nan_sensor_never_poisons --timeout-ms 15000
run_expect "P6.BUG2 quad_mixer_buggy_nan_full_throttle" 1 FALSIFIED \
    check-contract "$OUT_DIR/robotics_flight_pid_mixer_buggy.wasm" --entry quad_mixer_buggy_nan_full_throttle \
    --ensures ens_quad_mixer_safe --timeout-ms 15000

echo ""
echo "=== 9. Pack 7: OS Kernel / Hypervisor W^X MMU & Vectorized 4-Way TLB ==="
run_expect "P7.1 init_mmu + map,mprotect,unmap -> inv_mmu_wx" 0 PROVED \
    check-contract "$OUT_DIR/os_mmu_wx_tlb.wasm" --init init_mmu \
    --ops map_region,mprotect_region,unmap_region --invariant inv_mmu_wx --timeout-ms 20000
run_expect "P7.2 contract_no_wx_escalation (global W^X non-interference)" 0 PROVED \
    check-contract "$OUT_DIR/os_mmu_wx_tlb.wasm" --entry contract_no_wx_escalation --timeout-ms 15000
run_expect "P7.3 contract_unmap_revokes_access (zero alias leak)" 0 PROVED \
    check-contract "$OUT_DIR/os_mmu_wx_tlb.wasm" --entry contract_unmap_revokes_access --timeout-ms 15000
run_expect "P7.4 tlb_check_4_v128 === tlb_check_4_ref" 0 PROVED \
    check-goal --candidate "$OUT_DIR/os_mmu_wx_tlb.wasm" --candidate-entry tlb_check_4_v128 \
    --spec "$OUT_DIR/os_mmu_wx_tlb.wasm" --spec-entry tlb_check_4_ref \
    --pre "$OUT_DIR/os_mmu_wx_tlb.wasm" --pre-entry req_tlb_tables --timeout-ms 15000
run_expect "P7.5 tlb_check_4_branchless === tlb_check_4_ref" 0 PROVED \
    check-goal --candidate "$OUT_DIR/os_mmu_wx_tlb.wasm" --candidate-entry tlb_check_4_branchless \
    --spec "$OUT_DIR/os_mmu_wx_tlb.wasm" --spec-entry tlb_check_4_ref \
    --pre "$OUT_DIR/os_mmu_wx_tlb.wasm" --pre-entry req_tlb_tables --timeout-ms 15000
run_expect "P7.6 tlb_check_4_branchless SliceFrame readonly" 0 PROVED \
    check-contract "$OUT_DIR/os_mmu_wx_tlb.wasm" --entry tlb_check_4_branchless \
    --requires req_tlb_tables --slice-frame readonly --timeout-ms 15000
run_expect "P7.7 tlb_check_4_v128 SliceFrame readonly" 0 PROVED \
    check-contract "$OUT_DIR/os_mmu_wx_tlb.wasm" --entry tlb_check_4_v128 \
    --requires req_tlb_tables --slice-frame readonly --timeout-ms 15000
run_expect "P7.BUG1 map_region_buggy_wrap_overlap (inductive)" 1 FALSIFIED \
    check-contract "$OUT_DIR/os_mmu_wx_tlb_buggy.wasm" --init init_mmu \
    --ops map_region_buggy_wrap_overlap,unmap_region --invariant inv_mmu_wx --timeout-ms 15000
run_expect "P7.BUG2 mprotect_buggy_wx_escalation (contract_no_wx_escalation)" 1 FALSIFIED \
    check-contract "$OUT_DIR/os_mmu_wx_tlb_buggy.wasm" --entry contract_no_wx_escalation --timeout-ms 15000
run_expect "P7.BUG3 tlb_check_4_buggy_signed_cmp (high-half address)" 1 FALSIFIED \
    check-goal --candidate "$OUT_DIR/os_mmu_wx_tlb_buggy.wasm" --candidate-entry tlb_check_4_buggy_signed_cmp \
    --spec "$OUT_DIR/os_mmu_wx_tlb.wasm" --spec-entry tlb_check_4_ref \
    --pre "$OUT_DIR/os_mmu_wx_tlb.wasm" --pre-entry req_tlb_tables --timeout-ms 15000

echo ""
echo "=== 10. Dual-Architecture Native Hardware Profiling (x64 skylake & arm64 neoverse-v2) ==="
"$GNOMON" profile "$SCRIPT_DIR/ai_q8_0_quant.rs" \
    --compare "$SCRIPT_DIR/ai_q8_0_quant.rs" \
    --entry q8_0_scale_scalar --opt-entry q8_0_scale_vec --targets x64,arm64 >/dev/null
echo "[profile-ok] Pack 1: ai_q8_0_quant (q8_0_scale_scalar -> q8_0_scale_vec)"

"$GNOMON" profile "$SCRIPT_DIR/db_parquet_varint_slice.rs" \
    --compare "$SCRIPT_DIR/db_parquet_varint_slice.rs" \
    --entry varint_decode_branchy_ref --opt-entry varint_decode_branchless_opt --targets x64,arm64 >/dev/null
echo "[profile-ok] Pack 2: db_parquet_varint_slice (varint_decode_branchy_ref -> _branchless_opt)"

"$GNOMON" profile "$SCRIPT_DIR/net_wireguard_replay.rs" \
    --compare "$SCRIPT_DIR/net_wireguard_replay.rs" \
    --entry replay_check_branchy --opt-entry replay_check_branchless --targets x64,arm64 >/dev/null
echo "[profile-ok] Pack 3: net_wireguard_replay (replay_check_branchy -> _branchless)"

"$GNOMON" profile "$SCRIPT_DIR/crypto_ct_tls_record.rs" \
    --compare "$SCRIPT_DIR/crypto_ct_tls_record.rs" \
    --entry pkcs7_unpad16_branchy --opt-entry pkcs7_unpad16_branchless --targets x64,arm64 --bench \
    --bench-inputs '[["0x4142434445464748","0x04040404494a4b4c"],["0x1122334455667788","0x0808080808080808"],["0x0c0c0c0c41424344","0x0c0c0c0c0c0c0c0c"],["0x1010101010101010","0x1010101010101010"],["0x10101010101010ff","0x1010101010101010"]]' >/dev/null
echo "[profile-ok] Pack 5: crypto_ct_tls_record (pkcs7_unpad16_branchy -> _branchless + host bench)"

"$GNOMON" profile "$SCRIPT_DIR/robotics_flight_pid_mixer.rs" \
    --compare "$SCRIPT_DIR/robotics_flight_pid_mixer.rs" \
    --entry quad_mixer_4_scalar --opt-entry quad_mixer_4_opt --targets x64,arm64 --bench \
    --bench-inputs '[[0.65,0.08,-0.05,0.02,0],[0.50,-0.12,0.10,-0.04,0],[0.85,0.20,0.15,0.05,0],[0.20,-0.25,-0.10,0.08,0]]' >/dev/null
echo "[profile-ok] Pack 6: robotics_flight_pid_mixer (quad_mixer_4_scalar -> _opt + host bench)"

"$GNOMON" profile "$SCRIPT_DIR/os_mmu_wx_tlb.rs" \
    --compare "$SCRIPT_DIR/os_mmu_wx_tlb.rs" \
    --entry tlb_check_4_ref --opt-entry tlb_check_4_branchless --targets x64,arm64 --bench \
    --bench-inputs '[[[4096,65536,131072,262144],[4096,8192,16384,32768],[5,3,1,5],266240,4],[[4096,65536,131072,262144],[4096,8192,16384,32768],[5,3,1,5],135168,1],[[4096,65536,131072,262144],[4096,8192,16384,32768],[5,3,1,5],524288,1],[[4096,65536,131072,262144],[4096,8192,16384,32768],[5,3,1,5],270336,2]]' >/dev/null
echo "[profile-ok] Pack 7: os_mmu_wx_tlb (tlb_check_4_ref -> _branchless + host bench)"

TOTAL=$((PROVED_COUNT + FALSIFIED_COUNT))
echo ""
echo "All 7 vertical packs (14 modules) built (-D warnings), round-trip lifted, profiled, and verified: ${TOTAL}/${TOTAL} exact verdicts (${PROVED_COUNT} PROVED, ${FALSIFIED_COUNT} FALSIFIED)."
