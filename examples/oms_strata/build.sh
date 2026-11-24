#!/usr/bin/env bash
set -euo pipefail

export PATH="/usr/lib/llvm-23/bin:$HOME/.cargo/bin:$HOME/.local/bitwuzla/bin:$HOME/.local/bin:$PATH"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
OUT_DIR="$SCRIPT_DIR/out"
STATE_FILE="$OUT_DIR/oms_strata_state.json"
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
rm -f "$STATE_FILE"

# Layer-1 pure foundational Strata (compiled & registered before Layer 2-4 callers)
LAYER1_FIXTURES=(
    "s1_1_notional_collar"
    "s1_2_barrett_tick_fee"
    "s1_3_order_id_mix"
    "s1_4_swar_fix_price"
)

# Layer 2-4 OMS Strata + buggy mutants + Step 4 performance-optimization pairs
LAYER2_4_FIXTURES=(
    "s2_1_spsc_ring"
    "s2_1_spsc_ring_buggy"
    "s2_2_order_slab_table"
    "s2_2_order_slab_table_buggy"
    "s2_3_wire_rx_decode"
    "s2_3_wire_rx_decode_buggy"
    "s2_4_wire_tx_encode"
    "s2_4_wire_tx_encode_buggy"
    "s3_1_child_fsm"
    "s3_1_child_fsm_buggy"
    "s3_2_parent_child_oms"
    "s3_2_parent_child_oms_buggy"
    "s3_3_pretrade_risk_gate"
    "s3_3_pretrade_risk_gate_buggy"
    "s3_4_l2_book_sweep_v128"
    "s3_4_l2_book_sweep_v128_buggy"
    "s3_5_signal_vwap_var_v128"
    "s3_5_signal_vwap_var_v128_buggy"
    "s4_1_oms_on_exec_report"
    "s4_1_oms_on_exec_report_buggy"
    "s4_2_oms_on_tick_or_order"
    "s4_2_oms_on_tick_or_order_buggy"
    "s4_3_perf_opt_pairs"
)

uses_simd128() {
    case "$1" in
        s3_4_*|s3_5_*|s4_2_*|s4_3_*) return 0 ;;
        *) return 1 ;;
    esac
}

uses_stratum_state() {
    case "$1" in
        s2_2_*|s3_3_*|s4_1_*|s4_2_*) return 0 ;;
        *) return 1 ;;
    esac
}

build_and_lift() {
    local name="$1"
    local src="$SCRIPT_DIR/${name}.rs"
    local wasm="$OUT_DIR/${name}.wasm"
    local rt="$OUT_DIR/${name}.roundtrip.wasm"
    local rustc_flags=(--target wasm32-unknown-unknown --crate-type=cdylib -O -C panic=abort -D warnings)

    if uses_simd128 "$name"; then
        rustc_flags+=(-C target-feature=+simd128)
        echo "[build] $name.rs -> out/$name.wasm (+simd128)"
    else
        echo "[build] $name.rs -> out/$name.wasm"
    fi

    rustc "${rustc_flags[@]}" "$src" -o "$wasm"

    local lift_json
    if uses_stratum_state "$name"; then
        echo "[lift]  out/$name.wasm (Stratum-linked lift + lowered round-trip check)"
        lift_json="$("$GNOMON" --state "$STATE_FILE" lift "$wasm" --lower --emit-wasm "$rt")"
        # Also confirm non-lowered Stratum lift preserves CallTarget::Stratum imports cleanly.
        "$GNOMON" --state "$STATE_FILE" lift "$wasm" >/dev/null
    else
        echo "[lift]  out/$name.wasm (round-trip check)"
        lift_json="$("$GNOMON" lift "$wasm" --emit-wasm "$rt")"
    fi

    if [[ "$lift_json" != *'"roundtrip_wasm_valid": true'* ]]; then
        echo "error: round-trip validation failed for $name" >&2
        echo "$lift_json" >&2
        exit 1
    fi

    # Verify round-tripped Wasm also lifts cleanly.
    "$GNOMON" lift "$rt" >/dev/null

    # Verify zero shadow-stack globals in s3_1 stateful FSM modules.
    if [[ "$name" == s3_1_* ]]; then
        if [[ "$lift_json" != *'"globals": 0'* ]]; then
            echo "error: expected globals == 0 (zero shadow stack) for $name" >&2
            exit 1
        fi
        if [[ "$lift_json" != *'"host_contracts": 2'* ]]; then
            echo "error: expected host_contracts == 2 (gnomon_assume/gnomon_assert) for $name" >&2
            exit 1
        fi
    fi

    echo "[ok]    $name lifted and round-tripped cleanly ($(wc -c < "$wasm") bytes)"
}

for name in "${LAYER1_FIXTURES[@]}"; do
    build_and_lift "$name"
done

echo "[state] Registering Layer-1 OMS Strata (order_id_mix, checked_notional, price_collar_ok)"
"$GNOMON" --state "$STATE_FILE" define-op \
    --name order_id_mix --layer 1 "$OUT_DIR/s1_3_order_id_mix.wasm" >/dev/null
"$GNOMON" --state "$STATE_FILE" define-op \
    --name checked_notional --entry checked_notional --layer 1 "$OUT_DIR/s1_1_notional_collar.wasm" >/dev/null
"$GNOMON" --state "$STATE_FILE" define-op \
    --name price_collar_ok --entry price_collar_ok --layer 1 "$OUT_DIR/s1_1_notional_collar.wasm" >/dev/null

for name in "${LAYER2_4_FIXTURES[@]}"; do
    build_and_lift "$name"
done

TOTAL=$(( ${#LAYER1_FIXTURES[@]} + ${#LAYER2_4_FIXTURES[@]} ))
echo "All $TOTAL OMS Strata fixtures (S1.1-S4.3 + all buggy mutants) compiled (-D warnings), lifted, and round-tripped cleanly."
