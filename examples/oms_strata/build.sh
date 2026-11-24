#!/usr/bin/env bash
set -euo pipefail

export PATH="$HOME/.cargo/bin:$HOME/.local/bitwuzla/bin:$HOME/.local/bin:$PATH"

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

FIXTURES=(
    "s1_1_notional_collar"
    "s3_1_child_fsm"
    "s3_1_child_fsm_buggy"
)

for name in "${FIXTURES[@]}"; do
    src="$SCRIPT_DIR/${name}.rs"
    wasm="$OUT_DIR/${name}.wasm"
    rt="$OUT_DIR/${name}.roundtrip.wasm"

    echo "[build] $name.rs -> out/$name.wasm"
    rustc --target wasm32-unknown-unknown --crate-type=cdylib -O -C panic=abort \
        "$src" -o "$wasm"

    echo "[lift]  out/$name.wasm (round-trip check)"
    lift_json="$("$GNOMON" lift "$wasm" --emit-wasm "$rt")"
    echo "$lift_json" | grep -q '"roundtrip_wasm_valid": true' || {
        echo "error: round-trip validation failed for $name" >&2
        echo "$lift_json" >&2
        exit 1
    }

    # Verify round-tripped Wasm also lifts cleanly.
    "$GNOMON" lift "$rt" >/dev/null

    # Verify zero shadow-stack globals in stateful FSM modules.
    if [[ "$name" == s3_1_* ]]; then
        echo "$lift_json" | grep -q '"globals": 0' || {
            echo "error: expected globals == 0 (zero shadow stack) for $name" >&2
            exit 1
        }
        echo "$lift_json" | grep -q '"host_contracts": 2' || {
            echo "error: expected host_contracts == 2 (gnomon_assume/gnomon_assert) for $name" >&2
            exit 1
        }
    fi

    echo "[ok]    $name lifted and round-tripped cleanly ($(wc -c < "$wasm") bytes)"
done

echo "All ${#FIXTURES[@]} OMS Strata fixtures compiled, lifted, and round-tripped cleanly."
