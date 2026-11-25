#!/usr/bin/env bash
set -euo pipefail

export PATH="/usr/lib/llvm-23/bin:$HOME/.cargo/bin:$HOME/.local/bitwuzla/bin:$HOME/.local/bin:$PATH"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
OUT_DIR="$SCRIPT_DIR/out"
STATE_FILE="$OUT_DIR/closed_loop_state.json"
GNOMON="${GNOMON:-$REPO_ROOT/target/release/gnomon}"

mkdir -p "$OUT_DIR"
rm -f "$STATE_FILE"

FILES=(
  "strata_l1"
  "strata_l1_laws"
  "k1_fix_ascii_price"
  "k2_sor_venue_router"
  "k3_oms_tick_risk_fastpath"
)

echo "=== 1. Dual-Target Compilation Check (-D warnings: wasm32 + native x86_64) ==="
for name in "${FILES[@]}"; do
  src="$SCRIPT_DIR/${name}.rs"
  rustc --target wasm32-unknown-unknown --crate-type=cdylib --edition=2024 -O -C panic=abort -D warnings "$src" -o "$OUT_DIR/${name}.wasm"
  rustc --crate-type=lib --edition=2024 -O -D warnings "$src" -o "$OUT_DIR/${name}.rlib"
  echo "[ok] ${name}.rs compiled cleanly for wasm32 + native x86_64 (0 warnings)"
done

echo ""
echo "=== 2. Layer-1 Strata Registration (define-op) & Algebraic Law Proof (prove-law) ==="
"$GNOMON" --state "$STATE_FILE" define-op --name sor_div_10k --entry sor_div_10k --layer 1 "$SCRIPT_DIR/strata_l1.rs"
"$GNOMON" --state "$STATE_FILE" define-op --name notional_le --entry notional_le --layer 1 "$SCRIPT_DIR/strata_l1.rs"
"$GNOMON" --state "$STATE_FILE" define-op --name collar_le --entry collar_le --layer 1 "$SCRIPT_DIR/strata_l1.rs"

"$GNOMON" --state "$STATE_FILE" prove-law \
  --op sor_div_10k \
  --name sor-div-10k-fold \
  --lhs "$SCRIPT_DIR/strata_l1_laws.rs" --lhs-entry sor_div_10k_reciprocal \
  --rhs "$SCRIPT_DIR/strata_l1_laws.rs" --rhs-entry sor_div_10k_stratum

echo ""
echo "=== 3. Kernel 1 (k1_fix_ascii_price.rs): Equivalence + Contract + Profile ==="
"$GNOMON" check-goal \
  --candidate "$SCRIPT_DIR/k1_fix_ascii_price.rs" --candidate-entry fix_parse_8_opt \
  --spec "$SCRIPT_DIR/k1_fix_ascii_price.rs" --spec-entry fix_parse_8_ref \
  --timeout-ms 20000
"$GNOMON" check-contract "$SCRIPT_DIR/k1_fix_ascii_price.rs" \
  --entry fix_parse_8_opt --ensures ens_fix_parse_8 --timeout-ms 10000
"$GNOMON" profile "$SCRIPT_DIR/k1_fix_ascii_price.rs" \
  --entry fix_parse_8_ref --compare "$SCRIPT_DIR/k1_fix_ascii_price.rs" --opt-entry fix_parse_8_opt \
  --targets x64,arm64 --bench --bench-preset ascii-digits

echo ""
echo "=== 4. Kernel 2 (k2_sor_venue_router.rs): Equivalence + Contract + Profile ==="
"$GNOMON" --state "$STATE_FILE" check-goal \
  --candidate "$SCRIPT_DIR/k2_sor_venue_router.rs" --candidate-entry sor_route_4_opt \
  --spec "$SCRIPT_DIR/k2_sor_venue_router.rs" --spec-entry sor_route_4_ref \
  --pre "$SCRIPT_DIR/k2_sor_venue_router.rs" --pre-entry req_sor \
  --timeout-ms 15000
"$GNOMON" --state "$STATE_FILE" check-contract "$SCRIPT_DIR/k2_sor_venue_router.rs" \
  --entry sor_route_4_opt --requires req_sor --ensures ens_sor --timeout-ms 10000
"$GNOMON" profile "$SCRIPT_DIR/k2_sor_venue_router.rs" \
  --entry sor_route_4_ref --compare "$SCRIPT_DIR/k2_sor_venue_router.rs" --opt-entry sor_route_4_opt \
  --targets x64,arm64 --bench \
  --bench-inputs '[[0,500,10000,15000,200,30,14995,400,20,15010,600,10,14990,350,25],[1,800,10000,15000,200,30,15020,400,20,15015,600,10,15025,350,25],[0,1000,10000,22450,150,15,22440,500,35,22460,900,5,22455,300,10],[1,250,10000,22450,150,15,22480,500,35,22470,900,5,22465,300,10]]'

echo ""
echo "=== 5. Kernel 3 (k3_oms_tick_risk_fastpath.rs): Equivalence + Contract + Profile ==="
"$GNOMON" --state "$STATE_FILE" check-goal \
  --candidate "$SCRIPT_DIR/k3_oms_tick_risk_fastpath.rs" --candidate-entry oms_tick_risk_opt \
  --spec "$SCRIPT_DIR/k3_oms_tick_risk_fastpath.rs" --spec-entry oms_tick_risk_ref \
  --pre "$SCRIPT_DIR/k3_oms_tick_risk_fastpath.rs" --pre-entry req_tick_risk \
  --timeout-ms 15000
"$GNOMON" --state "$STATE_FILE" check-contract "$SCRIPT_DIR/k3_oms_tick_risk_fastpath.rs" \
  --entry oms_tick_risk_opt --requires req_tick_risk --ensures ens_tick_risk --timeout-ms 10000
"$GNOMON" profile "$SCRIPT_DIR/k3_oms_tick_risk_fastpath.rs" \
  --entry oms_tick_risk_ref --compare "$SCRIPT_DIR/k3_oms_tick_risk_fastpath.rs" --opt-entry oms_tick_risk_opt \
  --targets x64,arm64 --bench \
  --bench-inputs '[[150123,500,150000,16,100000000,500,0],[150099,200,150000,8,100000000,500,0],[150500,900,150000,32,100000000,500,0],[150123,500,150000,16,100000000,500,1]]'

echo ""
echo "All 3 closed-loop kernels compiled (0 warnings), PROVED (equivalence + contracts), and profiled cleanly on x64 + ARM64!"
