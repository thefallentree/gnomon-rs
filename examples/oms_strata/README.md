# OMS Strata Fixtures (Step 1a)

Strict `#![no_std]` Rust fixtures targeting `wasm32-unknown-unknown` for **Gnomon Step 1a** (`gnomon check-contract`: preconditions/postconditions, inductive state invariants, and inline `gnomon_assume` / `gnomon_assert`).

All modules avoid raw-pointer `unsafe` and shadow-stack spills (`__stack_pointer`):
- `s1_1_notional_collar.rs` has zero `unsafe` blocks and zero FFI imports.
- `s3_1_child_fsm.rs` and `s3_1_child_fsm_buggy.rs` store order state in fixed linear-memory `AtomicI32`/`AtomicI64` (`Ordering::Relaxed`) slots (`globals: 0` in lifted Wasm) and confine `unsafe` strictly to the `#[link(wasm_import_module = "gnomon")]` FFI declarations for `gnomon_assume` and `gnomon_assert`.

## Build & Lift Verification

```bash
./build.sh
```

Outputs are written to `out/` (git-ignored) and every compiled `.wasm` is checked with `gnomon lift --emit-wasm` for 100% clean lifting and round-trip validity.

## Fixtures & Exported Contracts

### 1. `S1.1` — Checked Notional & Price Collar ([`s1_1_notional_collar.rs`](s1_1_notional_collar.rs))

| Exported Function | Signature | Role |
| --- | --- | --- |
| `checked_notional` | `(price: i64, qty: i64, max_notional: i64) -> i32` | Safe overflow-free notional cap check (`price > 0 && qty > 0 && max_notional > 0 && price * qty <= max_notional`). |
| `req_notional` | `(price: i64, qty: i64, max_notional: i64) -> i32` | Precondition (`max_notional > 0`; `price` and `qty` unconstrained). |
| `ens_notional` | `(price: i64, qty: i64, max_notional: i64, ret: i32) -> i32` | Relational postcondition verifying exact cap bound and zero 64-bit wraparound. |
| `checked_notional_buggy_overflow` | `(price: i64, qty: i64, max_notional: i64) -> i32` | **Buggy mutant:** naive `price.wrapping_mul(qty) <= max_notional` (64-bit signed wraparound bypass). |
| `price_collar_ok` | `(price: i64, ref_price: i64, collar_bps: i64) -> i32` | Safe overflow-free 128-bit widening collar check (`|price - ref_price| * 10_000 <= ref_price * collar_bps`). |
| `req_price_collar` | `(price: i64, ref_price: i64, collar_bps: i64) -> i32` | Precondition (`0 <= collar_bps <= 10_000`; `price` and `ref_price` unconstrained). |
| `ens_price_collar` | `(price: i64, ref_price: i64, collar_bps: i64, ret: i32) -> i32` | Relational postcondition verifying exact collar semantics and non-positive rejection. |
| `price_collar_buggy_div0` | `(price: i64, ref_price: i64, collar_bps: i64) -> i32` | **Buggy mutant:** traps on `ref_price == 0`. |
| `price_collar_buggy_overflow` | `(price: i64, ref_price: i64, collar_bps: i64) -> i32` | **Buggy mutant:** 64-bit wraparound on large `price` bypasses collar. |

### 2. `S3.1` — Child Order Lifecycle FSM ([`s3_1_child_fsm.rs`](s3_1_child_fsm.rs))

States: `0=Empty`, `1=PendingNew`, `2=Live`, `3=PendingReplace`, `4=PendingCancel`, `5=Filled`, `6=Canceled`, `7=Rejected`.
Fields: `state: i32`, `orig_qty: i64`, `leaves_qty: i64`, `cum_filled: i64`, `pending_qty: i64` (pending replacement leaves while `PendingReplace`), `worst_case_leaves: i64`.

| Exported Function | Signature | Role |
| --- | --- | --- |
| `init_empty` | `()` | Establishes `inv_child_fsm()` from initial state (`use_initial_state = true`). |
| `submit_new` | `(qty: i64) -> i32` | `Empty -> PendingNew` (`qty > 0`). |
| `on_ack` | `() -> i32` | `PendingNew -> Live`. |
| `request_cancel` | `() -> i32` | `Live -> PendingCancel` (preserves `worst_case_leaves == leaves_qty`). |
| `request_replace` | `(new_total_qty: i64) -> i32` | `Live -> PendingReplace` (`worst_case_leaves = max(leaves_qty, new_leaves)`). |
| `on_fill` | `(fill_qty: i64) -> i32` | Valid in `Live \| PendingCancel \| PendingReplace`; never drops fills during `PendingCancel`. |
| `on_cancel_ack` | `() -> i32` | Valid in `PendingCancel \| Live`; preserves `cum_filled`, never modifies terminal states. |
| `on_replace_ack` | `() -> i32` | `PendingReplace -> Live \| Filled`; commits `leaves_qty` and `worst_case_leaves`. |
| `on_reject` | `() -> i32` | `PendingNew -> Rejected`, or `PendingCancel \| PendingReplace -> Live`. |
| `inv_child_fsm` | `() -> i32` | Full inductive state invariant over all 8 states and 6 fields. |
| `contract_fill_during_pending_cancel` | `(fill_qty: i64) -> i32` | Inline `gnomon_assume`/`gnomon_assert` relational proof for fills during `PendingCancel`. |
| `contract_no_terminal_resurrection` | `(evt: i32, arg: i64) -> i32` | Inline relational proof that no event mutates any terminal state. |
| `contract_replace_pessimistic_exposure` | `(new_total_qty: i64) -> i32` | Inline relational proof that `request_replace` never shrinks `worst_case_leaves` prematurely. |

### 3. `S3.1` Buggy Mutants ([`s3_1_child_fsm_buggy.rs`](s3_1_child_fsm_buggy.rs))

| Exported Mutant / Harness | Signature | Bug Demonstrated |
| --- | --- | --- |
| `on_fill_buggy_drops_pending_cancel` | `(fill_qty: i64) -> i32` | Drops fills while `PendingCancel` ("phantom flat"). |
| `on_cancel_ack_buggy_resurrects_or_overwrites_filled` | `() -> i32` | Overwrites terminal `Filled` with `Canceled`. |
| `request_replace_buggy_optimistic_leaves` | `(new_total_qty: i64) -> i32` | Optimistically shrinks `worst_case_leaves` before exchange ack (violates `inv_child_fsm()`). |
| `contract_fill_during_pending_cancel_buggy` | `(fill_qty: i64) -> i32` | Fails inline assertion on Mutant 1 (`FALSIFIED`). |
| `contract_no_terminal_resurrection_buggy` | `(evt: i32, arg: i64) -> i32` | Fails inline assertion on Mutant 2 (`FALSIFIED`). |
| `contract_replace_pessimistic_exposure_buggy` | `(new_total_qty: i64) -> i32` | Fails inline assertion on Mutant 3 (`FALSIFIED`). |
