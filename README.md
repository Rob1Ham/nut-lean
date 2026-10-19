# nut-lean — a Lean 4 model of basic Cashu mint accounting

The repository is `nut-lean`; the Lake package is named `cashu-lean`. It is a
small, zero-dependency Lean 4 project that models the accounting state machine
of a basic Cashu mint and proves that its solvency
inequality is preserved by minting, swapping, melting, and refunding. Earlier
increments added NUT-02 input-fee arithmetic and a fee-aware swap. This tree
also adds NUT-01/NUT-02 keyset metadata, V2 keyset-ID derivation, and a
mint-side proof-to-keyset binding without changing `Proof`.

It is a **formal model**, not a Cashu mint implementation. The
cryptography is abstract: signatures are opaque strings and no blind
signature, DLEQ, hash-to-curve, or secp256k1 operation is defined or proved.

## Build

Requires the Lean toolchain pinned in `lean-toolchain`
(`leanprover/lean4:v4.35.0`).

```bash
~/.elan/bin/lake build
./scripts/gate.sh
```

`scripts/gate.sh` builds the package, rejects `sorry`, `admit`,
`native_decide`, and `axiom` declarations in the Lean sources, and prints
`GATE OK`.

## What is modeled

The state (`CashuLean/Basic.lean`) records:

- `outstanding : List Proof` — spendable ecash the mint still owes;
- `spent : List Secret` — secrets that must not be spent again;
- `pending : List PendingMelt` — melts awaiting confirmation or refund;
- `reserve : Amount` — the mint's backing balance;
- `issued : Amount` — cumulative deposit-funded issuance;
- `keysets : List Keyset` — all known keysets, active and inactive;
- `activeKeyset : KeysetId` — the keyset used for new issuance;
- `proofKeyset : List (Secret × KeysetId)` — the mint-side issuing-keyset
  binding, kept as a side table so `Proof` remains `{amount, secret,
  signature}`.

`liability s` is the sum of the face values of `s.outstanding`.

The operations (`CashuLean/Mint.lean`, plus `CashuLean/Fees.lean` for the
fee-aware swap) are:

- `mint deposit outputs` — add the deposit to the reserve, issue outputs whose
  total does not exceed the deposit, and bind each output secret to the active
  keyset;
- `swap inputSecrets outputs` — remove known, unspent, keyset-bound inputs and
  issue active-keyset-supported outputs of exactly equal total face value. This
  path is fee-free and does **not** consult `feeForKeysets`;
- `swapWithFee inputSecrets outputs fee` — as `swap`, but outputs plus `fee`
  must equal the selected input total and `fee` must equal the keyset-derived
  fee; the fee stays in the reserve. This is the only path that enforces the
  keyset fee;
- `melt id inputSecrets` — burn known, unspent inputs, release reserve equal
  to their face value, and journal the melt;
- `refund id` — restore a journaled melt's proofs and reserve;
- `confirmMelt id` — drop a successful melt's journal entry.

Every operation returns `Except MintError MintState`.

The legacy single-keyset fee is
`feeFor ppk ps = (ps.length * ppk + 999) / 1000`. The keyset-aware form is
`feeForKeysets s ps`: it sums each proof's bound keyset's `input_fee_ppk` and
then ceiling-divides by 1000, returning `none` for an unbound proof or unknown
keyset. `feeForKeysets_eq_feeFor` proves the two agree when every input uses
one known keyset. Ordinary `swap` remains fee-free; only `swapWithFee` rejects
a fee that differs from `feeForKeysets`. A public API should choose one path;
do not expose the fee-free primitive as interchangeable with `swapWithFee`
when NUT-02 fees are required.

`keysetIdV2` hashes the V2 preimage: sorted public-key/amount pairs, the unit,
optional `input_fee_ppk`, and optional `final_expiry`. `Keyset.wellFormed`
requires ASCII-lowercase key/unit strings and a `|`-free unit; it is not a
general Unicode-canonicalization check. The preimage/ID checks use a
`ByteArray` view to avoid `Classical.choice`; the new keyset declarations and
invariants are checked with only `propext` and `Quot.sound`.

## What is proved

For every operation, if `s.reserve ≥ liability s` before the call and the
call succeeds, then `s'.reserve ≥ liability s'` afterwards:

```lean
Cashu.mint_preserves_solvency
Cashu.swap_preserves_solvency
Cashu.melt_preserves_solvency
Cashu.refund_preserves_solvency
Cashu.confirmMelt_preserves_solvency
Cashu.swapWithFee_preserves_solvency
```

The fee-aware swap additionally proves the exact liability equation
`Cashu.liability_swapWithFee : liability s' + fee = liability s`, together
with `feeFor_nil`, `feeFor_zero_ppk`, `feeFor_pos`, and monotonicity in `ppk`
and in the number of inputs. No face-value upper bound is claimed: the
statement `feeFor ppk ps ≤ sumProofs ps` is false for large `ppk`.

For the keyset increment, `Cashu.inputsBound_sound` says every accepted input
has a mint-side binding to a known keyset whose key map supports its amount.
`Cashu.feeForKeysets_eq_feeFor` is the single-keyset bridge above. The
invariants `KeysetInvariant` and `StateInvariant` extend the reachable-state
result with keyset-table shape, binding-table shape, a resolvable active
keyset, and binding coverage; all six operations preserve them. Details and
boundaries are summarized in "What this does NOT claim" below.

The proofs are kernel-checked and contain no `sorry` or `admit`. The list
accounting lemma `sumProofs_select_add_reject` is the shared workhorse.

The invariant is about spendable outstanding ecash. A melt moves proofs out
of `outstanding` and releases the same face value of reserve in one
transition; a refund reverses both. Pending-melt proofs are therefore not
counted in `liability`.

The accounting model accepts an empty mint output list, an empty no-op swap,
and duplicate input secrets. `selectBySecret` selects each outstanding proof
once, so duplicate secrets do not duplicate value, although `spent` may record
a secret more than once. None of these changes solvency; a production API
should reject degenerate requests or enforce distinct inputs if desired.

## What this does NOT claim

- It does **not** prove Cashu secure, private, or unlinkable.
- It does **not** model BDHKE, blind signatures, DLEQ proofs, SHA-256,
  hash-to-curve, or the secp256k1 group. See `docs/CRYPTO-LIMITS.md`.
- It does **not** implement NUT-00..05 wire formats, JSON, base64, HTTP, or
  error codes. It models the V2 keyset-ID preimage, but SHA-256 is a
  parameter and no hash implementation is provided.
- It does **not** model key rotation, multiple simultaneously active keysets,
  runtime enforcement of `idMatches`/`wellFormed`, a SHA-256 instance, change
  outputs (NUT-08), melt fees, quote accounting, persistence, concurrency,
  crashes, or the Lightning payment rail. Keyset-aware `feeForKeysets` is
  defined and enforced by `swapWithFee`; melt fees remain absent.
- It does **not** authenticate `refund` or `confirmMelt`. These are operator
  side transitions and do not observe Lightning payment status.
- It does **not** establish that a proof's keyset binding is cryptographic:
  `proofKeyset` is mint state, and `inputsBound_sound` reasons about that
  table, not about signatures.
- It does **not** validate proof signatures. A proof is trusted because its
  secret is in `outstanding`, which is mint-internal state.
- It is **not** audited and should not be used to operate a real mint.

## Layout

```
CashuLean.lean           root module
CashuLean/Basic.lean     types, keyset lookups, liabilities, list lemmas
CashuLean/Mint.lean      operations, keyset guards, solvency theorems
CashuLean/Fees.lean      NUT-02 fee arithmetic, fee-aware swap
CashuLean/Freshness.lean output-secret freshness predicates
CashuLean/Invariants.lean reachable-state and preservation invariants
CashuLean/Examples.lean  small executable examples
docs/CRYPTO-LIMITS.md    assumptions A1..A6
docs/PLAN.md             current scope and future work
scripts/gate.sh          build and proof-hole gate
```

## References

The model follows the vocabulary of the Cashu NUT specifications, especially
NUT-00 (notation and proofs), NUT-01/NUT-02 (keysets), NUT-03 (swap), NUT-04
(mint), and NUT-05 (melt). The NUT specifications are maintained at
`https://github.com/cashubtc/nuts`.

## License

MIT. See `LICENSE`.
