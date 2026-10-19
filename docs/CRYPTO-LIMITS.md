# Cryptographic limits and assumptions

`nut-lean` proves accounting invariants. It does not formalize cryptography.
The assumptions below are **not** Lean axioms and are **not** used by any
proof. They are the external premises under which the accounting model would
correspond to a real Cashu mint. No proof in this repository establishes them.

## A1 — secp256k1 group arithmetic

The mint and wallets use the secp256k1 group with the standard generator `G`,
scalar field order `n`, point addition, and scalar multiplication. Group laws,
scalar arithmetic, and point encoding are assumed correct. The model contains
no curve, field, scalar, or point type.

## A2 — BDHKE blind-signature correctness

For a mint key `k`, public key `K = kG`, secret `x`, point `Y =
hash_to_curve(x)`, blinding factor `r`, blinded point `B_ = Y + rG`, and blind
signature `C_ = kB_`, unblinding gives `C = C_ - rK = kY`. Verification
accepts exactly when `C = k·hash_to_curve(x)`. The model stores a `Signature`
as an opaque `String` and never signs or verifies. A `Proof` is trusted only
because its secret is present in the mint's `outstanding` list.

## A3 — SHA-256 and hash-to-curve

`SHA256` is assumed collision- and preimage-resistant for the purposes used by
Cashu. `hash_to_curve` is assumed to be the NUT-00 construction with the
`Secp256k1_HashToCurve_Cashu_` domain separator and counter search. Neither
hash nor point decompression is implemented.

## A4 — DLEQ proofs

NUT-12 DLEQ proofs are assumed complete and sound: a wallet can check that the
mint used the same key for a blind signature as for its published public key.
DLEQ statements, challenges, and responses are not modeled.

## A5 — Keysets and identifiers

The state-level keyset table and proof-to-keyset binding are modeled:
`Keyset` carries `id`, `unit`, `active`, `inputFeePpk`, `finalExpiry`, and a
key map, while `MintState.proofKeyset` maps proof secrets to issuing keyset
ids. `Proof` itself still carries no keyset identifier.

What remains assumed is cryptographic and operational: the supplied hash is a
correct lowercase-hex SHA-256 implementation; published public keys really
belong to the mint; a signature verifies under the key bound to its secret;
keysets are provisioned and rotated correctly; and the mint state (including
`proofKeyset`) is authoritative. The V2 ID preimage is defined, but no
collision resistance, injectivity, key rotation, or real key management is
proved here.

Unit and public-key strings must be normalized to canonical lowercase before
derivation; `Keyset.wellFormed` enforces the ASCII subset of this at the state
layer, but the hash function itself hashes the supplied strings verbatim.
`final_expiry = 0` is omitted, a `|` in the unit is rejected only by
`wellFormed`, and `idMatches` is not enforced by mint/swap/melt operations.
These are boundary obligations, not proved conformance properties.

## A6 — Randomness, unforgeability, and unlinkability

Secrets and blinding factors are assumed to be generated with a CSPRNG.
Signatures are assumed unforgeable without the mint key, and the blind
signature flow is assumed to hide the link between issuance and redemption.
The Lean model is deterministic: it has no probability space, no adversary,
and no observational-equivalence notion, so it cannot state or prove
unlinkability.

## Consequence

`mint_preserves_solvency` and the other solvency theorems are accounting
statements. They can hold for a system whose signatures are forgeable, whose
secrets are predictable, or whose transport is insecure. They must not be read
as a security proof for Cashu or for any mint.
