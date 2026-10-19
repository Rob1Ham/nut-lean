# Scope and roadmap

This document describes the current release and the work that remains outside
it. The formal model is deliberately smaller than a Cashu mint implementation:
it models accounting transitions and their invariants, not cryptography, wire
formats, or deployment behavior.

## Included in this release

- `Amount`, `Secret`, `Proof`, `Keyset`, `PendingMelt`, and `MintState`.
- `liability` as the sum of outstanding proof face values.
- `mint`, `swap`, `swapWithFee`, `melt`, `refund`, and `confirmMelt` with
  explicit failure results.
- Solvency preservation for every operation.
- NUT-02 input-fee arithmetic, including the keyset-aware fee and exact
  fee-aware swap.
- NUT-01/NUT-02 keyset metadata, a V2 keyset-ID preimage, and a mint-side
  proof-to-keyset binding.
- Output-freshness checks and reachable-state invariants.

## Outside the current release

- NUT-08 change outputs and melt-fee/quote accounting.
- Full pending-melt lifecycle, expiry, and exactly-once refund guarantees.
- NUT-07 proof-state queries and NUT-09 restore.
- NUT-00 token encodings, JSON/base64 transport, and error-code mapping.
- NUT-11 P2PK, NUT-12 DLEQ, and NUT-14 HTLC.
- BDHKE, blind signatures, SHA-256, hash-to-curve, and secp256k1.
- Key rotation and multiple simultaneously active keysets.
- Persistence, crash consistency, concurrency, database transactions, and the
  Lightning payment rail.
- Authentication, privacy, unlinkability, production key management, and side
  channels.
