/-!
# CashuLean.Basic

The data model for the basic Cashu mint accounting core.

This file contains **no cryptography**. `Signature` is an opaque byte string;
proofs are records whose signatures are stored and moved around but never
checked here. See `docs/CRYPTO-LIMITS.md` for the explicit assumptions.

The model follows the vocabulary of NUT-00 (`Proof`), NUT-01/NUT-02
(`Keyset`), NUT-03 (`swap`), NUT-04 (`mint`), and NUT-05 (`melt`).

Amounts are natural numbers in the mint's smallest unit (normally sat). The
model deliberately has no maximum-supply constant and no signed arithmetic:
all accounting quantities are non-negative and subtraction is Lean's
truncating `Nat.sub`.
-/

namespace Cashu

/-- A non-negative amount in the mint's unit. -/
abbrev Amount := Nat

/-- The secret message `x` in a Cashu proof (NUT-00). -/
abbrev Secret := String

/-- An opaque blind/unblinded signature encoding (NUT-00). No cryptographic
meaning is assigned to this type in the model. -/
abbrev Signature := String

/-- NUT-02 keyset ID in wire form: 33 bytes = 66 lowercase hex characters,
with a two-hex-character version prefix (`01` for V2). -/
abbrev KeysetId := String

/-- A compressed secp256k1 public key in wire form: 33 bytes = 66 lowercase
hex characters, prefix `02` or `03`. -/
abbrev PubKey := String

/-- A Cashu `Proof` (NUT-00): an amount, the secret message, and the mint's
unblinded signature on that secret. The signature is carried opaquely. -/
structure Proof where
  amount : Amount
  secret : Secret
  signature : Signature
  deriving Repr, DecidableEq

/-- Byte `i` of a string as a `UInt8`, or `0` if out of bounds. This indexed
view is used for wire-shape checks because `String.length`, `String.toList`,
and `String.toLower` depend on `Classical.choice` in the current Lean library.
`String.toByteArray`, `ByteArray.size`, and `ByteArray.get` do not, and the
indexed form reduces under `decide` for concrete strings. -/
def byteAt (s : String) (i : Nat) : UInt8 :=
  if h : i < s.toByteArray.size then s.toByteArray.get i h else 0

/-- Does every byte of `s` satisfy `p`? -/
def allBytes (s : String) (p : UInt8 → Bool) : Bool :=
  (List.range s.toByteArray.size).all (fun i => p (byteAt s i))

/-- A computable prefix test on UTF-8 bytes. -/
def hasBytePrefix (s : String) (p : List Nat) : Bool :=
  if p.length ≤ s.toByteArray.size then
    (List.range p.length).all (fun i => (byteAt s i).toNat == p.getD i 0)
  else false

/-- Does a string contain a given byte value? -/
def bytesContains (s : String) (n : Nat) : Bool :=
  (List.range s.toByteArray.size).any (fun i => (byteAt s i).toNat == n)

/-- An ASCII lowercase hexadecimal byte. -/
def isLowerHexByte (n : Nat) : Bool :=
  (48 ≤ n && n ≤ 57) || (97 ≤ n && n ≤ 102)

/-- The NUT-02 V2 wire shape: 66 lowercase hex bytes beginning `01`. -/
def isV2Id (s : String) : Bool :=
  s.toByteArray.size = 66 &&
    hasBytePrefix s [48, 49] &&
    allBytes s (fun b => isLowerHexByte b.toNat)

/-- The NUT-01 compressed public-key wire shape: 66 lowercase hex bytes
beginning `02` or `03`. -/
def isCompressedPubKey (s : String) : Bool :=
  s.toByteArray.size = 66 &&
    (hasBytePrefix s [48, 50] || hasBytePrefix s [48, 51]) &&
    allBytes s (fun b => isLowerHexByte b.toNat)

/-- A computable ASCII lowercase test: no byte is in `A`–`Z`. This is the
same alphabetical range normalized by `String.toLower`; non-ASCII bytes are
left to the caller's normalization policy. -/
def isLowerString (s : String) : Bool :=
  allBytes s (fun b => b.toNat < 65 || b.toNat > 90)

/-- Mint-side relation: secret → issuing keyset id. Append-only in this
design, so a refund never has to reconstruct a binding. -/
abbrev ProofKeyset := List (Secret × KeysetId)

namespace ProofKeyset

/-- The issuing keyset bound to `x`, or `none` if the mint has no binding. -/
def lookup (t : ProofKeyset) (x : Secret) : Option KeysetId :=
  (t.find? (fun e => e.1 == x)).map (fun e => e.2)

/-- A binding table is well formed when its secrets are distinct and every
identifier has the NUT-02 V2 wire shape. -/
def wellFormed (t : ProofKeyset) : Prop :=
  (t.map Prod.fst).Nodup ∧
  ∀ e ∈ t, isV2Id e.2 = true

end ProofKeyset

/-- Keyset metadata and key material (NUT-01/NUT-02). `inputFeePpk` is the
per-input fee; `active` controls whether the keyset may issue new outputs.
`finalExpiry` and `keys` are NUT-01/NUT-02 metadata and are not part of the
wave-0 accounting functions. -/
structure Keyset where
  id : KeysetId
  unit : String
  active : Bool
  inputFeePpk : Nat
  finalExpiry : Option Nat := none
  keys : List (Amount × PubKey) := []
  deriving Repr, DecidableEq

/-- Exact NUT-02 V2 preimage: sorted `amount:pubkey` pairs joined by `,`,
then `|unit:U`, optional `|input_fee_ppk:P`, optional
`|final_expiry:E`. The `01` version prefix is not part of the preimage.

The public keys and unit are hashed **as supplied**. They are expected to be
canonical lowercase strings, which `Keyset.wellFormed` enforces. Normalization
is therefore a boundary obligation, not hidden inside this function; this is
what lets the derivation avoid the `Classical.choice` dependency of
`String.toLower` while agreeing with the spec on every well-formed keyset. -/
def keysetIdPreimage (k : Keyset) : String :=
  String.intercalate ","
      ((k.keys.mergeSort (fun a b => a.1 ≤ b.1)).map
        (fun e => toString e.1 ++ ":" ++ e.2))
    ++ "|unit:" ++ k.unit
    ++ (if k.inputFeePpk = 0 then ""
        else "|input_fee_ppk:" ++ toString k.inputFeePpk)
    ++ (match k.finalExpiry with
        | none => ""
        | some 0 => ""
        | some t => "|final_expiry:" ++ toString t)

/-- NUT-02 V2 keyset ID. `hash` must implement UTF-8 encoding, SHA-256, and
lowercase hex; it is a parameter so the model does not axiomatize SHA-256.
The `01` version prefix is prepended after hashing. -/
def keysetIdV2 (hash : String → String) (k : Keyset) : KeysetId :=
  "01" ++ hash (keysetIdPreimage k)

/-- `active` is mutable metadata and is not part of the V2 preimage, so it does
not affect the derived id. -/
theorem keysetIdV2_active_irrelevant (hash : String → String) (k : Keyset)
    (b : Bool) :
    keysetIdV2 hash { k with active := b } = keysetIdV2 hash k := rfl

namespace Keyset

/-- Shape and metadata well-formedness. This is a predicate, not a type
invariant: a hand-constructed `MintState` can contain a malformed keyset.
The unit and public keys must already be canonical lowercase strings; the ID
derivation hashes them verbatim. -/
def wellFormed (k : Keyset) : Prop :=
  isV2Id k.id = true ∧
  isLowerString k.unit = true ∧
  bytesContains k.unit 124 = false ∧
  (k.keys.map Prod.fst).Nodup ∧
  (∀ e ∈ k.keys, e.1 > 0 ∧ isCompressedPubKey e.2 = true) ∧
  (∀ t, k.finalExpiry = some t → t > 0)

/-- The id is the V2 derivation of the key map and metadata. This is the
wallet-side check NUT-02 recommends; the mint state is assumed to satisfy it. -/
def idMatches (hash : String → String) (k : Keyset) : Prop :=
  k.id = keysetIdV2 hash k

end Keyset

/-- A melt that has been optimistically settled and is awaiting confirmation.

`amount` is derived from the proofs, not stored separately: a melt releases
exactly the face value of the proofs it burns. This is the no-fee wave-0
model. A `refund` restores the same proofs and the same reserve amount. -/
structure PendingMelt where
  id : Nat
  proofs : List Proof
  deriving Repr, DecidableEq

namespace PendingMelt

/-- The secrets carried by a pending melt. -/
def secrets (m : PendingMelt) : List Secret :=
  m.proofs.map (fun p => p.secret)

/-- The reserve amount released by a pending melt: the face value of its
proofs. -/
def amount (m : PendingMelt) : Amount :=
  (m.proofs.map (fun p => p.amount)).sum

end PendingMelt

/-- The mint's accounting state.

* `outstanding` — proofs the mint still owes to holders; this is the
  liability the solvency theorems talk about.
* `spent` — secrets that have been spent and must never be accepted again.
* `pending` — optimistically settled melts awaiting `confirmMelt` or
  `refund`; their proofs have already left `outstanding`.
* `reserve` — the mint's backing balance in the same unit.
* `issued` — cumulative face value issued by `mint` (deposit-funded
  issuance). Swaps and melts do not change it.
* `keysets` — all known keysets, active and inactive.
* `activeKeyset` — the keyset used for new issuance.
* `proofKeyset` — mint-side relation from a proof secret to its issuing
  keyset. Append-only; `Proof` itself is deliberately unchanged.
-/
structure MintState where
  outstanding : List Proof
  spent : List Secret
  pending : List PendingMelt
  reserve : Amount
  issued : Amount
  keysets : List Keyset
  activeKeyset : KeysetId
  proofKeyset : ProofKeyset
  deriving Repr, DecidableEq

/-- Total face value of a list of proofs. -/
def sumProofs (ps : List Proof) : Amount :=
  (ps.map (fun p => p.amount)).sum

/-- The mint's liability: the total face value of spendable outstanding
proofs. Pending-melt proofs are intentionally excluded. -/
def liability (s : MintState) : Amount :=
  sumProofs s.outstanding

/-- All secrets currently locked by pending melts. -/
def MintState.pendingSecrets (s : MintState) : List Secret :=
  s.pending.flatMap PendingMelt.secrets

/-- Boolean list membership for secrets. -/
def contains (xs : List Secret) (x : Secret) : Bool :=
  xs.any (fun y => y == x)

/-- Proofs whose secret occurs in `secrets`. -/
def selectBySecret (ps : List Proof) (secrets : List Secret) : List Proof :=
  ps.filter (fun p => contains secrets p.secret)

/-- Proofs whose secret does not occur in `secrets`. -/
def rejectBySecret (ps : List Proof) (secrets : List Secret) : List Proof :=
  ps.filter (fun p => !contains secrets p.secret)

/-! ## Keyset lookups and keyset-aware guards -/

/-- Look up a keyset by its wire id. -/
def keysetOf? (s : MintState) (kid : KeysetId) : Option Keyset :=
  s.keysets.find? (fun k => k.id == kid)

/-- The active issuance keyset, if the pointer resolves. -/
def activeKeyset? (s : MintState) : Option Keyset :=
  keysetOf? s s.activeKeyset

/-- The bindings created by issuing `ps` from keyset `kid`. -/
def issuedBindings (kid : KeysetId) (ps : List Proof) : ProofKeyset :=
  ps.map (fun p => (p.secret, kid))

/-- The issuing keyset bound to `p.secret`, or `none` if unbound. -/
def proofKeyset? (s : MintState) (p : Proof) : Option KeysetId :=
  s.proofKeyset.lookup p.secret

/-- The binding table is well formed and refers only to known keysets. -/
def MintState.bindingsWellFormed (s : MintState) : Prop :=
  s.proofKeyset.wellFormed ∧
  ∀ e ∈ s.proofKeyset, ∃ k ∈ s.keysets, e.2 = k.id

/-- The keyset table has distinct ids and every entry is well formed. -/
def MintState.keysetsWellFormed (s : MintState) : Prop :=
  (s.keysets.map (fun k => k.id)).Nodup ∧
  ∀ k ∈ s.keysets, k.wellFormed

/-- Keyset-aware input validation. Fail-closed: an unbound proof, an id absent
from `s.keysets`, or an amount absent from the key map all return `false`.
Inactive keysets are allowed for inputs, as NUT-02 requires. -/
def inputsBound (s : MintState) (secrets : List Secret) : Bool :=
  (selectBySecret s.outstanding secrets).all (fun p =>
    match proofKeyset? s p with
    | none => false
    | some kid =>
        match keysetOf? s kid with
        | none => false
        | some k => k.keys.any (fun e => e.1 == p.amount))

/-- Output validation: the active issuance keyset exists, is active, and its
key map supports every output amount. -/
def outputsValid (s : MintState) (outputs : List Proof) : Bool :=
  match activeKeyset? s with
  | none => false
  | some k =>
      k.active && outputs.all (fun p => k.keys.any (fun e => e.1 == p.amount))

/-- The NUT-03 value equation, factored out of `swapValid`. -/
def swapValueOK (s : MintState) (secrets : List Secret)
    (outputs : List Proof) : Bool :=
  sumProofs outputs == sumProofs (selectBySecret s.outstanding secrets)

/-- The propositional form of the swap value equation. -/
theorem swapValueOK_eq {s : MintState} {secrets : List Secret}
    {outputs : List Proof} (h : swapValueOK s secrets outputs = true) :
    sumProofs outputs = sumProofs (selectBySecret s.outstanding secrets) :=
  beq_iff_eq.mp h

/-- Keyset-aware input validation is sound: every selected input has a
mint-side binding to a known keyset whose key map contains its amount. -/
theorem inputsBound_sound (s : MintState) (secrets : List Secret)
    (h : inputsBound s secrets = true) :
    ∀ p ∈ selectBySecret s.outstanding secrets,
      ∃ k ∈ s.keysets,
        proofKeyset? s p = some k.id ∧
        k.keys.any (fun e => e.1 == p.amount) = true := by
  intro p hp
  have h' := (List.all_eq_true.mp h) p hp
  cases hpk : proofKeyset? s p with
  | none => simp [hpk] at h'
  | some kid =>
      cases hk : keysetOf? s kid with
      | none => simp [hpk, hk] at h'
      | some k =>
          have hkey : k.keys.any (fun e => e.1 == p.amount) = true := by
            simpa [hpk, hk] using h'
          unfold keysetOf? at hk
          have hkmem : k ∈ s.keysets :=
            List.mem_of_find?_eq_some (p := fun j : Keyset => j.id == kid) hk
          have hkid : k.id = kid :=
            beq_iff_eq.mp
              (List.find?_some (p := fun j : Keyset => j.id == kid) hk)
          exact ⟨k, hkmem, by rw [hkid], hkey⟩

/-! ## List accounting lemmas -/

/-- A list split by any Boolean predicate has additive face-value accounting. -/
theorem sumProofs_filter_add_filter_not (ps : List Proof) (pred : Proof → Bool) :
    sumProofs (ps.filter pred) + sumProofs (ps.filter (fun p => !pred p)) =
      sumProofs ps := by
  induction ps with
  | nil => simp [sumProofs]
  | cons p ps ih =>
      cases hp : pred p with
      | true =>
          simp only [List.filter, hp, Bool.not_true, sumProofs, List.map_cons,
            List.sum_cons] at ih ⊢
          calc
            p.amount +
                (List.map (fun p => p.amount) (List.filter pred ps)).sum +
                (List.map (fun p => p.amount)
                  (List.filter (fun p => !pred p) ps)).sum
                = p.amount +
                  ((List.map (fun p => p.amount) (List.filter pred ps)).sum +
                   (List.map (fun p => p.amount)
                     (List.filter (fun p => !pred p) ps)).sum) := by
                    ac_rfl
            _ = p.amount + (List.map (fun p => p.amount) ps).sum := by
                    rw [ih]
      | false =>
          simp only [List.filter, hp, Bool.not_false, sumProofs, List.map_cons,
            List.sum_cons] at ih ⊢
          calc
            (List.map (fun p => p.amount) (List.filter pred ps)).sum +
                (p.amount +
                 (List.map (fun p => p.amount)
                   (List.filter (fun p => !pred p) ps)).sum)
                = p.amount +
                  ((List.map (fun p => p.amount) (List.filter pred ps)).sum +
                   (List.map (fun p => p.amount)
                     (List.filter (fun p => !pred p) ps)).sum) := by
                    ac_rfl
            _ = p.amount + (List.map (fun p => p.amount) ps).sum := by
                    rw [ih]

/-- Selecting and rejecting the same secrets partitions the face value of a
proof list. -/
theorem sumProofs_select_add_reject (ps : List Proof) (secrets : List Secret) :
    sumProofs (selectBySecret ps secrets) +
      sumProofs (rejectBySecret ps secrets) = sumProofs ps := by
  exact sumProofs_filter_add_filter_not ps (fun p => contains secrets p.secret)

/-- Face value is additive under list append. -/
theorem sumProofs_append (a b : List Proof) :
    sumProofs (a ++ b) = sumProofs a + sumProofs b := by
  simp [sumProofs, List.map_append, List.sum_append]

end Cashu
