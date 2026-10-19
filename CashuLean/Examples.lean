import CashuLean.Fees

/-!
# CashuLean.Examples

Small concrete checks that the accounting operations execute. The `#guard`
commands are evaluator-based build-time checks, not kernel proofs. These are
not cryptographic test vectors: signatures and secrets are arbitrary strings.
-/

namespace Cashu.Examples

/-- A V2-shaped keyset id for the executable examples. -/
def kid : KeysetId :=
  "010000000000000000000000000000000000000000000000000000000000000000"

/-- A compressed-key-shaped public key for the executable examples. -/
def pk : PubKey :=
  "020000000000000000000000000000000000000000000000000000000000000000"

def ks : Keyset :=
  { id := kid, unit := "sat", active := true, inputFeePpk := 0
    finalExpiry := none
    keys := [(1, pk), (2, pk), (4, pk), (5, pk), (6, pk), (10, pk)] }

def proof (amount : Amount) (secret : Secret) : Proof :=
  { amount := amount, secret := secret, signature := "sig:" ++ secret }

def empty : MintState :=
  { outstanding := []
    spent := []
    pending := []
    reserve := 0
    issued := 0
    keysets := [ks]
    activeKeyset := kid
    proofKeyset := [] }

def ok : Except MintError MintState → Bool
  | .ok _ => true
  | .error _ => false

def opened : MintState :=
  { empty with
    outstanding := [proof 4 "a", proof 6 "b"]
    reserve := 10
    issued := 10
    proofKeyset := [("a", kid), ("b", kid)] }

-- A deposit must cover the output total.
#guard mintValid empty 10 [proof 4 "a", proof 6 "b"]
#guard !mintValid empty 9 [proof 4 "a", proof 6 "b"]

def afterMelt : MintState :=
  { opened with
    outstanding := [proof 6 "b"]
    spent := ["a"]
    pending := [{ id := 7, proofs := [proof 4 "a"] }]
    reserve := 6 }

-- Minting, melting one proof, and refunding it all execute.
#guard ok (mint empty 10 [proof 4 "a", proof 6 "b"])
#guard ok (melt opened 7 ["a"])
#guard ok (refund afterMelt 7)

-- Mint-bound outputs are spendable, and swap-bound outputs are too.
def minted : MintState :=
  match mint empty 10 [proof 4 "m", proof 6 "n"] with
  | .ok s => s
  | .error _ => empty

#guard inputsBound minted ["m", "n"]
#guard ok (swap minted ["m", "n"] [proof 5 "p", proof 5 "q"])

def swapped : MintState :=
  match swap minted ["m", "n"] [proof 5 "p", proof 5 "q"] with
  | .ok s => s
  | .error _ => empty

#guard inputsBound swapped ["p", "q"]

-- The binding is append-only, so a refunded proof remains spendable.
def refunded : MintState :=
  match refund afterMelt 7 with
  | .ok s => s
  | .error _ => empty

#guard inputsBound refunded ["a"]

-- A swap must conserve value and cannot touch a spent secret.
#guard swapValid opened ["a", "b"] [proof 5 "c", proof 5 "d"]
#guard !swapValid opened ["a", "b"] [proof 5 "c"]
#guard !swapValid { opened with spent := ["a"] } ["a"] [proof 4 "c"]

-- Boundary paths accepted by the accounting model: an empty mint, an empty
-- no-op swap, and duplicate input secrets. None changes solvency; a production
-- API may reject them separately.
#guard mintValid empty 0 []
#guard swapValid opened [] []
#guard swapValid opened ["a", "a"] [proof 4 "d"]

-- A proof with an outstanding secret but no mint-side binding is rejected.
def unbound : MintState :=
  { opened with outstanding := [proof 4 "c"] }

#guard !swapValid unbound ["c"] [proof 4 "d"]
#guard !meltValid unbound 8 ["c"]
#guard feeForKeysets unbound [proof 4 "c"] = none

-- A binding to a known keyset whose key map lacks the proof's amount is
-- rejected (amount 3 is absent from `ks.keys`).
def missingAmount : MintState :=
  { empty with outstanding := [proof 3 "z"], proofKeyset := [("z", kid)] }

#guard !swapValid missingAmount ["z"] [proof 3 "y"]
#guard !meltValid missingAmount 8 ["z"]

-- A zero-fee keyset is charged zero; a nonzero-fee keyset uses the ceiling.
#guard feeForKeysets opened [proof 4 "a", proof 6 "b"] = some 0
#guard feeFor (0 : Nat) [proof 4 "a", proof 6 "b"] = 0

def feeKs : Keyset := { ks with inputFeePpk := 100 }
def feeState : MintState :=
  { empty with
    keysets := [feeKs],
    outstanding := [proof 4 "a"],
    proofKeyset := [("a", kid)] }

#guard feeForKeysets feeState [proof 4 "a"] = some 1
#guard feeFor 100 [proof 4 "a"] = 1

-- A fee-aware swap checks the derived fee, issues the outputs, and binds them.
def feeOpened : MintState :=
  { empty with
    keysets := [feeKs],
    outstanding := [proof 6 "f"],
    reserve := 6,
    proofKeyset := [("f", kid)] }

#guard feeForKeysets feeOpened [proof 6 "f"] =
  some (feeFor feeKs.inputFeePpk [proof 6 "f"])
#guard ok (swapWithFee feeOpened ["f"] [proof 5 "g"] 1)

def feeSwapped : MintState :=
  match swapWithFee feeOpened ["f"] [proof 5 "g"] 1 with
  | .ok s => s
  | .error _ => empty

#guard inputsBound feeSwapped ["g"]

-- The V2 preimage: sorted by amount, canonical lowercase unit/pubkeys, and
-- optional fields. Normalization is a boundary obligation: the preimage
-- hashes the supplied strings verbatim.
def preimageKs : Keyset :=
  { id := kid, unit := "sat", active := true, inputFeePpk := 100,
    finalExpiry := some 99, keys := [(2, pk), (1, pk)] }

#guard keysetIdPreimage preimageKs =
  "1:" ++ pk ++ ",2:" ++ pk ++ "|unit:sat|input_fee_ppk:100|final_expiry:99"

-- Zero fee and absent/zero final expiry are omitted from the preimage.
#guard keysetIdPreimage
    { preimageKs with inputFeePpk := 0, finalExpiry := none } =
  "1:" ++ pk ++ ",2:" ++ pk ++ "|unit:sat"
#guard keysetIdPreimage
    { preimageKs with inputFeePpk := 0, finalExpiry := some 0 } =
  "1:" ++ pk ++ ",2:" ++ pk ++ "|unit:sat"

-- `active` is not part of the preimage, so it does not change the id.
example : keysetIdV2 (fun _ => pk) { ks with active := false } =
    keysetIdV2 (fun _ => pk) ks := rfl

-- The `01` prefix is added after the hash (the stub returns 64 characters).
def stubHash : String → String :=
  fun _ =>
    "0000000000000000000000000000000000000000000000000000000000000000"

#guard (keysetIdV2 stubHash ks).toByteArray.size == 66

-- The solvency statement is invoked on a concrete state; the general theorem
-- lives in `CashuLean.Mint`.
example : liability opened = 10 := by decide

end Cashu.Examples
