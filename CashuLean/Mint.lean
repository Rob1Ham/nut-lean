import CashuLean.Freshness

/-!
# CashuLean.Mint

Executable accounting operations for a basic Cashu mint, plus the solvency
theorems.

The operations use `Except MintError` for failure. Validation is deliberately
coarse in wave 0: each operation has one `invalid...` error constructor rather
than the NUT error-code taxonomy. The important property is that no operation
can increase the mint's liability by more than the value it receives.

Fees, change outputs (NUT-08), signature verification, key rotation, and
persistence are out of scope.
-/

namespace Cashu

/-- Wave-0 operation failures. Coarse on purpose; NUT error codes are not
modeled yet. -/
inductive MintError where
  | invalidMint
  | invalidSwap
  | invalidMelt
  | noSuchMelt
  deriving Repr, DecidableEq

/-- Every proof carries a positive face value. Zero-value proofs are rejected
by `mint` and `swap`. -/
def allPositive (ps : List Proof) : Bool :=
  ps.all (fun p => p.amount > 0)

/-- Every supplied secret is present in the mint's outstanding set. -/
def allKnown (s : MintState) (secrets : List Secret) : Bool :=
  secrets.all (fun x => contains (s.outstanding.map (fun p => p.secret)) x)

/-- No supplied secret has already been spent. -/
def noneSpent (s : MintState) (secrets : List Secret) : Bool :=
  secrets.all (fun x => !contains s.spent x)

/-- No supplied secret is locked in a pending melt. -/
def nonePending (s : MintState) (secrets : List Secret) : Bool :=
  secrets.all (fun x => !contains s.pendingSecrets x)

/-! ## Mint (NUT-04) -/

/-- A mint request is valid when the active issuance keyset supports every
output amount, outputs are positive, the output total does not exceed the
deposit, and the output secrets are fresh (see `CashuLean.Freshness`).

`mintValid` has no proof inputs: a deposit is not a list of Cashu proofs, so
the keyset-aware input guard is on `swapValid` and `meltValid`. -/
def mintValid (s : MintState) (deposit : Amount) (outputs : List Proof) : Bool :=
  outputsValid s outputs && allPositive outputs &&
    (sumProofs outputs ≤ deposit) && outputsFresh s outputs

/-- The freshness clause of `mintValid`. -/
theorem mintValid_outputsFresh {s : MintState} {deposit : Amount}
    {outputs : List Proof} (h : mintValid s deposit outputs = true) :
    outputsFresh s outputs = true := by
  simp [mintValid] at h
  exact h.2

/-- The value clause of `mintValid`. -/
theorem mintValid_valueLe {s : MintState} {deposit : Amount}
    {outputs : List Proof} (h : mintValid s deposit outputs = true) :
    sumProofs outputs ≤ deposit := by
  simp [mintValid] at h
  exact h.1.2

/-- Deposit `deposit` and issue `outputs`.

The reserve grows by the full deposit; outstanding proofs grow by the output
total. If the output total is smaller than the deposit, the difference remains
in the reserve. Signatures are carried opaquely and are not checked. -/
def mint (s : MintState) (deposit : Amount) (outputs : List Proof) :
    Except MintError MintState :=
  if mintValid s deposit outputs then
    .ok { s with
      outstanding := s.outstanding ++ outputs
      reserve := s.reserve + deposit
      issued := s.issued + sumProofs outputs
      proofKeyset := issuedBindings s.activeKeyset outputs ++ s.proofKeyset }
  else .error .invalidMint

/-- **Solvency is preserved by minting.** If the reserve covered outstanding
liability before, and the minted output total does not exceed the deposit, the
reserve covers the enlarged outstanding set afterwards. -/
theorem mint_preserves_solvency (s : MintState) (deposit : Amount)
    (outputs : List Proof) (s' : MintState)
    (hm : mint s deposit outputs = .ok s')
    (hs : s.reserve ≥ liability s) :
    s'.reserve ≥ liability s' := by
  unfold mint at hm
  split at hm
  · rename_i hvalid
    injection hm with hstate
    subst s'
    have hv := hvalid
    simp [mintValid] at hv
    have hdep : sumProofs outputs ≤ deposit := hv.1.2
    dsimp only [liability, sumProofs] at hs hdep ⊢
    rw [List.map_append, List.sum_append]
    exact Nat.add_le_add hs hdep
  · contradiction

/-! ## Swap (NUT-03) -/

/-- A swap is valid when all inputs are known, unspent, and not pending; the
mint holds a keyset binding for each selected input; the active keyset supports
every output amount; outputs are positive and fresh; and the output total
equals the face value of the selected inputs. -/
def swapValid (s : MintState) (secrets : List Secret)
    (outputs : List Proof) : Bool :=
  allKnown s secrets && noneSpent s secrets && nonePending s secrets &&
    inputsBound s secrets && outputsValid s outputs &&
    allPositive outputs && swapValueOK s secrets outputs &&
    outputsFresh s outputs

/-- The freshness clause of `swapValid`. -/
theorem swapValid_outputsFresh {s : MintState} {secrets : List Secret}
    {outputs : List Proof} (h : swapValid s secrets outputs = true) :
    outputsFresh s outputs = true := by
  simp [swapValid] at h
  exact h.2

/-- The known-input clause of `swapValid`. -/
theorem swapValid_allKnown {s : MintState} {secrets : List Secret}
    {outputs : List Proof} (h : swapValid s secrets outputs = true) :
    allKnown s secrets = true := by
  simp [swapValid] at h
  exact h.1.1.1.1.1.1.1

/-- The keyset-binding clause of `swapValid`. -/
theorem swapValid_inputsBound {s : MintState} {secrets : List Secret}
    {outputs : List Proof} (h : swapValid s secrets outputs = true) :
    inputsBound s secrets = true := by
  simp [swapValid] at h
  exact h.1.1.1.1.2

/-- The output-keyset clause of `swapValid`. -/
theorem swapValid_outputsValid {s : MintState} {secrets : List Secret}
    {outputs : List Proof} (h : swapValid s secrets outputs = true) :
    outputsValid s outputs = true := by
  simp [swapValid] at h
  exact h.1.1.1.2

/-- Spend `inputSecrets` and issue `outputs` of equal total value.

The old proofs leave `outstanding`; their secrets are appended to `spent`.
Fee handling (NUT-02) and change (NUT-08) are not modeled: totals must match
exactly. -/
def swap (s : MintState) (inputSecrets : List Secret)
    (outputs : List Proof) : Except MintError MintState :=
  if swapValid s inputSecrets outputs then
    .ok { s with
      outstanding := rejectBySecret s.outstanding inputSecrets ++ outputs
      spent := inputSecrets ++ s.spent
      proofKeyset := issuedBindings s.activeKeyset outputs ++ s.proofKeyset }
  else .error .invalidSwap

/-- **Solvency is preserved by swapping.** Equal-value reissuance leaves total
outstanding liability unchanged. -/
theorem swap_preserves_solvency (s : MintState) (inputSecrets : List Secret)
    (outputs : List Proof) (s' : MintState)
    (hm : swap s inputSecrets outputs = .ok s')
    (hs : s.reserve ≥ liability s) :
    s'.reserve ≥ liability s' := by
  unfold swap at hm
  split at hm
  · rename_i hvalid
    injection hm with hstate
    subst s'
    have heq : sumProofs outputs =
        sumProofs (selectBySecret s.outstanding inputSecrets) := by
      have h := hvalid
      simp [swapValid] at h
      exact swapValueOK_eq h.1.2
    have hpart := sumProofs_select_add_reject s.outstanding inputSecrets
    dsimp only [sumProofs] at heq hpart
    dsimp only [liability, sumProofs] at hs ⊢
    rw [List.map_append, List.sum_append]
    rw [heq]
    have hEq :
        (List.map (fun p => p.amount)
          (rejectBySecret s.outstanding inputSecrets)).sum +
        (List.map (fun p => p.amount)
          (selectBySecret s.outstanding inputSecrets)).sum =
        (List.map (fun p => p.amount) s.outstanding).sum := by
      rw [Nat.add_comm]
      exact hpart
    rw [hEq]
    exact hs
  · contradiction

/-! ## Melt (NUT-05) -/

/-- A melt is valid when all inputs are known, unspent, not pending, and
keyset-bound; at least one secret is supplied; the melt id is not already
pending; and the burned face value fits in the reserve. -/
def meltValid (s : MintState) (id : Nat) (secrets : List Secret) : Bool :=
  allKnown s secrets && noneSpent s secrets && nonePending s secrets &&
    inputsBound s secrets &&
    !secrets.isEmpty &&
    s.pending.all (fun m => m.id != id) &&
    (sumProofs (selectBySecret s.outstanding secrets) ≤ s.reserve)

/-- The known-input clause of `meltValid`. -/
theorem meltValid_allKnown {s : MintState} {id : Nat}
    {secrets : List Secret} (h : meltValid s id secrets = true) :
    allKnown s secrets = true := by
  simp [meltValid] at h
  exact h.1.1.1.1.1.1

/-- The not-pending clause of `meltValid`. -/
theorem meltValid_nonePending {s : MintState} {id : Nat}
    {secrets : List Secret} (h : meltValid s id secrets = true) :
    nonePending s secrets = true := by
  simp [meltValid] at h
  exact h.1.1.1.1.2

/-- The keyset-binding clause of `meltValid`. -/
theorem meltValid_inputsBound {s : MintState} {id : Nat}
    {secrets : List Secret} (h : meltValid s id secrets = true) :
    inputsBound s secrets = true := by
  simp [meltValid] at h
  exact h.1.1.1.2

/-- The fresh-id clause of `meltValid`. -/
theorem meltValid_ids {s : MintState} {id : Nat} {secrets : List Secret}
    (h : meltValid s id secrets = true) :
    ∀ m ∈ s.pending, m.id ≠ id := by
  simp [meltValid] at h
  exact h.1.2

/-- Burn `inputSecrets`, release reserve equal to their face value, and record
the melt in the pending journal.

Wave 0 is a no-fee, exact-value melt: the amount paid out is the input total.
The journal is optimistic — the proofs leave `outstanding` and the reserve
leaves immediately. `confirmMelt` finalizes; `refund` reverses. -/
def melt (s : MintState) (id : Nat) (inputSecrets : List Secret) :
    Except MintError MintState :=
  if meltValid s id inputSecrets then
    let burned := selectBySecret s.outstanding inputSecrets
    .ok { s with
      outstanding := rejectBySecret s.outstanding inputSecrets
      spent := inputSecrets ++ s.spent
      pending := { id := id, proofs := burned } :: s.pending
      reserve := s.reserve - sumProofs burned }
  else .error .invalidMelt

/-- **Solvency is preserved by melting.** The reserve drops by the burned
face value and outstanding liability drops by the same amount; a reserve that
covered the old liability covers the remainder. -/
theorem melt_preserves_solvency (s : MintState) (id : Nat)
    (inputSecrets : List Secret) (s' : MintState)
    (hm : melt s id inputSecrets = .ok s')
    (hs : s.reserve ≥ liability s) :
    s'.reserve ≥ liability s' := by
  unfold melt at hm
  split at hm
  · rename_i _hvalid
    injection hm with hstate
    subst s'
    have hpart := sumProofs_select_add_reject s.outstanding inputSecrets
    have hsub :
        s.reserve - sumProofs (selectBySecret s.outstanding inputSecrets) ≥
        liability s - sumProofs (selectBySecret s.outstanding inputSecrets) :=
      Nat.sub_le_sub_right hs _
    have hL : liability s =
        sumProofs (selectBySecret s.outstanding inputSecrets) +
        sumProofs (rejectBySecret s.outstanding inputSecrets) := hpart.symm
    rw [hL] at hsub
    change s.reserve - sumProofs (selectBySecret s.outstanding inputSecrets) ≥
      sumProofs (rejectBySecret s.outstanding inputSecrets)
    simpa [Nat.add_sub_cancel_left] using hsub
  · contradiction

/-! ## Refund and confirmation -/

/-- Remove every occurrence of the given secrets. -/
def removeSecrets (xs ys : List Secret) : List Secret :=
  xs.filter (fun x => !contains ys x)

/-- Membership after removing secrets. -/
theorem mem_removeSecrets {xs ys : List Secret} {x : Secret} :
    x ∈ removeSecrets xs ys ↔ x ∈ xs ∧ x ∉ ys := by
  simp [removeSecrets, List.mem_filter, contains_eq_false]

/-- Removing a list of secrets preserves membership of everything not removed. -/
theorem mem_removeSecrets_of_mem_of_not_mem {xs ys : List Secret} {x : Secret}
    (hx : x ∈ xs) (hy : x ∉ ys) : x ∈ removeSecrets xs ys :=
  mem_removeSecrets.mpr ⟨hx, hy⟩

/-- Anything carrying a removed secret is absent from `removeSecrets`. -/
theorem not_mem_removeSecrets_of_mem {xs ys : List Secret} {x : Secret}
    (h : x ∈ ys) : x ∉ removeSecrets xs ys := by
  intro hx
  exact (mem_removeSecrets.mp hx).2 h

/-- Reverse a failed melt: restore its proofs to `outstanding`, restore the
same reserve value, and release its secrets from `spent`.

The model does not know whether the external payment succeeded. Calling
`refund` is an operator decision; `confirmMelt` is the success path. -/
def refund (s : MintState) (id : Nat) : Except MintError MintState :=
  match s.pending.find? (fun m => m.id == id) with
  | none => .error .noSuchMelt
  | some m =>
      .ok { s with
        outstanding := s.outstanding ++ m.proofs
        spent := removeSecrets s.spent m.secrets
        pending := s.pending.filter (fun n => n.id != id)
        reserve := s.reserve + m.amount }

/-- **Solvency is preserved by refunding a failed melt.** Refund adds the same
face value to both reserve and outstanding liability, so the inequality is
unchanged. -/
theorem refund_preserves_solvency (s : MintState) (id : Nat) (s' : MintState)
    (hm : refund s id = .ok s')
    (hs : s.reserve ≥ liability s) :
    s'.reserve ≥ liability s' := by
  unfold refund at hm
  split at hm
  · simp at hm
  · rename_i m _hfind
    injection hm with hstate
    subst s'
    dsimp only [liability, sumProofs] at hs ⊢
    rw [List.map_append, List.sum_append]
    change s.reserve + m.amount ≥
      (List.map (fun p => p.amount) s.outstanding).sum +
        (List.map (fun p => p.amount) m.proofs).sum
    have ham : m.amount =
        (List.map (fun p => p.amount) m.proofs).sum := rfl
    rw [ham]
    exact Nat.add_le_add_right hs _

/-- Finalize a successful melt by dropping its journal entry. The proofs'
secrets remain in `spent` from `melt`. -/
def confirmMelt (s : MintState) (id : Nat) : Except MintError MintState :=
  match s.pending.find? (fun m => m.id == id) with
  | none => .error .noSuchMelt
  | some _ =>
      .ok { s with pending := s.pending.filter (fun n => n.id != id) }

/-- Confirmation does not touch `outstanding` or `reserve`, so solvency is
immediate. -/
theorem confirmMelt_preserves_solvency (s : MintState) (id : Nat)
    (s' : MintState) (hm : confirmMelt s id = .ok s')
    (hs : s.reserve ≥ liability s) :
    s'.reserve ≥ liability s' := by
  unfold confirmMelt at hm
  split at hm
  · simp at hm
  · rename_i _m _hfind
    injection hm with hstate
    subst s'
    exact hs

end Cashu
