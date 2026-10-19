import CashuLean.Fees

/-!
# CashuLean.Invariants — reachability and pending-journal invariants

This module supplies the reachability closure that the per-transition
preservation theorems in `CashuLean.Mint` and `CashuLean.Fees` leave implicit,
and closes the output-freshness gap with the checks from
`CashuLean.Freshness`.

## What is proved

* `Reachable` is the closure of `empty` under the six successful operations
  (`mint`, `swap`, `swapWithFee`, `melt`, `refund`, `confirmMelt`).
* `reachable_solvent` derives `s.reserve ≥ liability s` for every reachable
  state by induction, using the six existing solvency preservation theorems.
* `PendingBacked` is the machine-checkable pending-journal boundary:
  every pending proof secret is in `spent`, no pending proof
  secret is in `outstanding`, and pending melt ids are `Nodup`.
* `WellFormed` records the full target for this module.
* `empty_wellFormed` checks the base state.
* `FreshInvariant` adds one auxiliary clause to `WellFormed`: different pending
  melts carry disjoint proof secrets.  Without it, `refund` cannot preserve
  `WellFormed` (it moves one pending melt's proofs back into `outstanding`
  while other melts remain).  The clause is preserved by all six operations
  because `meltValid` rejects inputs already locked in a pending melt.
* `reachable_freshInvariant`, `reachable_wellFormed`, and
  `reachable_pending_backed` lift the six preservation lemmas over `Reachable`.

The output-producing validators (`mintValid`, `swapValid`,
`swapWithFeeValid`) now require `outputsFresh`, so the earlier secret-reuse
counterexample is rejected by construction.  The definitions of
`PendingBacked` and `WellFormed` are unchanged.

No proof holes or kernel escape hatches are used.
-/

namespace Cashu

/-- A 66-character V2-shaped keyset id used by the executable example state.
It is a single literal so kernel `decide` can inspect its bytes. -/
def emptyKeysetId : KeysetId :=
  "010000000000000000000000000000000000000000000000000000000000000000"

/-- A 66-character compressed-key-shaped public key used by `empty`. -/
def emptyPubKey : PubKey :=
  "020000000000000000000000000000000000000000000000000000000000000000"

/-- The key map of the example active keyset. Amounts need not be powers of
two for the accounting model; the tests use 1, 2, 4, 6, and 10. -/
def emptyKeys : List (Amount × PubKey) :=
  [(1, emptyPubKey), (2, emptyPubKey), (4, emptyPubKey), (6, emptyPubKey),
    (10, emptyPubKey)]

/-- The initial mint state: no proofs, no spent or pending secrets, zero
reserve, zero issuance, an active zero-fee keyset, and no bindings. -/
def empty : MintState :=
  { outstanding := []
    spent := []
    pending := []
    reserve := 0
    issued := 0
    keysets :=
      [{ id := emptyKeysetId, unit := "sat", active := true, inputFeePpk := 0,
          finalExpiry := none, keys := emptyKeys }]
    activeKeyset := emptyKeysetId
    proofKeyset := [] }

/-- Reachability closure of the accounting state machine.

There is one constructor for each successful operation. Every constructor
carries the reachability of its pre-state and the equality witnessed by the
operation's `Except` result. The operation arguments are explicit so that the
constructor records the exact successful call. -/
inductive Reachable : MintState → Prop where
  | empty : Reachable empty
  | mint (s : MintState) (deposit : Amount) (outputs : List Proof)
      (s' : MintState) (h : Reachable s)
      (hm : Cashu.mint s deposit outputs = .ok s') : Reachable s'
  | swap (s : MintState) (inputSecrets : List Secret) (outputs : List Proof)
      (s' : MintState) (h : Reachable s)
      (hm : Cashu.swap s inputSecrets outputs = .ok s') : Reachable s'
  | swapWithFee (s : MintState) (inputSecrets : List Secret)
      (outputs : List Proof) (fee : Nat) (s' : MintState)
      (h : Reachable s)
      (hm : Cashu.swapWithFee s inputSecrets outputs fee = .ok s') :
      Reachable s'
  | melt (s : MintState) (id : Nat) (inputSecrets : List Secret)
      (s' : MintState) (h : Reachable s)
      (hm : Cashu.melt s id inputSecrets = .ok s') : Reachable s'
  | refund (s : MintState) (id : Nat) (s' : MintState)
      (h : Reachable s) (hm : Cashu.refund s id = .ok s') : Reachable s'
  | confirmMelt (s : MintState) (id : Nat) (s' : MintState)
      (h : Reachable s) (hm : Cashu.confirmMelt s id = .ok s') : Reachable s'

/-- **Every reachable state is solvent.** This closes the per-transition
theorems into an invariant over the whole reachable state space. -/
theorem reachable_solvent (s : MintState) (h : Reachable s) :
    s.reserve ≥ liability s := by
  induction h with
  | empty =>
      simp [empty, liability, sumProofs]
  | mint s deposit outputs s' _h hm ih =>
      exact mint_preserves_solvency s deposit outputs s' hm ih
  | swap s inputSecrets outputs s' _h hm ih =>
      exact swap_preserves_solvency s inputSecrets outputs s' hm ih
  | swapWithFee s inputSecrets outputs fee s' _h hm ih =>
      exact swapWithFee_preserves_solvency s inputSecrets outputs fee s' hm ih
  | melt s id inputSecrets s' _h hm ih =>
      exact melt_preserves_solvency s id inputSecrets s' hm ih
  | refund s id s' _h hm ih =>
      exact refund_preserves_solvency s id s' hm ih
  | confirmMelt s id s' _h hm ih =>
      exact confirmMelt_preserves_solvency s id s' hm ih

/-- The pending-journal boundary.

1. Every proof secret of every pending melt is recorded in `s.spent`.
2. No proof secret of a pending melt occurs in `s.outstanding`.
3. Pending melt ids are pairwise distinct.

This is the *exact* definition requested for module 1 and it is not weakened
here. -/
def PendingBacked (s : MintState) : Prop :=
  (∀ m ∈ s.pending, ∀ p ∈ m.proofs, p.secret ∈ s.spent) ∧
  (∀ m ∈ s.pending, ∀ p ∈ m.proofs,
    p.secret ∉ s.outstanding.map Proof.secret) ∧
  (s.pending.map PendingMelt.id).Nodup

/-- The audit's full target invariant for this module.

* outstanding proof secrets are `Nodup`;
* pending melt ids are `Nodup`;
* outstanding and spent secrets are disjoint;
* every pending proof secret is in `spent` (the pending ⊆ spent boundary);
* `PendingBacked` holds.

This definition is unchanged by the freshness increment. -/
def WellFormed (s : MintState) : Prop :=
  (s.outstanding.map Proof.secret).Nodup ∧
  (s.pending.map PendingMelt.id).Nodup ∧
  (∀ p ∈ s.outstanding, p.secret ∉ s.spent) ∧
  (∀ m ∈ s.pending, ∀ p ∈ m.proofs, p.secret ∈ s.spent) ∧
  PendingBacked s

/-- The empty state satisfies the full target invariant. -/
theorem empty_wellFormed : WellFormed empty := by
  simp [WellFormed, PendingBacked, empty]

/-! ## Auxiliary invariant and validator projections -/

/-- `WellFormed` plus the fact that different pending melts carry disjoint
proof secrets.  The extra clause is needed by `refund`; it is not part of the
requested `WellFormed` definition. -/
def FreshInvariant (s : MintState) : Prop :=
  WellFormed s ∧ PendingDistinct s

/-- The binding table's secrets are all accounted for by outstanding proofs,
spent secrets, or pending-melt proofs.  This is what lets an append of fresh
outputs preserve binding-table `Nodup`. -/
def BindingsCover (s : MintState) : Prop :=
  ∀ e ∈ s.proofKeyset,
    e.1 ∈ s.outstanding.map Proof.secret ∨
    e.1 ∈ s.spent ∨
    e.1 ∈ s.pendingSecrets

/-- The active pointer resolves to an active keyset. -/
def ActiveKeysetPresent (s : MintState) : Prop :=
  ∃ k, activeKeyset? s = some k ∧ k.active = true

/-- Invariants for the keyset and proof-binding tables added by this
increment.  `keysetsWellFormed` and `bindingsWellFormed` are state-authority
assumptions, not type invariants; preservation is proved for every operation. -/
def KeysetInvariant (s : MintState) : Prop :=
  s.keysetsWellFormed ∧
  s.bindingsWellFormed ∧
  ActiveKeysetPresent s ∧
  BindingsCover s

/-- The empty state satisfies the auxiliary freshness invariant. -/
theorem empty_freshInvariant : FreshInvariant empty := by
  constructor
  · exact empty_wellFormed
  · simp [PendingDistinct, empty]

/-- The empty state satisfies the keyset/binding invariant. -/
theorem empty_keysetInvariant : KeysetInvariant empty := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · simp [empty]
    · intro k hk
      simp [empty] at hk
      subst k
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · decide
      · decide
      · decide
      · decide
      · intro e he
        simp [emptyKeys] at he
        rcases he with rfl | rfl | rfl | rfl | rfl <;> decide
      · intro t ht
        simp at ht
  · constructor
    · constructor
      · simp [empty]
      · intro e he
        simp [empty] at he
    · intro e he
      simp [empty] at he
  · let active : Keyset :=
      { id := emptyKeysetId, unit := "sat", active := true, inputFeePpk := 0,
        finalExpiry := none, keys := emptyKeys }
    refine ⟨active, ?_, ?_⟩
    · change keysetOf? empty emptyKeysetId = some active
      rfl
    · rfl
  · intro e he
    simp [empty] at he

/-- A proof secret from an outstanding proof is either selected by the secret
list (and hence in it) or retained by `rejectBySecret`. -/
theorem mem_reject_or_mem_of_mem_map {ps : List Proof} {secrets : List Secret}
    {x : Secret} (h : x ∈ ps.map Proof.secret) :
    x ∈ (rejectBySecret ps secrets).map Proof.secret ∨ x ∈ secrets := by
  rcases List.mem_map.mp h with ⟨p, hp, hpeq⟩
  cases hc : contains secrets p.secret with
  | true =>
      right
      rw [← hpeq]
      exact contains_eq_true.mp hc
  | false =>
      left
      rw [← hpeq]
      exact List.mem_map_of_mem (mem_rejectBySecret.mpr ⟨hp, hc⟩)

/-- Appending freshly issued bindings preserves binding-table well-formedness,
provided the new id is V2-shaped and names a known keyset. -/
theorem bindingsWellFormed_append_issued (s : MintState) (kid : KeysetId)
    (outputs : List Proof)
    (hb : s.bindingsWellFormed) (hcov : BindingsCover s)
    (hfresh : outputsFresh s outputs = true)
    (hkid : isV2Id kid = true)
    (hknown : ∃ k ∈ s.keysets, kid = k.id) :
    ({ s with proofKeyset := issuedBindings kid outputs ++ s.proofKeyset } :
      MintState).bindingsWellFormed := by
  unfold MintState.bindingsWellFormed at hb ⊢
  rcases hb with ⟨holdWF, holdKnown⟩
  rcases holdWF with ⟨holdNodup, holdIds⟩
  constructor
  · constructor
    · have hnod : (outputs.map Proof.secret ++ s.proofKeyset.map Prod.fst).Nodup := by
        rw [List.nodup_append]
        refine ⟨?_, holdNodup, ?_⟩
        · simpa [outputSecrets] using outputsFresh_nodup hfresh
        · intro x hx y hy hxy
          rcases List.mem_map.mp hx with ⟨p, hp, hpeq⟩
          rcases List.mem_map.mp hy with ⟨e, he, heeq⟩
          have hEq : p.secret = e.1 := by rw [hpeq, hxy, ← heeq]
          rcases hcov e he with ho | hs | hpending
          · exact (outputsFresh_not_mem_outstanding hfresh p hp)
              (by rwa [← hEq] at ho)
          · exact (outputsFresh_not_mem_spent hfresh p hp)
              (by rwa [← hEq] at hs)
          · exact (outputsFresh_not_mem_pending hfresh p hp)
              (by rwa [← hEq] at hpending)
      simpa [issuedBindings, List.map_append, List.map_map, Function.comp_def,
        outputSecrets] using hnod
    · intro e he
      rcases List.mem_append.mp he with hnew | hold
      · rcases List.mem_map.mp hnew with ⟨p, hp, hpeq⟩
        rw [← hpeq]
        exact hkid
      · exact holdIds e hold
  · intro e he
    rcases List.mem_append.mp he with hnew | hold
    · rcases List.mem_map.mp hnew with ⟨p, hp, hpeq⟩
      rw [← hpeq]
      exact hknown
    · exact holdKnown e hold

/-- Minting appends outputs to `outstanding`; the binding cover is preserved. -/
theorem bindingsCover_mint (s : MintState) (kid : KeysetId)
    (outputs : List Proof) (hcov : BindingsCover s) :
    BindingsCover { s with
      outstanding := s.outstanding ++ outputs
      proofKeyset := issuedBindings kid outputs ++ s.proofKeyset } := by
  intro e he
  unfold BindingsCover at hcov
  rcases List.mem_append.mp he with hnew | hold
  · left
    rcases List.mem_map.mp hnew with ⟨p, hp, hpeq⟩
    rw [← hpeq, List.map_append]
    exact List.mem_append_right _ (List.mem_map_of_mem hp)
  · rcases hcov e hold with ho | hs | hp
    · left
      rw [List.map_append]
      exact List.mem_append_left _ ho
    · right; left; exact hs
    · right; right; exact hp

/-- Swapping moves selected proofs to `spent` and rejects the rest; the
binding cover is preserved. -/
theorem bindingsCover_swap (s : MintState) (secrets : List Secret)
    (outputs : List Proof) (kid : KeysetId) (hcov : BindingsCover s) :
    BindingsCover { s with
      outstanding := rejectBySecret s.outstanding secrets ++ outputs
      spent := secrets ++ s.spent
      proofKeyset := issuedBindings kid outputs ++ s.proofKeyset } := by
  intro e he
  unfold BindingsCover at hcov
  rcases List.mem_append.mp he with hnew | hold
  · left
    rcases List.mem_map.mp hnew with ⟨p, hp, hpeq⟩
    rw [← hpeq, List.map_append]
    exact List.mem_append_right _ (List.mem_map_of_mem hp)
  · rcases hcov e hold with ho | hs | hp
    · rcases mem_reject_or_mem_of_mem_map ho with hrej | hsec
      · left
        rw [List.map_append]
        exact List.mem_append_left _ hrej
      · right; left
        exact List.mem_append_left _ hsec
    · right; left
      exact List.mem_append_right _ hs
    · right; right; exact hp

/-- Melting moves selected proofs to `spent` and rejects the rest; the binding
cover is preserved. -/
theorem bindingsCover_melt (s : MintState) (id : Nat)
    (secrets : List Secret) (hcov : BindingsCover s) :
    BindingsCover { s with
      outstanding := rejectBySecret s.outstanding secrets
      spent := secrets ++ s.spent
      pending := { id := id, proofs := selectBySecret s.outstanding secrets } ::
        s.pending } := by
  intro e he
  change e ∈ s.proofKeyset at he
  unfold BindingsCover at hcov
  rcases hcov e he with ho | hs | hp
  · rcases mem_reject_or_mem_of_mem_map ho with hrej | hsec
    · left; exact hrej
    · right; left
      exact List.mem_append_left _ hsec
  · right; left
    exact List.mem_append_right _ hs
  · right; right
    simp only [MintState.pendingSecrets, List.flatMap_cons, List.mem_append]
    exact Or.inr hp

/-- A secret that `allKnown` accepts is an outstanding proof secret. -/
theorem mem_outstanding_of_allKnown {s : MintState} {secrets : List Secret}
    {x : Secret} (h : allKnown s secrets = true) (hx : x ∈ secrets) :
    x ∈ s.outstanding.map Proof.secret := by
  exact contains_eq_true.mp ((List.all_eq_true.mp h) x hx)

/-- A secret that `nonePending` accepts is not a pending proof secret. -/
theorem not_mem_pendingSecrets_of_nonePending {s : MintState}
    {secrets : List Secret} {x : Secret}
    (h : nonePending s secrets = true) (hx : x ∈ secrets) :
    x ∉ s.pendingSecrets := by
  have hb : (!contains s.pendingSecrets x) = true :=
    (List.all_eq_true.mp h) x hx
  rw [Bool.not_eq_true'] at hb
  exact contains_eq_false.mp hb

/-- A melt id accepted by the fresh-id check is absent from the journal. -/
theorem id_not_mem_of_valid {s : MintState} {id : Nat}
    (h : ∀ m ∈ s.pending, m.id ≠ id) :
    id ∉ s.pending.map PendingMelt.id := by
  intro hid
  rcases List.mem_map.mp hid with ⟨m, hm, hmid⟩
  exact h m hm hmid

/-- A `find?` hit belongs to the searched list. -/
theorem mem_of_find?_eq_some {s : MintState} {id : Nat} {m : PendingMelt}
    (h : s.pending.find? (fun m => m.id == id) = some m) :
    m ∈ s.pending :=
  List.mem_of_find?_eq_some h

/-- A `find?` hit satisfies the search predicate. -/
theorem id_eq_of_find?_eq_some {s : MintState} {id : Nat} {m : PendingMelt}
    (h : s.pending.find? (fun m => m.id == id) = some m) :
    m.id = id :=
  beq_iff_eq.mp (List.find?_some (p := fun n : PendingMelt => n.id == id) h)

/-! ## Preservation of `FreshInvariant` -/

/-- Minting preserves the auxiliary invariant. -/
theorem mint_preserves_freshInvariant (s : MintState) (deposit : Amount)
    (outputs : List Proof) (s' : MintState)
    (hm : Cashu.mint s deposit outputs = .ok s')
    (h : FreshInvariant s) : FreshInvariant s' := by
  rcases h with ⟨hWF, hPD⟩
  rcases hWF with ⟨houtNodup, hpendingIds, houtSpent, hpendingSpent, hPB⟩
  rcases hPB with ⟨hPB1, hPB2, hPB3⟩
  unfold Cashu.mint at hm
  split at hm
  · rename_i hvalid
    have hfresh := mintValid_outputsFresh hvalid
    injection hm with hstate
    subst s'
    have hfreshNodup := outputsFresh_nodup hfresh
    have hfreshSpent := outputsFresh_not_mem_spent hfresh
    have hfreshOut := outputsFresh_not_mem_outstanding hfresh
    have hfreshPending := outputsFresh_not_mem_pending hfresh
    constructor
    · refine ⟨?_, hpendingIds, ?_, ?_, ?_⟩
      · have hnod := nodup_append_of houtNodup hfreshNodup (by
          intro x hx y hy hxy
          rcases List.mem_map.mp hy with ⟨q, hq, hqeq⟩
          have hx' : q.secret ∈ outputSecrets s.outstanding := by
            rw [hqeq, ← hxy]
            exact hx
          exact hfreshOut q hq hx')
        simpa [outputSecrets, List.map_append] using hnod
      · intro p hp
        rcases List.mem_append.mp hp with hpo | hpn
        · exact houtSpent p hpo
        · exact hfreshSpent p hpn
      · intro m hm p hp
        exact hpendingSpent m hm p hp
      · refine ⟨hPB1, ?_, hPB3⟩
        intro m hm p hp hmem
        rw [List.map_append] at hmem
        rcases List.mem_append.mp hmem with hpo | hpn
        · exact hPB2 m hm p hp hpo
        · rcases List.mem_map.mp hpn with ⟨q, hq, hqeq⟩
          have hpending : p.secret ∈ s.pendingSecrets :=
            mem_pendingSecrets_of_mem_proofs hm hp
          exact hfreshPending q hq (by simpa [hqeq] using hpending)
    · simpa [PendingDistinct] using hPD
  · contradiction

/-- Swapping preserves the auxiliary invariant. -/
theorem swap_preserves_freshInvariant (s : MintState)
    (inputSecrets : List Secret) (outputs : List Proof) (s' : MintState)
    (hm : Cashu.swap s inputSecrets outputs = .ok s')
    (h : FreshInvariant s) : FreshInvariant s' := by
  rcases h with ⟨hWF, hPD⟩
  rcases hWF with ⟨houtNodup, hpendingIds, houtSpent, hpendingSpent, hPB⟩
  rcases hPB with ⟨hPB1, hPB2, hPB3⟩
  unfold Cashu.swap at hm
  split at hm
  · rename_i hvalid
    have hfresh := swapValid_outputsFresh hvalid
    have hknown := swapValid_allKnown hvalid
    injection hm with hstate
    subst s'
    have hfreshNodup := outputsFresh_nodup hfresh
    have hfreshSpent := outputsFresh_not_mem_spent hfresh
    have hfreshOut := outputsFresh_not_mem_outstanding hfresh
    have hfreshPending := outputsFresh_not_mem_pending hfresh
    constructor
    · refine ⟨?_, hpendingIds, ?_, ?_, ?_⟩
      · have hrejNodup :
            (outputSecrets (rejectBySecret s.outstanding inputSecrets)).Nodup :=
          nodup_outputSecrets_filter
            (pred := fun p => !contains inputSecrets p.secret) houtNodup
        have hnod := nodup_append_of hrejNodup hfreshNodup (by
            intro x hx y hy hxy
            rcases List.mem_map.mp hx with ⟨p, hp, hpeq⟩
            rcases List.mem_map.mp hy with ⟨q, hq, hqeq⟩
            have hpold : p ∈ s.outstanding := (List.mem_filter.mp hp).1
            have hxold : p.secret ∈ s.outstanding.map Proof.secret :=
              List.mem_map_of_mem hpold
            have hx' : q.secret ∈ outputSecrets s.outstanding := by
              rw [hqeq, ← hxy, ← hpeq]
              exact hxold
            exact hfreshOut q hq hx')
        simpa [outputSecrets, List.map_append] using hnod
      · intro p hp hspent
        rcases List.mem_append.mp hp with hprej | hpout
        · have hpred := mem_rejectBySecret.mp hprej
          rcases List.mem_append.mp hspent with hin | hsp
          · exact secret_not_mem_of_mem_rejectBySecret hprej hin
          · exact houtSpent p hpred.1 hsp
        · rcases List.mem_append.mp hspent with hin | hsp
          · exact hfreshOut p hpout (mem_outstanding_of_allKnown hknown hin)
          · exact hfreshSpent p hpout hsp
      · intro m hm p hp
        exact List.mem_append_right inputSecrets (hpendingSpent m hm p hp)
      · refine ⟨?_, ?_, hPB3⟩
        · intro m hm p hp
          exact List.mem_append_right inputSecrets (hpendingSpent m hm p hp)
        · intro m hm p hp hmem
          change p.secret ∈
            (rejectBySecret s.outstanding inputSecrets ++ outputs).map Proof.secret at hmem
          rw [List.map_append] at hmem
          rcases List.mem_append.mp hmem with hrej | hout
          · exact hPB2 m hm p hp (mem_outstanding_of_mem_rejectBySecret hrej)
          · rcases List.mem_map.mp hout with ⟨q, hq, hqeq⟩
            have hpending : p.secret ∈ s.pendingSecrets :=
              mem_pendingSecrets_of_mem_proofs hm hp
            exact hfreshPending q hq (by simpa [hqeq] using hpending)
    · simpa [PendingDistinct] using hPD
  · contradiction

/-- A fee-aware swap preserves the auxiliary invariant. -/
theorem swapWithFee_preserves_freshInvariant (s : MintState)
    (inputSecrets : List Secret) (outputs : List Proof) (fee : Nat)
    (s' : MintState)
    (hm : Cashu.swapWithFee s inputSecrets outputs fee = .ok s')
    (h : FreshInvariant s) : FreshInvariant s' := by
  rcases h with ⟨hWF, hPD⟩
  rcases hWF with ⟨houtNodup, hpendingIds, houtSpent, hpendingSpent, hPB⟩
  rcases hPB with ⟨hPB1, hPB2, hPB3⟩
  unfold Cashu.swapWithFee at hm
  split at hm
  · rename_i hvalid
    have hfresh := swapWithFeeValid_outputsFresh hvalid
    have hknown : allKnown s inputSecrets = true :=
      swapWithFeeValid_allKnown hvalid
    injection hm with hstate
    subst s'
    have hfreshNodup := outputsFresh_nodup hfresh
    have hfreshSpent := outputsFresh_not_mem_spent hfresh
    have hfreshOut := outputsFresh_not_mem_outstanding hfresh
    have hfreshPending := outputsFresh_not_mem_pending hfresh
    constructor
    · refine ⟨?_, hpendingIds, ?_, ?_, ?_⟩
      · have hrejNodup :
            (outputSecrets (rejectBySecret s.outstanding inputSecrets)).Nodup :=
          nodup_outputSecrets_filter
            (pred := fun p => !contains inputSecrets p.secret) houtNodup
        have hnod := nodup_append_of hrejNodup hfreshNodup (by
            intro x hx y hy hxy
            rcases List.mem_map.mp hx with ⟨p, hp, hpeq⟩
            rcases List.mem_map.mp hy with ⟨q, hq, hqeq⟩
            have hpold : p ∈ s.outstanding := (List.mem_filter.mp hp).1
            have hxold : p.secret ∈ s.outstanding.map Proof.secret :=
              List.mem_map_of_mem hpold
            have hx' : q.secret ∈ outputSecrets s.outstanding := by
              rw [hqeq, ← hxy, ← hpeq]
              exact hxold
            exact hfreshOut q hq hx')
        simpa [outputSecrets, List.map_append] using hnod
      · intro p hp hspent
        rcases List.mem_append.mp hp with hprej | hpout
        · have hpred := mem_rejectBySecret.mp hprej
          rcases List.mem_append.mp hspent with hin | hsp
          · exact secret_not_mem_of_mem_rejectBySecret hprej hin
          · exact houtSpent p hpred.1 hsp
        · rcases List.mem_append.mp hspent with hin | hsp
          · exact hfreshOut p hpout (mem_outstanding_of_allKnown hknown hin)
          · exact hfreshSpent p hpout hsp
      · intro m hm p hp
        exact List.mem_append_right inputSecrets (hpendingSpent m hm p hp)
      · refine ⟨?_, ?_, hPB3⟩
        · intro m hm p hp
          exact List.mem_append_right inputSecrets (hpendingSpent m hm p hp)
        · intro m hm p hp hmem
          change p.secret ∈
            (rejectBySecret s.outstanding inputSecrets ++ outputs).map Proof.secret at hmem
          rw [List.map_append] at hmem
          rcases List.mem_append.mp hmem with hrej | hout
          · exact hPB2 m hm p hp (mem_outstanding_of_mem_rejectBySecret hrej)
          · rcases List.mem_map.mp hout with ⟨q, hq, hqeq⟩
            have hpending : p.secret ∈ s.pendingSecrets :=
              mem_pendingSecrets_of_mem_proofs hm hp
            exact hfreshPending q hq (by simpa [hqeq] using hpending)
    · simpa [PendingDistinct] using hPD
  · contradiction

/-- Melting preserves the auxiliary invariant. -/
theorem melt_preserves_freshInvariant (s : MintState) (id : Nat)
    (inputSecrets : List Secret) (s' : MintState)
    (hm : Cashu.melt s id inputSecrets = .ok s')
    (h : FreshInvariant s) : FreshInvariant s' := by
  rcases h with ⟨hWF, hPD⟩
  rcases hWF with ⟨houtNodup, hpendingIds, houtSpent, hpendingSpent, hPB⟩
  rcases hPB with ⟨hPB1, hPB2, hPB3⟩
  unfold Cashu.melt at hm
  split at hm
  · rename_i hvalid
    have hnonePending := meltValid_nonePending hvalid
    have hids := meltValid_ids hvalid
    injection hm with hstate
    subst s'
    have hburnedNodup :
        (outputSecrets (selectBySecret s.outstanding inputSecrets)).Nodup :=
      nodup_outputSecrets_filter houtNodup
    have hidFresh : id ∉ s.pending.map PendingMelt.id :=
      id_not_mem_of_valid hids
    constructor
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact nodup_outputSecrets_filter houtNodup
      · exact List.nodup_cons.mpr ⟨hidFresh, hpendingIds⟩
      · intro p hp hspent
        have hpred := mem_rejectBySecret.mp hp
        rcases List.mem_append.mp hspent with hin | hsp
        · exact secret_not_mem_of_mem_rejectBySecret hp hin
        · exact houtSpent p hpred.1 hsp
      · intro m hm p hp
        rcases List.mem_cons.mp hm with rfl | hmold
        · exact List.mem_append_left s.spent
            (secret_mem_of_mem_selectBySecret hp)
        · exact List.mem_append_right inputSecrets (hpendingSpent m hmold p hp)
      · refine ⟨?_, ?_, ?_⟩
        · intro m hm p hp
          rcases List.mem_cons.mp hm with rfl | hmold
          · exact List.mem_append_left s.spent
              (secret_mem_of_mem_selectBySecret hp)
          · exact List.mem_append_right inputSecrets (hpendingSpent m hmold p hp)
        · intro m hm p hp hmem
          rcases List.mem_cons.mp hm with rfl | hmold
          · have hin : p.secret ∈ inputSecrets :=
              secret_mem_of_mem_selectBySecret hp
            rcases List.mem_map.mp hmem with ⟨q, hq, hqeq⟩
            have hqnot : q.secret ∉ inputSecrets :=
              secret_not_mem_of_mem_rejectBySecret hq
            exact hqnot (by simpa [hqeq] using hin)
          · rcases List.mem_map.mp hmem with ⟨q, hq, hqeq⟩
            have hqold : q.secret ∈ s.outstanding.map Proof.secret :=
              List.mem_map_of_mem (mem_rejectBySecret.mp hq).1
            exact hPB2 m hmold p hp (by simpa [hqeq] using hqold)
        · exact List.nodup_cons.mpr ⟨hidFresh, hpendingIds⟩
    · constructor
      · intro m hm
        rcases List.mem_cons.mp hm with rfl | hmold
        · exact hburnedNodup
        · exact hPD.1 m hmold
      · intro m hm n hn hne x hx hxn
        rcases List.mem_cons.mp hm with rfl | hmold <;>
          rcases List.mem_cons.mp hn with rfl | hnold
        · exact hne rfl
        · have hin : x ∈ inputSecrets := by
            rcases List.mem_map.mp hx with ⟨p, hp, hpeq⟩
            exact hpeq ▸ secret_mem_of_mem_selectBySecret hp
          have hxnot : x ∉ s.pendingSecrets :=
            not_mem_pendingSecrets_of_nonePending hnonePending hin
          rcases List.mem_map.mp hxn with ⟨p, hp, hpeq⟩
          exact hxnot (hpeq ▸ mem_pendingSecrets_of_mem_proofs hnold hp)
        · rcases List.mem_map.mp hxn with ⟨p, hp, hpeq⟩
          have hin : x ∈ inputSecrets := by
            rw [← hpeq]
            exact secret_mem_of_mem_selectBySecret hp
          have hxnot : x ∉ s.pendingSecrets :=
            not_mem_pendingSecrets_of_nonePending hnonePending hin
          rcases List.mem_map.mp hx with ⟨q, hq, hqeq⟩
          exact hxnot (hqeq ▸ mem_pendingSecrets_of_mem_proofs hmold hq)
        · exact hPD.2 m hmold n hnold hne x hx hxn
  · contradiction

/-- Refunding a failed melt preserves the auxiliary invariant. -/
theorem refund_preserves_freshInvariant (s : MintState) (id : Nat)
    (s' : MintState) (hm : Cashu.refund s id = .ok s')
    (h : FreshInvariant s) : FreshInvariant s' := by
  rcases h with ⟨hWF, hPD⟩
  rcases hWF with ⟨houtNodup, hpendingIds, houtSpent, hpendingSpent, hPB⟩
  rcases hPB with ⟨hPB1, hPB2, hPB3⟩
  unfold Cashu.refund at hm
  split at hm
  · simp at hm
  · rename_i m hfind
    have hmmem : m ∈ s.pending := mem_of_find?_eq_some hfind
    have hmid : m.id = id := id_eq_of_find?_eq_some hfind
    have hmNodup : (m.proofs.map Proof.secret).Nodup := hPD.1 m hmmem
    injection hm with hstate
    subst s'
    have hfilteredId :
        ((s.pending.filter (fun n => n.id != id)).map PendingMelt.id).Nodup := by
      exact List.Nodup.sublist
        (List.Sublist.map PendingMelt.id
          (List.filter_sublist (p := fun n => n.id != id) (l := s.pending)))
        hpendingIds
    have hnotId {n : PendingMelt} (hn : n ∈ s.pending.filter (fun n => n.id != id)) :
        n.id ≠ id :=
      bne_iff_ne.mp (List.mem_filter.mp hn).2
    have hnmem {n : PendingMelt}
        (hn : n ∈ s.pending.filter (fun n => n.id != id)) : n ∈ s.pending :=
      (List.mem_filter.mp hn).1
    have hneM {n : PendingMelt}
        (hn : n ∈ s.pending.filter (fun n => n.id != id)) : n ≠ m := by
      intro hnm
      exact hnotId hn (by simpa [hnm] using hmid)
    have hsecretsNe {n : PendingMelt}
        (hn : n ∈ s.pending.filter (fun n => n.id != id))
        {q : Proof} (hq : q ∈ n.proofs) :
        q.secret ∉ m.proofs.map Proof.secret :=
      pendingDistinct_ne_secrets hPD (hnmem hn) hmmem (hneM hn)
        (List.mem_map_of_mem hq)
    have hpendingRemain : ∀ n ∈ s.pending.filter (fun n => n.id != id),
        ∀ q ∈ n.proofs, q.secret ∈ s.spent := by
      intro n hn q hq
      exact hpendingSpent n (hnmem hn) q hq
    have hpendingNotOut : ∀ n ∈ s.pending.filter (fun n => n.id != id),
        ∀ q ∈ n.proofs, q.secret ∉
          (s.outstanding ++ m.proofs).map Proof.secret := by
      intro n hn q hq hmem
      rw [List.map_append] at hmem
      rcases List.mem_append.mp hmem with ho | hmq
      · exact hPB2 n (hnmem hn) q hq ho
      · exact hsecretsNe hn hq hmq
    constructor
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · have hnod := nodup_append_of houtNodup hmNodup (by
          intro x hx y hy hxy
          rcases List.mem_map.mp hy with ⟨q, hq, hqeq⟩
          have hx' : q.secret ∈ s.outstanding.map Proof.secret := by
            rw [hqeq, ← hxy]
            exact hx
          exact hPB2 m hmmem q hq hx')
        simpa [List.map_append] using hnod
      · exact hfilteredId
      · intro p hp hspent
        rcases List.mem_append.mp hp with hpo | hpm
        · exact (houtSpent p hpo) (mem_removeSecrets.mp hspent).1
        · have hmemm : p.secret ∈ m.proofs.map Proof.secret :=
            List.mem_map_of_mem hpm
          exact (mem_removeSecrets.mp hspent).2 hmemm
      · intro n hn q hq
        exact mem_removeSecrets_of_mem_of_not_mem (hpendingRemain n hn q hq)
          (hsecretsNe hn hq)
      · refine ⟨?_, ?_, hfilteredId⟩
        · intro n hn q hq
          exact mem_removeSecrets_of_mem_of_not_mem (hpendingRemain n hn q hq)
            (hsecretsNe hn hq)
        · intro n hn q hq hmem
          exact hpendingNotOut n hn q hq hmem
    · exact pendingDistinct_filter (pred := fun n => n.id != id) hPD

/-- Confirming a melt preserves the auxiliary invariant. -/
theorem confirmMelt_preserves_freshInvariant (s : MintState) (id : Nat)
    (s' : MintState) (hm : Cashu.confirmMelt s id = .ok s')
    (h : FreshInvariant s) : FreshInvariant s' := by
  rcases h with ⟨hWF, hPD⟩
  rcases hWF with ⟨houtNodup, hpendingIds, houtSpent, hpendingSpent, hPB⟩
  rcases hPB with ⟨hPB1, hPB2, hPB3⟩
  unfold Cashu.confirmMelt at hm
  split at hm
  · simp at hm
  · rename_i m hfind
    injection hm with hstate
    subst s'
    have hfilteredId :
        ((s.pending.filter (fun n => n.id != id)).map PendingMelt.id).Nodup := by
      exact List.Nodup.sublist
        (List.Sublist.map PendingMelt.id
          (List.filter_sublist (p := fun n => n.id != id) (l := s.pending)))
        hpendingIds
    have hnmem {n : PendingMelt}
        (hn : n ∈ s.pending.filter (fun n => n.id != id)) : n ∈ s.pending :=
      (List.mem_filter.mp hn).1
    constructor
    · refine ⟨houtNodup, hfilteredId, houtSpent, ?_, ?_⟩
      · intro n hn q hq
        exact hpendingSpent n (hnmem hn) q hq
      · refine ⟨?_, ?_, hfilteredId⟩
        · intro n hn q hq
          exact hpendingSpent n (hnmem hn) q hq
        · intro n hn q hq hmem
          exact hPB2 n (hnmem hn) q hq hmem
    · exact pendingDistinct_filter (pred := fun n => n.id != id) hPD

/-! ## Preservation of the keyset/binding invariant -/

/-- Pending entries with the same id are the same entry when pending ids are
pairwise distinct. -/
theorem pending_eq_of_mem_of_id_eq {s : MintState}
    (hids : (s.pending.map PendingMelt.id).Nodup)
    {a b : PendingMelt} (ha : a ∈ s.pending) (hb : b ∈ s.pending)
    (h : a.id = b.id) : a = b := by
  rcases List.mem_iff_getElem.mp ha with ⟨i, hi, hia⟩
  rcases List.mem_iff_getElem.mp hb with ⟨j, hj, hjb⟩
  have hi' : i < (s.pending.map PendingMelt.id).length := by simpa using hi
  have hj' : j < (s.pending.map PendingMelt.id).length := by simpa using hj
  have hmap : (s.pending.map PendingMelt.id)[i] =
      (s.pending.map PendingMelt.id)[j] := by
    rw [List.getElem_map (f := PendingMelt.id) (h := hi'),
      List.getElem_map (f := PendingMelt.id) (h := hj')]
    rw [hia, hjb]
    exact h
  have hij : i = j := (hids.getElem_inj (hi := hi') (hj := hj')).mp hmap
  calc
    a = s.pending[i] := hia.symm
    _ = s.pending[j] := by subst hij; rfl
    _ = b := hjb

/-- A pending secret either survives the confirmation filter or belongs to the
confirmed melt, whose proofs are already in `spent`. -/
theorem mem_pendingSecrets_filter_or_spent {s : MintState} {id : Nat}
    {m : PendingMelt}
    (hfind : s.pending.find? (fun n => n.id == id) = some m)
    (hids : (s.pending.map PendingMelt.id).Nodup)
    (hspent : ∀ p ∈ m.proofs, p.secret ∈ s.spent)
    {x : Secret} (hx : x ∈ s.pendingSecrets) :
    x ∈ (s.pending.filter (fun n => n.id != id)).flatMap PendingMelt.secrets ∨
      x ∈ s.spent := by
  rw [mem_pendingSecrets] at hx
  rcases hx with ⟨n, hn, hxn⟩
  have hmmem : m ∈ s.pending := mem_of_find?_eq_some hfind
  have hmid : m.id = id := id_eq_of_find?_eq_some hfind
  by_cases hni : n.id = id
  · right
    have hnm : n = m :=
      pending_eq_of_mem_of_id_eq hids hn hmmem (by rw [hni, hmid])
    subst n
    rcases List.mem_map.mp hxn with ⟨p, hp, hpeq⟩
    rw [← hpeq]
    exact hspent p hp
  · left
    rw [List.mem_flatMap]
    exact ⟨n, by rw [List.mem_filter]; exact ⟨hn, by simp [hni]⟩, hxn⟩

/-- A pending secret either survives the refund filter or belongs to the
refunded melt, whose proofs return to `outstanding`. -/
theorem mem_pendingSecrets_filter_or_refunded {s : MintState} {id : Nat}
    {m : PendingMelt}
    (hfind : s.pending.find? (fun n => n.id == id) = some m)
    (hids : (s.pending.map PendingMelt.id).Nodup)
    {x : Secret} (hx : x ∈ s.pendingSecrets) :
    x ∈ (s.pending.filter (fun n => n.id != id)).flatMap PendingMelt.secrets ∨
      x ∈ m.proofs.map Proof.secret := by
  rw [mem_pendingSecrets] at hx
  rcases hx with ⟨n, hn, hxn⟩
  have hmmem : m ∈ s.pending := mem_of_find?_eq_some hfind
  have hmid : m.id = id := id_eq_of_find?_eq_some hfind
  by_cases hni : n.id = id
  · right
    have hnm : n = m :=
      pending_eq_of_mem_of_id_eq hids hn hmmem (by rw [hni, hmid])
    subst n
    exact hxn
  · left
    rw [List.mem_flatMap]
    exact ⟨n, by rw [List.mem_filter]; exact ⟨hn, by simp [hni]⟩, hxn⟩

/-- The active keyset id has the V2 wire shape. -/
theorem activeKeyset_isV2 {s : MintState} (h : KeysetInvariant s) :
    isV2Id s.activeKeyset = true := by
  rcases h.2.2.1 with ⟨k, hkSome, _hkActive⟩
  change keysetOf? s s.activeKeyset = some k at hkSome
  unfold keysetOf? at hkSome
  have hkmem : k ∈ s.keysets :=
    List.mem_of_find?_eq_some
      (p := fun j : Keyset => j.id == s.activeKeyset) hkSome
  have hkid : k.id = s.activeKeyset :=
    beq_iff_eq.mp
      (List.find?_some (p := fun j : Keyset => j.id == s.activeKeyset) hkSome)
  have hkWF : k.wellFormed := h.1.2 k hkmem
  have hkId : isV2Id k.id = true := hkWF.1
  rwa [hkid] at hkId

/-- The active keyset id names a member of the keyset table. -/
theorem activeKeyset_mem {s : MintState} (h : KeysetInvariant s) :
    ∃ k ∈ s.keysets, s.activeKeyset = k.id := by
  rcases h.2.2.1 with ⟨k, hkSome, _hkActive⟩
  change keysetOf? s s.activeKeyset = some k at hkSome
  unfold keysetOf? at hkSome
  have hkmem : k ∈ s.keysets :=
    List.mem_of_find?_eq_some
      (p := fun j : Keyset => j.id == s.activeKeyset) hkSome
  have hkid : k.id = s.activeKeyset :=
    beq_iff_eq.mp
      (List.find?_some (p := fun j : Keyset => j.id == s.activeKeyset) hkSome)
  exact ⟨k, hkmem, hkid.symm⟩

/-- Minting preserves the keyset/binding invariant. -/
theorem mint_preserves_keysetInvariant (s : MintState) (deposit : Amount)
    (outputs : List Proof) (s' : MintState)
    (hm : Cashu.mint s deposit outputs = .ok s')
    (_hF : FreshInvariant s) (hK : KeysetInvariant s) :
    KeysetInvariant s' := by
  unfold Cashu.mint at hm
  split at hm
  · rename_i hvalid
    have hfresh := mintValid_outputsFresh hvalid
    injection hm with hstate
    subst s'
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [MintState.keysetsWellFormed] using hK.1
    · exact bindingsWellFormed_append_issued s s.activeKeyset outputs
        hK.2.1 hK.2.2.2 hfresh (activeKeyset_isV2 hK) (activeKeyset_mem hK)
    · simpa [ActiveKeysetPresent, activeKeyset?, keysetOf?] using hK.2.2.1
    · exact bindingsCover_mint s s.activeKeyset outputs hK.2.2.2
  · contradiction

/-- Swapping preserves the keyset/binding invariant. -/
theorem swap_preserves_keysetInvariant (s : MintState)
    (inputSecrets : List Secret) (outputs : List Proof) (s' : MintState)
    (hm : Cashu.swap s inputSecrets outputs = .ok s')
    (_hF : FreshInvariant s) (hK : KeysetInvariant s) :
    KeysetInvariant s' := by
  unfold Cashu.swap at hm
  split at hm
  · rename_i hvalid
    have hfresh := swapValid_outputsFresh hvalid
    injection hm with hstate
    subst s'
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [MintState.keysetsWellFormed] using hK.1
    · exact bindingsWellFormed_append_issued s s.activeKeyset outputs
        hK.2.1 hK.2.2.2 hfresh (activeKeyset_isV2 hK) (activeKeyset_mem hK)
    · simpa [ActiveKeysetPresent, activeKeyset?, keysetOf?] using hK.2.2.1
    · exact bindingsCover_swap s inputSecrets outputs s.activeKeyset hK.2.2.2
  · contradiction

/-- A fee-aware swap preserves the keyset/binding invariant. -/
theorem swapWithFee_preserves_keysetInvariant (s : MintState)
    (inputSecrets : List Secret) (outputs : List Proof) (fee : Nat)
    (s' : MintState)
    (hm : Cashu.swapWithFee s inputSecrets outputs fee = .ok s')
    (_hF : FreshInvariant s) (hK : KeysetInvariant s) :
    KeysetInvariant s' := by
  unfold Cashu.swapWithFee at hm
  split at hm
  · rename_i hvalid
    have hfresh := swapWithFeeValid_outputsFresh hvalid
    injection hm with hstate
    subst s'
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [MintState.keysetsWellFormed] using hK.1
    · exact bindingsWellFormed_append_issued s s.activeKeyset outputs
        hK.2.1 hK.2.2.2 hfresh (activeKeyset_isV2 hK) (activeKeyset_mem hK)
    · simpa [ActiveKeysetPresent, activeKeyset?, keysetOf?] using hK.2.2.1
    · exact bindingsCover_swap s inputSecrets outputs s.activeKeyset hK.2.2.2
  · contradiction

/-- Melting preserves the keyset/binding invariant. -/
theorem melt_preserves_keysetInvariant (s : MintState) (id : Nat)
    (inputSecrets : List Secret) (s' : MintState)
    (hm : Cashu.melt s id inputSecrets = .ok s')
    (_hF : FreshInvariant s) (hK : KeysetInvariant s) :
    KeysetInvariant s' := by
  unfold Cashu.melt at hm
  split at hm
  · rename_i _hvalid
    injection hm with hstate
    subst s'
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [MintState.keysetsWellFormed] using hK.1
    · simpa [MintState.bindingsWellFormed] using hK.2.1
    · simpa [ActiveKeysetPresent, activeKeyset?, keysetOf?] using hK.2.2.1
    · exact bindingsCover_melt s id inputSecrets hK.2.2.2
  · contradiction

/-- Confirmation preserves the keyset/binding invariant. A removed pending
proof's secret is already in `spent` by `PendingBacked`. -/
theorem confirmMelt_preserves_keysetInvariant (s : MintState) (id : Nat)
    (s' : MintState) (hm : Cashu.confirmMelt s id = .ok s')
    (hF : FreshInvariant s) (hK : KeysetInvariant s) :
    KeysetInvariant s' := by
  rcases hF with ⟨hWF, _hPD⟩
  rcases hWF with ⟨_houtNodup, hpendingIds, _houtSpent, hpendingSpent, _hPB⟩
  unfold Cashu.confirmMelt at hm
  split at hm
  · simp at hm
  · rename_i m hfind
    have hmmem : m ∈ s.pending := mem_of_find?_eq_some hfind
    injection hm with hstate
    subst s'
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [MintState.keysetsWellFormed] using hK.1
    · simpa [MintState.bindingsWellFormed] using hK.2.1
    · simpa [ActiveKeysetPresent, activeKeyset?, keysetOf?] using hK.2.2.1
    · intro e he
      change e ∈ s.proofKeyset at he
      rcases hK.2.2.2 e he with ho | hs | hp
      · left; exact ho
      · right; left; exact hs
      · rcases mem_pendingSecrets_filter_or_spent hfind hpendingIds
          (fun p hp => hpendingSpent m hmmem p hp) hp with hrem | hsp
        · right; right; exact hrem
        · right; left; exact hsp

/-- Refund preserves the keyset/binding invariant. A refunded pending proof's
secret returns to `outstanding`, and a spent secret removed from `spent` is
exactly a secret of the refunded melt. -/
theorem refund_preserves_keysetInvariant (s : MintState) (id : Nat)
    (s' : MintState) (hm : Cashu.refund s id = .ok s')
    (hF : FreshInvariant s) (hK : KeysetInvariant s) :
    KeysetInvariant s' := by
  rcases hF with ⟨hWF, _hPD⟩
  rcases hWF with ⟨_houtNodup, hpendingIds, _houtSpent, _hpendingSpent, _hPB⟩
  unfold Cashu.refund at hm
  split at hm
  · simp at hm
  · rename_i m hfind
    injection hm with hstate
    subst s'
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [MintState.keysetsWellFormed] using hK.1
    · simpa [MintState.bindingsWellFormed] using hK.2.1
    · simpa [ActiveKeysetPresent, activeKeyset?, keysetOf?] using hK.2.2.1
    · intro e he
      change e ∈ s.proofKeyset at he
      rcases hK.2.2.2 e he with ho | hs | hp
      · left
        rw [List.map_append]
        exact List.mem_append_left _ ho
      · by_cases hrem : e.1 ∈ removeSecrets s.spent m.secrets
        · right; left; exact hrem
        · left
          rw [List.map_append]
          apply List.mem_append_right
          have hmemm : e.1 ∈ m.secrets := by
            by_cases h : e.1 ∈ m.secrets
            · exact h
            · exact absurd (mem_removeSecrets.mpr ⟨hs, h⟩) hrem
          simpa [PendingMelt.secrets] using hmemm
      · rcases mem_pendingSecrets_filter_or_refunded hfind hpendingIds hp with
          hrem | hmproofs
        · right; right
          simpa [MintState.pendingSecrets] using hrem
        · left
          rw [List.map_append]
          exact List.mem_append_right _ hmproofs

/-- The full reachable-state invariant: freshness/pending structure plus the
keyset and binding tables. -/
def StateInvariant (s : MintState) : Prop :=
  FreshInvariant s ∧ KeysetInvariant s

/-- The empty state satisfies the full invariant. -/
theorem empty_stateInvariant : StateInvariant empty :=
  ⟨empty_freshInvariant, empty_keysetInvariant⟩

theorem mint_preserves_stateInvariant (s : MintState) (deposit : Amount)
    (outputs : List Proof) (s' : MintState)
    (hm : Cashu.mint s deposit outputs = .ok s')
    (h : StateInvariant s) : StateInvariant s' :=
  ⟨mint_preserves_freshInvariant s deposit outputs s' hm h.1,
    mint_preserves_keysetInvariant s deposit outputs s' hm h.1 h.2⟩

theorem swap_preserves_stateInvariant (s : MintState)
    (inputSecrets : List Secret) (outputs : List Proof) (s' : MintState)
    (hm : Cashu.swap s inputSecrets outputs = .ok s')
    (h : StateInvariant s) : StateInvariant s' :=
  ⟨swap_preserves_freshInvariant s inputSecrets outputs s' hm h.1,
    swap_preserves_keysetInvariant s inputSecrets outputs s' hm h.1 h.2⟩

theorem swapWithFee_preserves_stateInvariant (s : MintState)
    (inputSecrets : List Secret) (outputs : List Proof) (fee : Nat)
    (s' : MintState)
    (hm : Cashu.swapWithFee s inputSecrets outputs fee = .ok s')
    (h : StateInvariant s) : StateInvariant s' :=
  ⟨swapWithFee_preserves_freshInvariant s inputSecrets outputs fee s' hm h.1,
    swapWithFee_preserves_keysetInvariant s inputSecrets outputs fee s' hm h.1 h.2⟩

theorem melt_preserves_stateInvariant (s : MintState) (id : Nat)
    (inputSecrets : List Secret) (s' : MintState)
    (hm : Cashu.melt s id inputSecrets = .ok s')
    (h : StateInvariant s) : StateInvariant s' :=
  ⟨melt_preserves_freshInvariant s id inputSecrets s' hm h.1,
    melt_preserves_keysetInvariant s id inputSecrets s' hm h.1 h.2⟩

theorem refund_preserves_stateInvariant (s : MintState) (id : Nat)
    (s' : MintState) (hm : Cashu.refund s id = .ok s')
    (h : StateInvariant s) : StateInvariant s' :=
  ⟨refund_preserves_freshInvariant s id s' hm h.1,
    refund_preserves_keysetInvariant s id s' hm h.1 h.2⟩

theorem confirmMelt_preserves_stateInvariant (s : MintState) (id : Nat)
    (s' : MintState) (hm : Cashu.confirmMelt s id = .ok s')
    (h : StateInvariant s) : StateInvariant s' :=
  ⟨confirmMelt_preserves_freshInvariant s id s' hm h.1,
    confirmMelt_preserves_keysetInvariant s id s' hm h.1 h.2⟩

/-! ## Direct `WellFormed` / `PendingBacked` preservation corollaries

The auxiliary `PendingDistinct` clause is only needed by `refund`; these
corollaries expose the two requested invariants separately with the same
strong pre-state hypothesis. -/

/-- The `PendingBacked` component of the auxiliary invariant. -/
theorem FreshInvariant.pendingBacked {s : MintState} (h : FreshInvariant s) :
    PendingBacked s := by
  rcases h.1 with ⟨_, _, _, _, hPB⟩
  exact hPB

/-- The `WellFormed` component of the auxiliary invariant. -/
theorem FreshInvariant.wellFormed {s : MintState} (h : FreshInvariant s) :
    WellFormed s :=
  h.1

theorem mint_preserves_wellFormed (s : MintState) (deposit : Amount)
    (outputs : List Proof) (s' : MintState)
    (hm : Cashu.mint s deposit outputs = .ok s')
    (h : FreshInvariant s) : WellFormed s' :=
  (mint_preserves_freshInvariant s deposit outputs s' hm h).wellFormed

theorem mint_preserves_pendingBacked (s : MintState) (deposit : Amount)
    (outputs : List Proof) (s' : MintState)
    (hm : Cashu.mint s deposit outputs = .ok s')
    (h : FreshInvariant s) : PendingBacked s' :=
  (mint_preserves_freshInvariant s deposit outputs s' hm h).pendingBacked

theorem swap_preserves_wellFormed (s : MintState)
    (inputSecrets : List Secret) (outputs : List Proof) (s' : MintState)
    (hm : Cashu.swap s inputSecrets outputs = .ok s')
    (h : FreshInvariant s) : WellFormed s' :=
  (swap_preserves_freshInvariant s inputSecrets outputs s' hm h).wellFormed

theorem swap_preserves_pendingBacked (s : MintState)
    (inputSecrets : List Secret) (outputs : List Proof) (s' : MintState)
    (hm : Cashu.swap s inputSecrets outputs = .ok s')
    (h : FreshInvariant s) : PendingBacked s' :=
  (swap_preserves_freshInvariant s inputSecrets outputs s' hm h).pendingBacked

theorem swapWithFee_preserves_wellFormed (s : MintState)
    (inputSecrets : List Secret) (outputs : List Proof) (fee : Nat)
    (s' : MintState)
    (hm : Cashu.swapWithFee s inputSecrets outputs fee = .ok s')
    (h : FreshInvariant s) : WellFormed s' :=
  (swapWithFee_preserves_freshInvariant s inputSecrets outputs fee s' hm h).wellFormed

theorem swapWithFee_preserves_pendingBacked (s : MintState)
    (inputSecrets : List Secret) (outputs : List Proof) (fee : Nat)
    (s' : MintState)
    (hm : Cashu.swapWithFee s inputSecrets outputs fee = .ok s')
    (h : FreshInvariant s) : PendingBacked s' :=
  (swapWithFee_preserves_freshInvariant s inputSecrets outputs fee s' hm h).pendingBacked

theorem melt_preserves_wellFormed (s : MintState) (id : Nat)
    (inputSecrets : List Secret) (s' : MintState)
    (hm : Cashu.melt s id inputSecrets = .ok s')
    (h : FreshInvariant s) : WellFormed s' :=
  (melt_preserves_freshInvariant s id inputSecrets s' hm h).wellFormed

theorem melt_preserves_pendingBacked (s : MintState) (id : Nat)
    (inputSecrets : List Secret) (s' : MintState)
    (hm : Cashu.melt s id inputSecrets = .ok s')
    (h : FreshInvariant s) : PendingBacked s' :=
  (melt_preserves_freshInvariant s id inputSecrets s' hm h).pendingBacked

theorem refund_preserves_wellFormed (s : MintState) (id : Nat)
    (s' : MintState) (hm : Cashu.refund s id = .ok s')
    (h : FreshInvariant s) : WellFormed s' :=
  (refund_preserves_freshInvariant s id s' hm h).wellFormed

theorem refund_preserves_pendingBacked (s : MintState) (id : Nat)
    (s' : MintState) (hm : Cashu.refund s id = .ok s')
    (h : FreshInvariant s) : PendingBacked s' :=
  (refund_preserves_freshInvariant s id s' hm h).pendingBacked

theorem confirmMelt_preserves_wellFormed (s : MintState) (id : Nat)
    (s' : MintState) (hm : Cashu.confirmMelt s id = .ok s')
    (h : FreshInvariant s) : WellFormed s' :=
  (confirmMelt_preserves_freshInvariant s id s' hm h).wellFormed

theorem confirmMelt_preserves_pendingBacked (s : MintState) (id : Nat)
    (s' : MintState) (hm : Cashu.confirmMelt s id = .ok s')
    (h : FreshInvariant s) : PendingBacked s' :=
  (confirmMelt_preserves_freshInvariant s id s' hm h).pendingBacked

/-! ## Reachability closure -/

/-- Every reachable state satisfies the auxiliary invariant. -/
theorem reachable_freshInvariant (s : MintState) (h : Reachable s) :
    FreshInvariant s := by
  induction h with
  | empty => exact empty_freshInvariant
  | mint s deposit outputs s' _h hm ih =>
      exact mint_preserves_freshInvariant s deposit outputs s' hm ih
  | swap s inputSecrets outputs s' _h hm ih =>
      exact swap_preserves_freshInvariant s inputSecrets outputs s' hm ih
  | swapWithFee s inputSecrets outputs fee s' _h hm ih =>
      exact swapWithFee_preserves_freshInvariant s inputSecrets outputs fee s' hm ih
  | melt s id inputSecrets s' _h hm ih =>
      exact melt_preserves_freshInvariant s id inputSecrets s' hm ih
  | refund s id s' _h hm ih =>
      exact refund_preserves_freshInvariant s id s' hm ih
  | confirmMelt s id s' _h hm ih =>
      exact confirmMelt_preserves_freshInvariant s id s' hm ih

/-- Every reachable state satisfies the full freshness plus keyset/binding
invariant. -/
theorem reachable_stateInvariant (s : MintState) (h : Reachable s) :
    StateInvariant s := by
  induction h with
  | empty => exact empty_stateInvariant
  | mint s deposit outputs s' _h hm ih =>
      exact mint_preserves_stateInvariant s deposit outputs s' hm ih
  | swap s inputSecrets outputs s' _h hm ih =>
      exact swap_preserves_stateInvariant s inputSecrets outputs s' hm ih
  | swapWithFee s inputSecrets outputs fee s' _h hm ih =>
      exact swapWithFee_preserves_stateInvariant s inputSecrets outputs fee s' hm ih
  | melt s id inputSecrets s' _h hm ih =>
      exact melt_preserves_stateInvariant s id inputSecrets s' hm ih
  | refund s id s' _h hm ih =>
      exact refund_preserves_stateInvariant s id s' hm ih
  | confirmMelt s id s' _h hm ih =>
      exact confirmMelt_preserves_stateInvariant s id s' hm ih

/-- Every reachable state satisfies the keyset/binding invariant. -/
theorem reachable_keysetInvariant (s : MintState) (h : Reachable s) :
    KeysetInvariant s :=
  (reachable_stateInvariant s h).2

/-- **Every reachable state is well formed.** This includes outstanding-secret
distinctness, the pending/spent boundary, and `PendingBacked`. -/
theorem reachable_wellFormed (s : MintState) (h : Reachable s) :
    WellFormed s :=
  (reachable_freshInvariant s h).1

/-- **Every reachable state satisfies the pending-journal boundary.** The
freshness checks in `mintValid`, `swapValid`, and `swapWithFeeValid` remove the
secret-reuse counterexample from module 1. -/
theorem reachable_pending_backed (s : MintState) (h : Reachable s) :
    PendingBacked s := by
  rcases reachable_wellFormed s h with ⟨_, _, _, _, hPB⟩
  exact hPB

/-! ## The former secret-reuse counterexample is rejected

Module 1 exhibited a reachable state in which secret `"a"` was simultaneously
spent, locked in pending melt `7`, and re-minted into `outstanding`.  The
freshness guard now rejects that mint before any state change. -/

/-- A concrete state with secret `"a"` spent and locked in pending melt `7`. -/
def staleState : MintState :=
  { outstanding := []
    spent := ["a"]
    pending := [{ id := 7, proofs :=
      [{ amount := 10, secret := "a", signature := "sig:a" }] }]
    reserve := 0
    issued := 10
    keysets := empty.keysets
    activeKeyset := empty.activeKeyset
    proofKeyset := [] }

/-- Re-minting the spent/pending secret `"a"` fails the freshness check. -/
theorem stale_mint_rejected :
    Cashu.mint staleState 10
      [{ amount := 10, secret := "a", signature := "sig:a" }] =
        .error .invalidMint := by
  rfl

end Cashu
