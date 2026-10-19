import CashuLean.Basic

/-!
# CashuLean.Freshness — output freshness checks

This module adds the output-freshness predicate that closes an earlier gap:
`mint`, `swap`, and `swapWithFee` used to append
caller-supplied outputs without checking whether an output secret was already
spent, outstanding, or locked in a pending melt.

`outputsFresh` is the executable `Bool` predicate used by the validators in
`CashuLean.Mint` and `CashuLean.Fees`.  `OutputsFresh` is its propositional
specification:

1. the output secrets are pairwise distinct;
2. no output secret occurs in `spent`;
3. no output secret occurs in the secrets of `outstanding`;
4. no output secret occurs as a proof secret of a pending melt.

The helper lemmas below are pure list/state facts.  Preservation of the
invariants lives in `CashuLean.Invariants`, which is the first module that can
import the operations.

No proof holes or kernel escape hatches are used.
-/

namespace Cashu

/-! ## Basic membership helpers -/

/-- Boolean membership agrees with list membership. -/
theorem contains_eq_true {xs : List Secret} {x : Secret} :
    contains xs x = true ↔ x ∈ xs := by
  unfold contains
  rw [List.any_eq_true]
  constructor
  · rintro ⟨y, hy, hbe⟩
    rw [beq_iff_eq] at hbe
    exact hbe ▸ hy
  · intro hx
    exact ⟨x, hx, by rw [beq_iff_eq]⟩

/-- Boolean non-membership agrees with list non-membership. -/
theorem contains_eq_false {xs : List Secret} {x : Secret} :
    contains xs x = false ↔ x ∉ xs := by
  rw [Bool.eq_false_iff]
  constructor
  · intro h hx
    exact h (contains_eq_true.mpr hx)
  · intro hx htrue
    exact hx (contains_eq_true.mp htrue)

/-- Membership in the proofs selected by a secret list. -/
theorem mem_selectBySecret {ps : List Proof} {secrets : List Secret}
    {p : Proof} :
    p ∈ selectBySecret ps secrets ↔
      p ∈ ps ∧ contains secrets p.secret = true := by
  simp [selectBySecret, List.mem_filter]

/-- Membership in the proofs rejected by a secret list. -/
theorem mem_rejectBySecret {ps : List Proof} {secrets : List Secret}
    {p : Proof} :
    p ∈ rejectBySecret ps secrets ↔
      p ∈ ps ∧ contains secrets p.secret = false := by
  simp [rejectBySecret, List.mem_filter]

/-- A proof kept by `rejectBySecret` does not carry a rejected secret. -/
theorem secret_not_mem_of_mem_rejectBySecret {ps : List Proof}
    {secrets : List Secret} {p : Proof}
    (h : p ∈ rejectBySecret ps secrets) : p.secret ∉ secrets := by
  exact contains_eq_false.mp (mem_rejectBySecret.mp h).2

/-- A rejected proof's secret is an outstanding secret. -/
theorem mem_outstanding_of_mem_rejectBySecret {ps : List Proof}
    {secrets : List Secret} {x : Secret}
    (h : x ∈ (rejectBySecret ps secrets).map Proof.secret) :
    x ∈ ps.map Proof.secret := by
  rcases List.mem_map.mp h with ⟨p, hp, hpeq⟩
  exact hpeq ▸ List.mem_map_of_mem (mem_rejectBySecret.mp hp).1

/-- A proof selected by `selectBySecret` carries a selected secret. -/
theorem secret_mem_of_mem_selectBySecret {ps : List Proof}
    {secrets : List Secret} {p : Proof}
    (h : p ∈ selectBySecret ps secrets) : p.secret ∈ secrets := by
  exact contains_eq_true.mp (mem_selectBySecret.mp h).2

/-- Membership of a secret in the flattened pending journal. -/
theorem mem_pendingSecrets {s : MintState} {x : Secret} :
    x ∈ s.pendingSecrets ↔ ∃ m, m ∈ s.pending ∧ x ∈ m.secrets := by
  simp [MintState.pendingSecrets, List.mem_flatMap]

/-- A proof's secret is a pending secret exactly when its secret occurs in the
proofs of some pending melt. -/
theorem mem_pendingSecrets_iff {s : MintState} {p : Proof} :
    p.secret ∈ s.pendingSecrets ↔
      ∃ m, m ∈ s.pending ∧ p.secret ∈ m.secrets :=
  mem_pendingSecrets

/-- A proof in a pending melt contributes its secret to `pendingSecrets`. -/
theorem mem_pendingSecrets_of_mem_proofs {s : MintState} {m : PendingMelt}
    {p : Proof} (hm : m ∈ s.pending) (hp : p ∈ m.proofs) :
    p.secret ∈ s.pendingSecrets := by
  rw [mem_pendingSecrets]
  exact ⟨m, hm, List.mem_map_of_mem hp⟩

/-! ## Output freshness -/

/-- The secrets carried by a list of output proofs. -/
def outputSecrets (outputs : List Proof) : List Secret :=
  outputs.map Proof.secret

/-- Propositional specification of output freshness. -/
def OutputsFresh (s : MintState) (outputs : List Proof) : Prop :=
  (outputs.map Proof.secret).Nodup ∧
  (∀ p ∈ outputs, p.secret ∉ s.spent) ∧
  (∀ p ∈ outputs, p.secret ∉ s.outstanding.map Proof.secret) ∧
  (∀ p ∈ outputs, p.secret ∉ s.pendingSecrets)

/-- Executable output-freshness check used by the output-producing validators.

It requires the four conditions of `OutputsFresh`: pairwise-distinct output
secrets, and no output secret in `spent`, in `outstanding`, or in the pending
melt journal. -/
def outputsFresh (s : MintState) (outputs : List Proof) : Bool :=
  decide ((outputs.map Proof.secret).Nodup) &&
  outputs.all (fun p => !contains s.spent p.secret) &&
  outputs.all (fun p => !contains (s.outstanding.map Proof.secret) p.secret) &&
  outputs.all (fun p => !contains s.pendingSecrets p.secret)

/-- The executable check is exactly the four-clause specification. -/
theorem outputsFresh_spec (s : MintState) (outputs : List Proof) :
    outputsFresh s outputs = true ↔ OutputsFresh s outputs := by
  simp [outputsFresh, OutputsFresh, List.all_eq_true, contains_eq_false,
    and_assoc]

/-- Fresh outputs have pairwise-distinct secrets. -/
theorem outputsFresh_nodup {s : MintState} {outputs : List Proof}
    (h : outputsFresh s outputs = true) :
    (outputSecrets outputs).Nodup :=
  (outputsFresh_spec s outputs).mp h |>.1

/-- Fresh outputs avoid the spent set. -/
theorem outputsFresh_not_mem_spent {s : MintState} {outputs : List Proof}
    (h : outputsFresh s outputs = true) :
    ∀ p ∈ outputs, p.secret ∉ s.spent :=
  (outputsFresh_spec s outputs).mp h |>.2.1

/-- Fresh outputs avoid the outstanding set. -/
theorem outputsFresh_not_mem_outstanding {s : MintState} {outputs : List Proof}
    (h : outputsFresh s outputs = true) :
    ∀ p ∈ outputs, p.secret ∉ outputSecrets s.outstanding :=
  (outputsFresh_spec s outputs).mp h |>.2.2.1

/-- Fresh outputs avoid every pending-melt proof secret. -/
theorem outputsFresh_not_mem_pending {s : MintState} {outputs : List Proof}
    (h : outputsFresh s outputs = true) :
    ∀ p ∈ outputs, p.secret ∉ s.pendingSecrets :=
  (outputsFresh_spec s outputs).mp h |>.2.2.2

/-- A filtered proof list inherits secret-distinctness from its source. -/
theorem nodup_outputSecrets_filter {ps : List Proof} {pred : Proof → Bool}
    (h : (outputSecrets ps).Nodup) :
    (outputSecrets (ps.filter pred)).Nodup := by
  exact List.Nodup.sublist
    (List.Sublist.map Proof.secret (List.filter_sublist (p := pred) (l := ps))) h

/-- Appending two secret lists is `Nodup` when both parts are and they are
disjoint. -/
theorem nodup_append_of {xs ys : List Secret} (hx : xs.Nodup) (hy : ys.Nodup)
    (hd : ∀ x ∈ xs, ∀ y ∈ ys, x ≠ y) : (xs ++ ys).Nodup :=
  List.nodup_append.mpr ⟨hx, hy, hd⟩

/-! ## Pending-journal distinctness

`WellFormed` and `PendingBacked` do not record that different pending melts
carry disjoint proof secrets.  That fact is needed when a refund moves one
melt's proofs back into `outstanding` while other melts remain pending, so it
is kept as an auxiliary invariant.  It holds for all reachable states because
`meltValid` rejects inputs that occur in any existing pending melt. -/

/-- Auxiliary pending-journal structure:

* every pending melt has pairwise-distinct proof secrets;
* different pending melts have disjoint proof secrets. -/
def PendingDistinct (s : MintState) : Prop :=
  (∀ m ∈ s.pending, (m.proofs.map Proof.secret).Nodup) ∧
  (∀ m ∈ s.pending, ∀ n ∈ s.pending, m ≠ n →
    ∀ x ∈ m.proofs.map Proof.secret, x ∉ n.proofs.map Proof.secret)

/-- A pending melt's own proof secrets are distinct when the whole journal's
secrets are distinct. -/
theorem nodup_secrets_of_pendingDistinct {s : MintState}
    (h : PendingDistinct s) {m : PendingMelt} (hm : m ∈ s.pending) :
    (m.proofs.map Proof.secret).Nodup :=
  h.1 m hm

/-- Removing pending entries preserves `PendingDistinct`. -/
theorem pendingDistinct_filter {s : MintState} {pred : PendingMelt → Bool}
    (h : PendingDistinct s) : PendingDistinct { s with pending := s.pending.filter pred } := by
  rcases h with ⟨hnodup, hdisj⟩
  constructor
  · intro m hm
    exact hnodup m (List.mem_filter.mp hm).1
  · intro m hm n hn hne x hx
    exact hdisj m (List.mem_filter.mp hm).1 n (List.mem_filter.mp hn).1 hne x hx

/-- A distinctness fact for a pending melt that is not the removed one. -/
theorem pendingDistinct_ne_secrets {s : MintState} (h : PendingDistinct s)
    {m n : PendingMelt} (hm : m ∈ s.pending) (hn : n ∈ s.pending)
    (hne : m ≠ n) {x : Secret} (hx : x ∈ m.proofs.map Proof.secret) :
    x ∉ n.proofs.map Proof.secret :=
  h.2 m hm n hn hne x hx

end Cashu
