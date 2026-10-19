import CashuLean.Mint

/-!
# CashuLean.Fees

NUT-02 input-fee arithmetic and a fee-aware swap.

## What is modeled

NUT-02 charges a fee for every proof spent as an input. The reference formula
is

```
fee = ceil((sum of input_fee_ppk over all inputs) / 1000)
```

where `input_fee_ppk` is a property of the keyset that issued each proof.

Two forms are modeled:

- `feeFor ppk ps` is the wave-1 single-keyset formula, kept for compatibility:
  one `input_fee_ppk` value applies to every proof.
- `feeForKeysets s ps` is the keyset-aware form: it looks up each proof's
  mint-side binding in `s.proofKeyset`, resolves the bound keyset, sums that
  keyset's `input_fee_ppk`, and then ceiling-divides by 1000. It returns
  `none` if any proof is unbound or its keyset is unknown, so callers fail
  closed.

In the single-keyset case, the NUT-02 numerator is the sum of the per-input
`input_fee_ppk` values, which is `ps.length * ppk` because every proof
contributes the same `ppk`:

```
feeFor ppk ps = (ps.length * ppk + 999) / 1000
```

The `+ 999` then `/ 1000` is the ceiling division used by NUT-02, so the
result is the smallest integer greater than or equal to
`ps.length * ppk / 1000`. `feeForKeysets_eq_feeFor` proves that the
keyset-aware form reduces to `feeFor` when every input is bound to the same
known keyset.

## What is *not* proved

There is deliberately no bound `feeFor ppk ps ≤ sumProofs ps` for arbitrary
`ppk`: with `ppk = 2000` and a single proof of amount `1`, the fee is
`(1 * 2000 + 999) / 1000 = 2`, which exceeds the input's face value. A real
mint would reject such a transaction, but that rejection is a wallet / mint
policy precondition, not a consequence of the ceiling formula. The fee lower
bound that *is* true is only `feeFor ppk ps > 0` when the input list is
non-empty and `ppk` is positive.

## Fee-aware swap

`swapWithFee` is `swap` with two extra checks: the outputs plus the fee must
equal the face value of the selected inputs, and the caller-supplied `fee`
must equal `feeForKeysets` on the selected inputs. The mint keeps the fee: the
reserve is unchanged while outstanding liability falls by `fee`. No change
outputs (NUT-08) are modeled.
-/

namespace Cashu

/-! ## NUT-02 input fee (single keyset) -/

/-- NUT-02 input fee for a single keyset, in the mint's smallest unit.

`ppk` is the keyset's `input_fee_ppk`. Every proof contributes `ppk`, so the
numerator is `ps.length * ppk`; the fee is the ceiling of that divided by 1000,
computed with integer arithmetic as `(ps.length * ppk + 999) / 1000`.

This compatibility function is single-keyset: one `ppk` applies to every
proof. `feeForKeysets` below is the keyset-aware multi-keyset form. -/
def feeFor (ppk : Nat) (ps : List Proof) : Nat :=
  (ps.length * ppk + 999) / 1000

/-! ## NUT-02 input fee across keysets -/

/-- The un-rounded numerator contribution of a proof list: sum each input's
keyset `input_fee_ppk`, failing closed on an unbound proof or unknown keyset. -/
def inputFeePpkSum (s : MintState) (ps : List Proof) : Option Nat :=
  match ps with
  | [] => some 0
  | p :: rest =>
      match proofKeyset? s p, inputFeePpkSum s rest with
      | some kid, some acc =>
          match keysetOf? s kid with
          | some k => some (k.inputFeePpk + acc)
          | none => none
      | _, _ => none

/-- NUT-02 multi-keyset input fee: sum each input's `input_fee_ppk`, then
ceil-divide by 1000 with `(sum + 999) / 1000`. `none` if any input is unbound
or its keyset is unknown, so callers fail closed. -/
def feeForKeysets (s : MintState) (ps : List Proof) : Option Nat :=
  (inputFeePpkSum s ps).map (fun n => (n + 999) / 1000)

/-- When every proof is bound to the same known keyset, the raw numerator is
`ps.length * inputFeePpk`. -/
theorem inputFeePpkSum_eq (s : MintState) (k : Keyset) (ps : List Proof)
    (hk : keysetOf? s k.id = some k)
    (hb : ∀ p ∈ ps, proofKeyset? s p = some k.id) :
    inputFeePpkSum s ps = some (ps.length * k.inputFeePpk) := by
  induction ps with
  | nil => simp [inputFeePpkSum]
  | cons p ps ih =>
      have hp : proofKeyset? s p = some k.id := hb p (by simp)
      have hb' : ∀ q ∈ ps, proofKeyset? s q = some k.id := by
        intro q hq
        exact hb q (by simp [hq])
      have ih' := ih hb'
      simp [inputFeePpkSum, hp, hk, ih']
      rw [Nat.succ_mul]
      omega

/-- In the single-keyset case the multi-keyset fee agrees with `feeFor`. -/
theorem feeForKeysets_eq_feeFor (s : MintState) (k : Keyset) (ps : List Proof)
    (hk : keysetOf? s k.id = some k)
    (hb : ∀ p ∈ ps, proofKeyset? s p = some k.id) :
    feeForKeysets s ps = some (feeFor k.inputFeePpk ps) := by
  unfold feeForKeysets feeFor
  rw [inputFeePpkSum_eq s k ps hk hb]
  rfl

/-- An empty input list incurs no fee. -/
theorem feeFor_nil (ppk : Nat) : feeFor ppk [] = 0 := by
  simp [feeFor]

/-- A zero `input_fee_ppk` incurs no fee, whatever the inputs. -/
theorem feeFor_zero_ppk (ps : List Proof) : feeFor 0 ps = 0 := by
  simp [feeFor]

/-- A non-empty input list and a positive `input_fee_ppk` give a positive fee.

The ceiling division guarantees at least one unit is charged as soon as the
numerator is positive. -/
theorem feeFor_pos (ppk : Nat) (ps : List Proof)
    (hlen : ps.length > 0) (hppk : ppk > 0) : feeFor ppk ps > 0 := by
  unfold feeFor
  have hprod : 0 < ps.length * ppk := Nat.mul_pos hlen hppk
  have hnum : 1000 ≤ ps.length * ppk + 999 := by
    have h1 : 1 ≤ ps.length * ppk := hprod
    exact Nat.add_le_add_right h1 999
  exact Nat.div_pos hnum (by decide)

/-- The fee is monotone in `input_fee_ppk` for a fixed input list. -/
theorem feeFor_mono_ppk (ps : List Proof) {ppk ppk' : Nat} (h : ppk ≤ ppk') :
    feeFor ppk ps ≤ feeFor ppk' ps := by
  unfold feeFor
  apply Nat.div_le_div_right
  exact Nat.add_le_add_right (Nat.mul_le_mul_left (ps.length) h) 999

/-- The fee is monotone in the number of inputs for a fixed
`input_fee_ppk`. -/
theorem feeFor_mono_length (ppk : Nat) {ps qs : List Proof}
    (h : ps.length ≤ qs.length) :
    feeFor ppk ps ≤ feeFor ppk qs := by
  unfold feeFor
  apply Nat.div_le_div_right
  exact Nat.add_le_add_right (Nat.mul_le_mul_right ppk h) 999

/-- Combined monotonicity: increasing either the number of inputs or the fee
rate cannot decrease the fee. -/
theorem feeFor_mono {ps qs : List Proof} {ppk ppk' : Nat}
    (hlen : ps.length ≤ qs.length) (hppk : ppk ≤ ppk') :
    feeFor ppk ps ≤ feeFor ppk' qs :=
  Nat.le_trans (feeFor_mono_ppk ps hppk) (feeFor_mono_length ppk' hlen)

/-! ## Fee-aware swap -/

/-- A fee-aware swap is valid when the ordinary swap preconditions hold and the
output total plus the fee equals the face value of the selected inputs.

The preconditions are the same as `swapValid`: every supplied secret is known,
unspent, and not pending in a melt; every selected input is keyset-bound;
outputs are active-keyset-supported, positive, and fresh. The additional
equations are NUT-02's `sum(inputs) - fees == sum(outputs)`, written additively
to avoid truncated subtraction, and `fee = feeForKeysets` on the selected
inputs. -/
def swapWithFeeValid (s : MintState) (secrets : List Secret)
    (outputs : List Proof) (fee : Nat) : Bool :=
  allKnown s secrets && noneSpent s secrets && nonePending s secrets &&
    inputsBound s secrets && outputsValid s outputs &&
    allPositive outputs &&
    (sumProofs outputs + fee == sumProofs (selectBySecret s.outstanding secrets)) &&
    (feeForKeysets s (selectBySecret s.outstanding secrets) == some fee) &&
    outputsFresh s outputs

/-- The freshness clause of `swapWithFeeValid`. -/
theorem swapWithFeeValid_outputsFresh {s : MintState}
    {secrets : List Secret} {outputs : List Proof} {fee : Nat}
    (h : swapWithFeeValid s secrets outputs fee = true) :
    outputsFresh s outputs = true := by
  simp [swapWithFeeValid] at h
  exact h.2

/-- The known-input clause of `swapWithFeeValid`. -/
theorem swapWithFeeValid_allKnown {s : MintState}
    {secrets : List Secret} {outputs : List Proof} {fee : Nat}
    (h : swapWithFeeValid s secrets outputs fee = true) :
    allKnown s secrets = true := by
  simp [swapWithFeeValid] at h
  exact h.1.1.1.1.1.1.1.1

/-- The keyset-binding clause of `swapWithFeeValid`. -/
theorem swapWithFeeValid_inputsBound {s : MintState}
    {secrets : List Secret} {outputs : List Proof} {fee : Nat}
    (h : swapWithFeeValid s secrets outputs fee = true) :
    inputsBound s secrets = true := by
  simp [swapWithFeeValid] at h
  exact h.1.1.1.1.1.2

/-- Spend `inputSecrets`, issue `outputs`, and retain `fee` in the reserve.

The selected inputs leave `outstanding`; their secrets are appended to
`spent`, exactly as in `swap`. The outputs are issued, but their total is the
input total minus `fee`. The reserve is not changed: the fee was already
backing the destroyed inputs, and destroying `fee` units of liability while
keeping the reserve turns that amount into mint surplus.

The caller supplies `fee`, and validation requires it to equal
`feeForKeysets s (selectBySecret s.outstanding inputSecrets)`. Thus the
operation rejects an underpaid or overpaid fee, not merely a fee that breaks
the value equation. Change outputs (NUT-08) are out of scope. -/
def swapWithFee (s : MintState) (inputSecrets : List Secret)
    (outputs : List Proof) (fee : Nat) : Except MintError MintState :=
  if swapWithFeeValid s inputSecrets outputs fee then
    .ok { s with
      outstanding := rejectBySecret s.outstanding inputSecrets ++ outputs
      spent := inputSecrets ++ s.spent
      proofKeyset := issuedBindings s.activeKeyset outputs ++ s.proofKeyset }
  else .error .invalidSwap

/-- A successful fee-aware swap does not change the reserve. The fee stays in
the reserve by construction. -/
theorem reserve_swapWithFee (s : MintState) (inputSecrets : List Secret)
    (outputs : List Proof) (fee : Nat) (s' : MintState)
    (hm : swapWithFee s inputSecrets outputs fee = .ok s') :
    s'.reserve = s.reserve := by
  unfold swapWithFee at hm
  split at hm
  · injection hm with hstate
    subst s'
    rfl
  · contradiction

/-- **Exact liability accounting for a fee-aware swap.** If the call succeeds,
the new liability plus the retained fee equals the old liability.

This is the precise statement behind solvency preservation: the fee is not
created from nothing, it is a reduction of outstanding liability. -/
theorem liability_swapWithFee (s : MintState) (inputSecrets : List Secret)
    (outputs : List Proof) (fee : Nat) (s' : MintState)
    (hm : swapWithFee s inputSecrets outputs fee = .ok s') :
    liability s' + fee = liability s := by
  unfold swapWithFee at hm
  split at hm
  · rename_i hvalid
    injection hm with hstate
    subst s'
    have heq : sumProofs outputs + fee =
        sumProofs (selectBySecret s.outstanding inputSecrets) := by
      have h := hvalid
      simp [swapWithFeeValid] at h
      exact h.1.1.2
    have hpart := sumProofs_select_add_reject s.outstanding inputSecrets
    dsimp only [liability]
    rw [sumProofs_append]
    calc
      (sumProofs (rejectBySecret s.outstanding inputSecrets) +
          sumProofs outputs) + fee
          = sumProofs (rejectBySecret s.outstanding inputSecrets) +
              (sumProofs outputs + fee) := Nat.add_assoc _ _ _
      _ = sumProofs (rejectBySecret s.outstanding inputSecrets) +
              sumProofs (selectBySecret s.outstanding inputSecrets) := by
            rw [heq]
      _ = sumProofs (selectBySecret s.outstanding inputSecrets) +
              sumProofs (rejectBySecret s.outstanding inputSecrets) :=
            Nat.add_comm _ _
      _ = sumProofs s.outstanding := hpart
  · contradiction

/-- **Solvency is preserved by a fee-aware swap.** The reserve is unchanged,
while liability drops by the retained fee (or stays equal when `fee = 0`), so
a reserve that covered the old liability covers the new one.

The hypothesis `s.reserve ≥ liability s` is the same as for the five wave-0
solvency theorems; no extra precondition on `fee` is needed. -/
theorem swapWithFee_preserves_solvency (s : MintState)
    (inputSecrets : List Secret) (outputs : List Proof) (fee : Nat)
    (s' : MintState) (hm : swapWithFee s inputSecrets outputs fee = .ok s')
    (hs : s.reserve ≥ liability s) :
    s'.reserve ≥ liability s' := by
  have hliab := liability_swapWithFee s inputSecrets outputs fee s' hm
  have hres := reserve_swapWithFee s inputSecrets outputs fee s' hm
  have hle : liability s' ≤ liability s := by
    calc
      liability s' ≤ liability s' + fee := Nat.le_add_right _ _
      _ = liability s := hliab
  rw [hres]
  exact Nat.le_trans hle hs

end Cashu
