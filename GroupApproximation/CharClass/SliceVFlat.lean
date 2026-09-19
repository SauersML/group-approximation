import GroupApproximation.CharClass.LIXVDecomposition
import GroupApproximation.CharClass.LemmaTwoTopClass
import GroupApproximation.CharClass.SliceReindex

/-!
# The decomposition of `V`, flattened to a range

`cc-lix-odd`'s `Vmat_eq_sum_lines` writes `V` as a sum over `Fin 3 ⊕ HBlk dd`,
which is the natural index: three trivial summands, then one block per projective
factor carrying the same tautological line `dd j` times.  The splitting principle
consumes a family over `Finset.range r`.  This file is the equivalence between the
two and the flattened statement.

The flattening is done once, here, on the consuming side, as `cc-lix-odd` asked.
The family is total on `ℕ` and zero off the range, so no partial function or
subtype appears in the statement and the sum is an honest `Finset.range` sum.

## Main declarations

* `card_vIndex`, `vIndexEquiv` — the index has cardinality `lixRank dd`.
* `vLineFlat` — the family of lines, indexed by a natural.
* `Vmat_eq_sum_range` — **the decomposition over `Finset.range (lixRank dd)`.**
* `trace_vLineFlat` — every line in range has trace one.
-/

set_option autoImplicit false

namespace GroupApproximation.CharClass

open scoped Matrix
open GroupApproximation.STW59

noncomputable section

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-- The index of the decomposition has cardinality the rank. -/
theorem card_vIndex (dd : Fin ℓ → ℕ) :
    Fintype.card (Fin 3 ⊕ HBlk dd) = lixRank dd := by
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_sigma, lixRank]
  simp only [Fintype.card_fin]
  omega

/-- The equivalence with a flat range of that size. -/
def vIndexEquiv (dd : Fin ℓ → ℕ) : (Fin 3 ⊕ HBlk dd) ≃ Fin (lixRank dd) :=
  Fintype.equivFinOfCardEq (card_vIndex dd)

/-- The lines of the decomposition, indexed by a natural and zero off the range. -/
def vLineFlat (dd : Fin ℓ → ℕ) (m : baseM dd) (l : ℕ) :
    Matrix (VIdx dd) (VIdx dd) ℂ :=
  if h : l < lixRank dd then vLine ((vIndexEquiv dd).symm ⟨l, h⟩) m else 0

theorem vLineFlat_apply_equiv (dd : Fin ℓ → ℕ) (m : baseM dd) (b : Fin 3 ⊕ HBlk dd) :
    vLineFlat dd m ((vIndexEquiv dd b : Fin (lixRank dd)) : ℕ) = vLine b m := by
  have hlt : ((vIndexEquiv dd b : Fin (lixRank dd)) : ℕ) < lixRank dd :=
    (vIndexEquiv dd b).isLt
  have hb : (vIndexEquiv dd).symm ⟨((vIndexEquiv dd b : Fin (lixRank dd)) : ℕ), hlt⟩ = b := by
    rw [Fin.eta]
    exact (vIndexEquiv dd).symm_apply_apply b
  rw [vLineFlat, dif_pos hlt, hb]

/-- **The decomposition, over a flat range.** -/
theorem Vmat_eq_sum_range (m : baseM dd) :
    Vmat m = ∑ l ∈ Finset.range (lixRank dd), vLineFlat dd m l := by
  rw [sum_range_of_equiv (lixRank dd) (vIndexEquiv dd) (fun b => vLine b m)
    (vLineFlat dd m) (vLineFlat_apply_equiv dd m)]
  exact Vmat_eq_sum_lines m

/-- Every line in range has trace one. -/
theorem trace_vLineFlat (m : baseM dd) {l : ℕ} (hl : l < lixRank dd) :
    Matrix.trace (vLineFlat dd m l) = 1 := by
  rw [vLineFlat, dif_pos hl]
  exact trace_vLine _ m

end

end GroupApproximation.CharClass
