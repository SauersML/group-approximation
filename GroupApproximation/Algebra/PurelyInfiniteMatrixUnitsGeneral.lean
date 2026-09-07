import GroupApproximation.Algebra.PurelyInfiniteSandwich

/-!
# Matrix-unit witnesses from any orthogonal family equivalent to `1`

`Algebra/PurelyInfiniteMatrixUnits.lean`'s witness construction is tied to the
specific `n`-fold family `Algebra/PurelyInfiniteUnitFamily.lean` builds
globally.  `AGPStepOne`'s own family is assembled from *two* different
sources (its `r_1 = 1 - e + f`, built by hand, and its `r_2, …, r_n`,
transported into `e - f`), so the witness construction needs to work from
**any** orthogonal family equivalent to `1`, not just the one specific
construction that happens to produce one.

This module is `PurelyInfiniteMatrixUnits.lean`'s witness argument, factored
out to take the family `r : Fin n → R` as a hypothesis instead of building it.
-/

namespace GroupApproximation
namespace MFQuotientUnits

variable {R : Type*} [Ring R]

/-- **Matrix-unit witnesses from any pairwise-orthogonal family equivalent to
`1`.** -/
theorem exists_matrixUnitWitnesses_of_family {n : ℕ} {r : Fin n → R}
    (hridem : ∀ i, IsIdempotentElem (r i))
    (hrortho : ∀ i j : Fin n, i ≠ j → r i * r j = 0)
    (hrequiv : ∀ i, IsEquivalentIdempotent R (r i) 1) :
    ∃ s t : Fin n → R, (∀ i, t i * s i = 1) ∧
      (∀ i j : Fin n, i ≠ j → t i * s j = 0) ∧ ∀ i, s i * t i = r i := by
  have hchoice : ∀ i : Fin n, ∃ s t : R, t * s = 1 ∧ s * t = r i ∧
      (1 : R) * s = s ∧ s * 1 = s ∧ (1 : R) * t = t ∧ t * 1 = t := fun i =>
    exists_normalized_isometry IsIdempotentElem.one (hridem i) (one_mul (r i))
      (mul_one (r i)) (hrequiv i).symm
  choose s t hts hst hes hse het hte using hchoice
  have hrs : ∀ k, r k * s k = s k := fun k => by
    calc r k * s k = (s k * t k) * s k := by rw [hst k]
      _ = s k * (t k * s k) := by noncomm_ring
      _ = s k * 1 := by rw [hts k]
      _ = s k := hse k
  have htr : ∀ j, t j * r j = t j := fun j => by
    calc t j * r j = t j * (s j * t j) := by rw [hst j]
      _ = (t j * s j) * t j := by noncomm_ring
      _ = 1 * t j := by rw [hts j]
      _ = t j := het j
  refine ⟨s, t, hts, fun i j hij => ?_, hst⟩
  have h1 : r i * s j = 0 := by
    calc r i * s j = r i * (r j * s j) := by rw [hrs j]
      _ = (r i * r j) * s j := by noncomm_ring
      _ = 0 * s j := by rw [hrortho i j hij]
      _ = 0 := zero_mul _
  calc t i * s j = (t i * r i) * s j := by rw [htr i]
    _ = t i * (r i * s j) := by noncomm_ring
    _ = t i * 0 := by rw [h1]
    _ = 0 := mul_zero _

end MFQuotientUnits
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.MFQuotientUnits.exists_matrixUnitWitnesses_of_family
