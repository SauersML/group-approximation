import GroupApproximation.Algebra.PurelyInfiniteUnitFamily

/-!
# Matrix units from `n` orthogonal copies of `1`

`Algebra/PurelyInfiniteUnitFamily.lean` builds `n` pairwise orthogonal
idempotents `r 0, …, r (n-1)`, each equivalent to `1`.  This module upgrades
that to a genuine **matrix unit system** living inside `R` itself: elements
`E i j`, `i j : Fin n`, satisfying the matrix-unit relations

    `E i j * E k l = if j = k then E i l else 0`,

with `E i i` equivalent to `1` for every `i`.  No isomorphic copy of `R` or of
a matrix ring is ever built — `E i j` are literal elements of `R` — and this
is exactly the algebra `AGPStepOne`'s ring isomorphism `θ : M_n(R) → PRP`
needs as its input.

## The construction

For each `i`, `r i ~ 1` gives a *normalised* isometry pair `s i, t i` with
`t i * s i = 1` and `s i * t i = r i` (`exists_normalized_isometry`, applied
with `1` as the ambient idempotent).  Set `E i j := s i * t j`.

The diagonal is right: `E i i = s i * t i = r i ~ 1`.  The off-diagonal
relation needs `t i * s j = 0` for `i ≠ j`, which follows from orthogonality of
the `r`'s alone: `s j = r j * s j` and `t i = t i * r i` (both immediate from
the normalised pair), so

    `t i * s j = (t i * r i) * s j = t i * (r i * s j) = t i * ((r i * r j) * s j) = 0`.
-/

namespace GroupApproximation
namespace MFQuotientUnits

variable {R : Type*} [Ring R]

/-- **A matrix unit system on `n` copies of `1`.**  Literal elements of `R`,
satisfying the matrix-unit relations, with each diagonal entry equivalent to
`1`. -/
theorem exists_matrixUnitSystem (hR : IsPurelyInfiniteSimpleRing R) (n : ℕ) :
    ∃ E : Fin n → Fin n → R,
      (∀ i j k l, E i j * E k l = if j = k then E i l else 0) ∧
        ∀ i, IsEquivalentIdempotent R (E i i) 1 := by
  obtain ⟨r, hridem, hrortho, hrequiv⟩ := exists_orthogonal_unit_family hR n
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
  have hcross : ∀ i j : Fin n, i ≠ j → t i * s j = 0 := fun i j hij => by
    have h1 : r i * s j = 0 := by
      calc r i * s j = r i * (r j * s j) := by rw [hrs j]
        _ = (r i * r j) * s j := by noncomm_ring
        _ = 0 * s j := by rw [hrortho i j hij]
        _ = 0 := zero_mul _
    calc t i * s j = (t i * r i) * s j := by rw [htr i]
      _ = t i * (r i * s j) := by noncomm_ring
      _ = t i * 0 := by rw [h1]
      _ = 0 := mul_zero _
  refine ⟨fun i j => s i * t j, fun i j k l => ?_, fun i => ?_⟩
  · by_cases hjk : j = k
    · subst hjk
      rw [if_pos rfl]
      calc s i * t j * (s j * t l) = s i * (t j * s j) * t l := by noncomm_ring
        _ = s i * 1 * t l := by rw [hts j]
        _ = s i * t l := by rw [mul_one]
    · rw [if_neg hjk]
      calc s i * t j * (s k * t l) = s i * (t j * s k) * t l := by noncomm_ring
        _ = s i * 0 * t l := by rw [hcross j k hjk]
        _ = 0 := by simp
  · show IsEquivalentIdempotent R (s i * t i) 1
    rw [hst i]
    exact hrequiv i

end MFQuotientUnits
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.MFQuotientUnits.exists_matrixUnitSystem
