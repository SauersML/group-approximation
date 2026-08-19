import GroupApproximation.Analysis.StateExtension

/-!
# Positive functionals are hermitian

Toward proof-ledger row `RE.05` (the Lance debt).  The Krein extension of
`Analysis/StateExtension.lean` produces a functional that is nonnegative on
positives; the Arveson reconstruction also needs it to be **hermitian** —
`Φ (star y) = conj (Φ y)` — so that the extended operator-valued map
commutes with the star.  This is the classical argument: a self-adjoint
element is squeezed between `±‖a‖·1`, so its value is a difference of
nonnegative reals, and a general element splits into self-adjoint real and
imaginary parts (`StateExtension.rePart`/`imPart`, already in the tree).

## Manuscript status

Infrastructure for the Lance lane; certifies no manuscript step on its own.
`RE.05` remains conditional until the full compression statement lands.
-/

namespace GroupApproximation
namespace StateExtension

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A functional that is nonnegative on positives is real on self-adjoint
elements. -/
theorem real_on_selfAdjoint_of_nonneg (Φ : A →ₗ[ℂ] ℂ)
    (hpos : ∀ a : A, 0 ≤ a → ∃ r : ℝ, 0 ≤ r ∧ Φ a = r)
    {a : A} (ha : IsSelfAdjoint a) : ∃ t : ℝ, Φ a = t := by
  have h1 : a ≤ algebraMap ℝ A ‖a‖ := ha.le_algebraMap_norm_self
  obtain ⟨r1, _, hΦ1⟩ := hpos _ (sub_nonneg.mpr h1)
  obtain ⟨r0, _, hΦ0⟩ := hpos 1 (by simpa only [star_one, one_mul] using star_mul_self_nonneg (1 : A))
  have halg : Φ (algebraMap ℝ A ‖a‖) = (‖a‖ : ℂ) * Φ 1 := by
    have h2 : algebraMap ℝ A ‖a‖ = (‖a‖ : ℂ) • (1 : A) := by
      rw [Algebra.algebraMap_eq_smul_one, ← algebraMap_smul ℂ (‖a‖ : ℝ)
        (1 : A)]
      norm_num
    rw [h2, map_smul, smul_eq_mul]
  have hsplit : Φ a = Φ (algebraMap ℝ A ‖a‖)
      - Φ (algebraMap ℝ A ‖a‖ - a) := by
    rw [map_sub]
    ring
  refine ⟨‖a‖ * r0 - r1, ?_⟩
  rw [hsplit, halg, hΦ0, hΦ1]
  push_cast
  ring

/-- **A functional that is nonnegative on positives is hermitian.** -/
theorem hermitian_of_nonneg (Φ : A →ₗ[ℂ] ℂ)
    (hpos : ∀ a : A, 0 ≤ a → ∃ r : ℝ, 0 ≤ r ∧ Φ a = r) (y : A) :
    Φ (star y) = (starRingEnd ℂ) (Φ y) := by
  obtain ⟨t1, ht1⟩ := real_on_selfAdjoint_of_nonneg Φ hpos (rePart y).2
  obtain ⟨t2, ht2⟩ := real_on_selfAdjoint_of_nonneg Φ hpos (imPart y).2
  have hy : ((rePart y : selfAdjoint A) : A)
      + Complex.I • ((imPart y : selfAdjoint A) : A) = y :=
    rePart_add_I_smul_imPart y
  have hstar_y : ((rePart y : selfAdjoint A) : A)
      - Complex.I • ((imPart y : selfAdjoint A) : A) = star y := by
    have h := congrArg star hy
    rw [star_add, star_smul, Complex.star_def, Complex.conj_I,
      (rePart y).2.star_eq, (imPart y).2.star_eq, neg_smul] at h
    rw [sub_eq_add_neg]
    exact h
  have hval : Φ y = (t1 : ℂ) + Complex.I * t2 := by
    rw [← hy, map_add, map_smul, ht1, ht2, smul_eq_mul]
  have hvalstar : Φ (star y) = (t1 : ℂ) - Complex.I * t2 := by
    rw [← hstar_y, map_sub, map_smul, ht1, ht2, smul_eq_mul]
  rw [hval, hvalstar, map_add, map_mul, Complex.conj_I,
    Complex.conj_ofReal, Complex.conj_ofReal]
  ring

end

end StateExtension
end GroupApproximation
