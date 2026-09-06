import GroupApproximation.Analysis.LIXLemmaSixSouth

/-!
# The equator embedding is a bijection onto the equator

`equatorEmb` carries `S⁴ ⊆ ℝ⁵` into `{x ∈ S⁵ : Re (x 2) = 0}`.  The analytic
half of Corollary 4 needs the other direction: the southern cap has to be
presented as a quotient of `[0,1] × S⁴`, and for that the cone
`southParam` must hit every point of the cap, which needs every point of the
equator to be `equatorEmb` of something.

The inverse is the only formula there is, `x ↦ (Re x₀, Im x₀, Re x₁, Im x₁,
Im x₂)`, and the two facts about it are that it lands on `S⁴` — where
`Re x₂ = 0` is exactly what makes `|x₂|² = (Im x₂)²` — and that composing back
gives `x`.
-/

namespace GroupApproximation
namespace LIX

open scoped Matrix ComplexOrder CStarAlgebra

set_option linter.unusedSectionVars false

noncomputable section

/-- The inverse of `equatorEmb` on the equator. -/
def equatorInv (x : Fin 3 → ℂ) : EuclideanSpace ℝ (Fin 5) :=
  WithLp.toLp 2 ![(x 0).re, (x 0).im, (x 1).re, (x 1).im, (x 2).im]

theorem equatorInv_zero (x : Fin 3 → ℂ) : equatorInv x 0 = (x 0).re := rfl
theorem equatorInv_one (x : Fin 3 → ℂ) : equatorInv x 1 = (x 0).im := rfl
theorem equatorInv_two (x : Fin 3 → ℂ) : equatorInv x 2 = (x 1).re := rfl
theorem equatorInv_three (x : Fin 3 → ℂ) : equatorInv x 3 = (x 1).im := rfl
theorem equatorInv_four (x : Fin 3 → ℂ) : equatorInv x 4 = (x 2).im := rfl

/-- **The round trip.**  On the equator, `equatorEmb ∘ equatorInv` is the
identity: the first two coordinates reassemble `x₀` and `x₁`, and the third
reassembles `x₂` because its real part vanishes. -/
theorem equatorEmb_equatorInv {x : Fin 3 → ℂ} (h : (x 2).re = 0) :
    equatorEmb (equatorInv x) = x := by
  funext i
  fin_cases i
  · show equatorEmb (equatorInv x) 0 = x 0
    rw [equatorEmb_zero, equatorInv_zero, equatorInv_one]
    apply Complex.ext <;> simp
  · show equatorEmb (equatorInv x) 1 = x 1
    rw [equatorEmb_one, equatorInv_two, equatorInv_three]
    apply Complex.ext <;> simp
  · show equatorEmb (equatorInv x) 2 = x 2
    rw [equatorEmb_two, equatorInv_four]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, h]

/-- The inverse lands on `S⁴`.  `Re x₂ = 0` is what makes the fifth coordinate
carry all of `|x₂|`. -/
theorem equatorInv_mem {x : Fin 3 → ℂ} (hx : x ∈ STW59.unitVectors (Fin 3))
    (h : (x 2).re = 0) : equatorInv x ∈ STW59.sphereFour := by
  have hsum : (∑ i, ‖x i‖ ^ 2 : ℝ) = 1 := hx
  have hnorm : ‖equatorInv x‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_five, Fin.sum_univ_three] at *
    simp only [equatorInv_zero, equatorInv_one, equatorInv_two, equatorInv_three,
      equatorInv_four, Real.norm_eq_abs, sq_abs]
    have e0 : ‖x 0‖ ^ 2 = (x 0).re ^ 2 + (x 0).im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    have e1 : ‖x 1‖ ^ 2 = (x 1).re ^ 2 + (x 1).im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    have e2 : ‖x 2‖ ^ 2 = (x 2).im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, h]; ring
    rw [e0, e1, e2] at hsum
    linarith
  have : ‖equatorInv x‖ = 1 := by
    nlinarith [norm_nonneg (equatorInv x)]
  exact mem_sphere_zero_iff_norm.mpr this

/-- **Every point of the equator is in the image.** -/
theorem exists_equatorEmb {x : Fin 3 → ℂ} (hx : x ∈ STW59.unitVectors (Fin 3))
    (h : (x 2).re = 0) : ∃ v ∈ STW59.sphereFour, equatorEmb v = x :=
  ⟨equatorInv x, equatorInv_mem hx h, equatorEmb_equatorInv h⟩

end

end LIX
end GroupApproximation
