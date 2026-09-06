import GroupApproximation.CharClass.LIXProjectiveChartSection
import GroupApproximation.CharClass.LIXSectionDeriv

/-!
# The H-block section is a local homeomorphism at the base point

Lane `cc-lix-odd`, the second factor of the product chart at the full rank.

`LIXProjectiveChartSection` computed the section in the affine chart; its `j = 0`
component is `conj (wᵢ)` over a positive real.  This file differentiates that at the
origin, where the denominator is `1` and the section vanishes, so the strict derivative is
**componentwise complex conjugation**, a real-linear isomorphism.

## Main results

* `conjPiCLE` — componentwise conjugation, as a continuous real-linear equivalence.
* `cpChartSection` — the `j = 0` block of the section, in the chart.
* `hasStrictFDerivAt_cpChartSection` — its strict derivative at the origin is `conjPiCLE`.
-/

noncomputable section

namespace GroupApproximation.CharClass

open GroupApproximation.STW59

set_option linter.unusedSectionVars false

variable {d : ℕ}

/-! ## 1. Conjugation as a real-linear equivalence -/

/-- Componentwise complex conjugation on `ℂ^d`, as a continuous `ℝ`-linear equivalence. -/
def conjPiCLE (d : ℕ) : (Fin d → ℂ) ≃L[ℝ] (Fin d → ℂ) :=
  ContinuousLinearEquiv.piCongrRight fun _ : Fin d => Complex.conjCLE

@[simp] theorem conjPiCLE_apply (w : Fin d → ℂ) (i : Fin d) :
    conjPiCLE d w i = star (w i) := rfl

/-! ## 2. The denominator has vanishing differential -/

/-- A squared norm of one coordinate has zero differential at the origin. -/
theorem hasStrictFDerivAt_normSq_projPi (k : Fin d) :
    HasStrictFDerivAt (fun w : Fin d → ℂ => ‖w k‖ ^ 2) (0 : (Fin d → ℂ) →L[ℝ] ℝ) 0 := by
  have hp : ((ContinuousLinearMap.proj k : (Fin d → ℂ) →L[ℝ] ℂ)) 0 = 0 := by simp
  have h := (hasStrictFDerivAt_norm_sq
      ((ContinuousLinearMap.proj k : (Fin d → ℂ) →L[ℝ] ℂ) 0)).comp (0 : Fin d → ℂ)
    (ContinuousLinearMap.proj k : (Fin d → ℂ) →L[ℝ] ℂ).hasStrictFDerivAt
  rw [hp] at h
  simpa using h

/-- The chart denominator `1 + ∑ ‖wₖ‖²` has zero differential at the origin. -/
theorem hasStrictFDerivAt_cpDenomReal :
    HasStrictFDerivAt (fun w : Fin d → ℂ => (1 : ℝ) + ∑ k, ‖w k‖ ^ 2)
      (0 : (Fin d → ℂ) →L[ℝ] ℝ) 0 := by
  have hsum : HasStrictFDerivAt (fun w : Fin d → ℂ => ∑ k, ‖w k‖ ^ 2)
      (0 : (Fin d → ℂ) →L[ℝ] ℝ) 0 := by
    have h := HasStrictFDerivAt.sum
      (fun k (_ : k ∈ Finset.univ) => hasStrictFDerivAt_normSq_projPi (d := d) k)
    have hfun : (∑ i : Fin d, fun w : Fin d → ℂ => ‖w i‖ ^ 2)
        = fun w : Fin d → ℂ => ∑ k, ‖w k‖ ^ 2 := by
      funext w
      simp
    rw [hfun] at h
    refine h.congr_fderiv ?_
    ext w
    simp
  have h := (hasStrictFDerivAt_const (1 : ℝ) (0 : Fin d → ℂ)).add hsum
  exact h.congr_fderiv (by simp)

/-- The same, cast to `ℂ`. -/
theorem hasStrictFDerivAt_cpDenomComplex :
    HasStrictFDerivAt (fun w : Fin d → ℂ => (((1 : ℝ) + ∑ k, ‖w k‖ ^ 2 : ℝ) : ℂ))
      (0 : (Fin d → ℂ) →L[ℝ] ℂ) 0 := by
  have h := Complex.ofRealCLM.hasStrictFDerivAt.comp (0 : Fin d → ℂ)
    (hasStrictFDerivAt_cpDenomReal (d := d))
  simpa using h

/-- The reciprocal of the denominator, whose differential also vanishes. -/
theorem hasStrictFDerivAt_cpDenomInv :
    HasStrictFDerivAt (fun w : Fin d → ℂ => ((((1 : ℝ) + ∑ k, ‖w k‖ ^ 2 : ℝ) : ℂ))⁻¹)
      (0 : (Fin d → ℂ) →L[ℝ] ℂ) 0 := by
  have hne : (((1 : ℝ) + ∑ k, ‖(0 : Fin d → ℂ) k‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    simp
  have hinv := (hasStrictFDerivAt_inv hne).restrictScalars ℝ
  have h := hinv.comp (0 : Fin d → ℂ) (hasStrictFDerivAt_cpDenomComplex (d := d))
  exact h.congr_fderiv (by simp)

/-! ## 3. The section block and its derivative -/

/-- The `j = 0` block of the tautological column section, in the affine chart. -/
def cpChartSection (w : Fin d → ℂ) : Fin d → ℂ :=
  fun i => star (w i) / ((((1 : ℝ) + ∑ k, ‖w k‖ ^ 2 : ℝ)) : ℂ)

theorem cpChartSection_eq (w : Fin d → ℂ) :
    cpChartSection w
      = ((((1 : ℝ) + ∑ k, ‖w k‖ ^ 2 : ℝ) : ℂ))⁻¹ • (conjPiCLE d w) := by
  funext i
  simp [cpChartSection, div_eq_inv_mul]

/-- **The strict derivative at the origin is componentwise conjugation.**  The denominator
is `1` there and the section vanishes, so the product rule leaves only the linear factor.
Conjugation is a real-linear isomorphism, which is all the mod-2 argument needs. -/
theorem hasStrictFDerivAt_cpChartSection :
    HasStrictFDerivAt (cpChartSection (d := d))
      ((conjPiCLE d : (Fin d → ℂ) →L[ℝ] (Fin d → ℂ))) 0 := by
  have hconj : HasStrictFDerivAt (fun w : Fin d → ℂ => conjPiCLE d w)
      (conjPiCLE d : (Fin d → ℂ) →L[ℝ] (Fin d → ℂ)) 0 :=
    (conjPiCLE d : (Fin d → ℂ) →L[ℝ] (Fin d → ℂ)).hasStrictFDerivAt
  have h := (hasStrictFDerivAt_cpDenomInv (d := d)).smul hconj
  have hz : (conjPiCLE d) (0 : Fin d → ℂ) = 0 := by simp
  refine (h.congr_fderiv ?_).congr_of_eventuallyEq ?_
  · rw [hz]
    simp
  · filter_upwards with w
    exact (cpChartSection_eq w).symm

end GroupApproximation.CharClass
