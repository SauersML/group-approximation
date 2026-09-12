import GroupApproximation.CharClass.LIXKGenChart
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import GroupApproximation.Meta.AxiomGuard

/-!
# The strict derivative of the section at its zero, at rank `n`

Lane `lix-oddside-n` (predecessor report `sp-oddside-n.md` §0.3, file E).

`CharClass/LIXKGenChart.lean` charts `S^{2n+1}` at `−e₀` and writes down the candidate
derivative `eulerContinuousLinearEquiv n` of the trivial block.  This file proves it is the
strict derivative, which is what `HasStrictFDerivAt.toOpenPartialHomeomorph` consumes.  The
argument is `CharClass/LIXSectionDeriv.lean`'s with the rank a parameter: the chart splits as a
linear part minus a radial correction `√(1 − ‖w‖²) • e₀`, whose differential at the origin
vanishes because a quadratic form's does, and `Φ (w, u) = e₀ + τ(u) • (X w − e₀)` gives the
rest by the product rule.

## Main results

* `KGen.chartLinearCLM` — the linear part of the chart; `sphereChartVec_eq`.
* `KGen.hasStrictFDerivAt_chartWeight` — zero differential of the radial weight.
* `KGen.hasStrictFDerivAt_trivialBlockChart` — **the derivative of the trivial block at its
  zero is `eulerContinuousLinearEquiv n`.**
-/

noncomputable section

namespace GroupApproximation.CharClass

namespace KGen

open GroupApproximation.STW59

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-! ## 1. The linear part of the chart -/

/-- The ℝ-linear part of `sphereChartVec n`. -/
def chartLinearMap (n : ℕ) : ChartBase n →ₗ[ℝ] (Fin (n + 1) → ℂ) where
  toFun w := Fin.cons ((w.1 : ℂ) * Complex.I) w.2
  map_add' p q := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero, Prod.fst_add, Pi.add_apply, Complex.ofReal_add] <;> ring
    · simp only [Fin.cons_succ, Prod.snd_add, Pi.add_apply] <;> rfl
  map_smul' r p := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero, Prod.smul_fst, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul,
        Complex.real_smul, RingHom.id_apply] <;> ring
    · simp only [Fin.cons_succ, Prod.smul_snd, Pi.smul_apply, RingHom.id_apply] <;> rfl

/-- The linear part, as a continuous linear map. -/
def chartLinearCLM (n : ℕ) : ChartBase n →L[ℝ] (Fin (n + 1) → ℂ) :=
  LinearMap.toContinuousLinearMap (chartLinearMap n)

@[simp]
theorem chartLinearCLM_apply (n : ℕ) (w : ChartBase n) :
    chartLinearCLM n w = Fin.cons ((w.1 : ℂ) * Complex.I) w.2 := rfl

/-- **The chart splits into a linear part and a radial correction.** -/
theorem sphereChartVec_eq (n : ℕ) (w : ChartBase n) :
    sphereChartVec n w = chartLinearCLM n w - chartWeight n w • eZero n := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [sphereChartVec, eZero, Complex.real_smul]
  · simp [sphereChartVec, eZero]

/-! ## 2. The radial weight has vanishing differential -/

/-- A squared norm after a continuous linear map has zero differential at the origin. -/
theorem hasStrictFDerivAt_normSq_comp {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (L : E →L[ℝ] F) :
    HasStrictFDerivAt (fun p : E => ‖L p‖ ^ 2) (0 : E →L[ℝ] ℝ) 0 := by
  have h := (hasStrictFDerivAt_norm_sq (L 0)).comp (0 : E) L.hasStrictFDerivAt
  rw [map_zero] at h
  simpa using h

theorem hasStrictFDerivAt_chartQ (n : ℕ) :
    HasStrictFDerivAt (fun p : ChartSrc n => chartQ n p.1) (0 : ChartSrc n →L[ℝ] ℝ) 0 := by
  have h1 : HasStrictFDerivAt (fun p : ChartSrc n => ‖p.1.1‖ ^ 2) (0 : ChartSrc n →L[ℝ] ℝ) 0 :=
    hasStrictFDerivAt_normSq_comp
      ((ContinuousLinearMap.fst ℝ ℝ (Fin n → ℂ)).comp
        (ContinuousLinearMap.fst ℝ (ChartBase n) ℝ))
  have h1' : HasStrictFDerivAt (fun p : ChartSrc n => p.1.1 ^ 2) (0 : ChartSrc n →L[ℝ] ℝ) 0 := by
    simpa [Real.norm_eq_abs, sq_abs] using h1
  have h2 : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      HasStrictFDerivAt (fun p : ChartSrc n => ‖p.1.2 j‖ ^ 2) (0 : ChartSrc n →L[ℝ] ℝ) 0 :=
    fun j _ => hasStrictFDerivAt_normSq_comp
      ((ContinuousLinearMap.proj j).comp
        ((ContinuousLinearMap.snd ℝ ℝ (Fin n → ℂ)).comp
          (ContinuousLinearMap.fst ℝ (ChartBase n) ℝ)))
  have hsum := HasStrictFDerivAt.fun_sum h2
  exact (h1'.add hsum).congr_fderiv (by simp)

/-- **The radial weight has zero differential at the origin.** -/
theorem hasStrictFDerivAt_chartWeight (n : ℕ) :
    HasStrictFDerivAt (fun p : ChartSrc n => chartWeight n p.1) (0 : ChartSrc n →L[ℝ] ℝ) 0 := by
  have hinner : HasStrictFDerivAt (fun p : ChartSrc n => 1 - chartQ n p.1)
      (0 : ChartSrc n →L[ℝ] ℝ) 0 :=
    ((hasStrictFDerivAt_const (1 : ℝ) (0 : ChartSrc n)).sub
      (hasStrictFDerivAt_chartQ n)).congr_fderiv (by simp)
  have hval : (fun p : ChartSrc n => 1 - chartQ n p.1) (0 : ChartSrc n) = 1 := by
    simp [chartQ]
  have hsqrt : HasStrictFDerivAt Real.sqrt
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (1 / (2 * Real.sqrt 1)))
      ((fun p : ChartSrc n => 1 - chartQ n p.1) (0 : ChartSrc n)) := by
    rw [hval]
    exact (Real.hasStrictDerivAt_sqrt one_ne_zero).hasStrictFDerivAt
  have h := hsqrt.comp (0 : ChartSrc n) hinner
  simpa [chartWeight] using h

/-! ## 3. The derivative of the chart, and of the section -/

theorem hasStrictFDerivAt_sphereChartVec (n : ℕ) :
    HasStrictFDerivAt (fun p : ChartSrc n => sphereChartVec n p.1)
      ((chartLinearCLM n).comp (ContinuousLinearMap.fst ℝ (ChartBase n) ℝ)) 0 := by
  have hlin : HasStrictFDerivAt (fun p : ChartSrc n => chartLinearCLM n p.1)
      ((chartLinearCLM n).comp (ContinuousLinearMap.fst ℝ (ChartBase n) ℝ)) 0 :=
    ((chartLinearCLM n).comp (ContinuousLinearMap.fst ℝ (ChartBase n) ℝ)).hasStrictFDerivAt
  have hrad : HasStrictFDerivAt (fun p : ChartSrc n => chartWeight n p.1 • eZero n)
      (0 : ChartSrc n →L[ℝ] (Fin (n + 1) → ℂ)) 0 := by
    have h := (hasStrictFDerivAt_chartWeight n).smul
      (hasStrictFDerivAt_const (eZero n : Fin (n + 1) → ℂ) (0 : ChartSrc n))
    simpa using h
  have h := hlin.sub hrad
  have hfe2 : ((fun p : ChartSrc n => chartLinearCLM n p.1)
      - fun p : ChartSrc n => chartWeight n p.1 • eZero n)
      = fun p : ChartSrc n => sphereChartVec n p.1 := by
    funext p
    simp only [Pi.sub_apply]
    rw [sphereChartVec_eq]
  rw [hfe2] at h
  exact h.congr_fderiv (by simp)

/-- **The derivative of the trivial block of the section at its zero**, at rank `n`.

`Φ (w, u) = e₀ + τ(u) • (X w − e₀)`, so the product rule gives `dτ • (−2 e₀) + (1/2) • dX`,
which is `eulerContinuousLinearEquiv n`. -/
theorem hasStrictFDerivAt_trivialBlockChart (n : ℕ) :
    HasStrictFDerivAt (fun p : ChartSrc n => trivialBlockChart n p.1 p.2)
      (eulerContinuousLinearEquiv n : ChartSrc n →L[ℝ] (Fin (n + 1) → ℂ)) 0 := by
  have hsnd : HasStrictFDerivAt (fun p : ChartSrc n => p.2)
      (ContinuousLinearMap.snd ℝ (ChartBase n) ℝ) 0 :=
    (ContinuousLinearMap.snd ℝ (ChartBase n) ℝ).hasStrictFDerivAt
  have hfe : (fun p : ChartSrc n => (1 + p.2) / 2)
      = fun p : ChartSrc n => (2⁻¹ : ℝ) • ((1 : ℝ) + p.2) := by
    funext p
    rw [smul_eq_mul]
    ring
  have hτ : HasStrictFDerivAt (fun p : ChartSrc n => (1 + p.2) / 2)
      ((2⁻¹ : ℝ) • ((0 : ChartSrc n →L[ℝ] ℝ) + ContinuousLinearMap.snd ℝ (ChartBase n) ℝ))
      0 := by
    rw [hfe]
    exact ((hasStrictFDerivAt_const (1 : ℝ) (0 : ChartSrc n)).add hsnd).const_smul (2⁻¹ : ℝ)
  have hY : HasStrictFDerivAt (fun p : ChartSrc n => sphereChartVec n p.1 - eZero n)
      ((chartLinearCLM n).comp (ContinuousLinearMap.fst ℝ (ChartBase n) ℝ)) 0 := by
    simpa using (hasStrictFDerivAt_sphereChartVec n).sub
      (hasStrictFDerivAt_const (eZero n : Fin (n + 1) → ℂ) (0 : ChartSrc n))
  have hprod := hτ.smul hY
  have hfull := (hasStrictFDerivAt_const (eZero n : Fin (n + 1) → ℂ) (0 : ChartSrc n)).add hprod
  have hfun : ((fun _ : ChartSrc n => (eZero n : Fin (n + 1) → ℂ))
        + (fun p : ChartSrc n => (1 + p.2) / 2)
          • fun p : ChartSrc n => sphereChartVec n p.1 - eZero n)
      = fun p : ChartSrc n => trivialBlockChart n p.1 p.2 := by
    funext p i
    show eZero n i + ((1 + p.2) / 2 : ℝ) • (sphereChartVec n p.1 i - eZero n i)
        = ((1 - (1 + p.2) / 2 : ℝ) : ℂ) * eZero n i
          + (((1 + p.2) / 2 : ℝ) : ℂ) * sphereChartVec n p.1 i
    rw [Complex.real_smul]
    push_cast
    ring
  rw [hfun] at hfull
  refine hfull.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun p => ?_
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [eZero, sphereChartVec_zero, Complex.real_smul] <;> ring
  · simp [eZero, sphereChartVec_zero, Complex.real_smul] <;> ring

end KGen

/-! Audited on every build. -/

#audit_axioms KGen.hasStrictFDerivAt_chartWeight
#audit_axioms KGen.hasStrictFDerivAt_trivialBlockChart

end GroupApproximation.CharClass
