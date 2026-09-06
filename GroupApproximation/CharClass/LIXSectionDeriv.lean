import GroupApproximation.CharClass.LIXSectionChart

/-!
# The strict derivative of the section at its zero

Lane `cc-lix-odd` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

`CharClass/LIXSectionChart.lean` charts `S⁵` at `-e₃` on the plain product `ℂ × ℂ × ℝ` and
writes down the candidate derivative `eulerContinuousLinearEquiv` of the trivial block of
the manuscript's section.  This file proves that it really is the derivative, in the
`HasStrictFDerivAt` form that `HasStrictFDerivAt.toOpenPartialHomeomorph` consumes and
`cc-thom`'s `EulerLocalChart.openPartialHomeomorphChartPair` then turns into a
homeomorphism of pairs.

## Why the square root costs nothing

Write `X` for the chart of the sphere and `τ (u) = (1 + u)/2` for the circle coordinate.
The trivial block is

```text
Φ (w, u) = e₃ + τ(u) • (X w − e₃),
```

so by the product rule its derivative at the origin is
`dτ • (X 0 − e₃) + τ(0) • dX`, and `X 0 − e₃ = −2 e₃` while `τ(0) = 1/2`.  The chart splits
as `X w = A w − (√(1 − ‖w‖²)) • e₃` with `A` **linear**, and the radial weight has
*vanishing* differential at the origin because `‖w‖²` does.  So the only analysis in the
file is "a quadratic form has zero differential at zero" plus one chain rule through
`Real.sqrt` at the point `1`.

## Main results

* `chartLinearCLM` — the linear part `A` of the sphere chart.
* `hasStrictFDerivAt_chartWeight` — the radial weight has zero differential at the origin.
* `hasStrictFDerivAt_sphereChartVec` — the chart's derivative is its linear part.
* `hasStrictFDerivAt_trivialBlockChart` — **the derivative of the section's trivial block at
  its zero is `eulerContinuousLinearEquiv`.**
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open GroupApproximation.STW59

set_option linter.unusedSectionVars false

/-- The source of the chart of `S⁵ × S¹` at the zero. -/
abbrev ChartSrc : Type := (ℂ × ℂ × ℝ) × ℝ

/-! ## 1. The linear part of the sphere chart -/

/-- The ℝ-linear part of `sphereChartVec`. -/
def chartLinearMap : (ℂ × ℂ × ℝ) →ₗ[ℝ] (Fin 3 → ℂ) where
  toFun w := ![w.1, w.2.1, (w.2.2 : ℂ) * Complex.I]
  map_add' p q := by
    funext i
    fin_cases i
    all_goals simp
    all_goals ring
  map_smul' r p := by
    funext i
    fin_cases i
    all_goals simp
    all_goals ring

/-- The linear part, as a continuous linear map (both sides are finite-dimensional). -/
def chartLinearCLM : (ℂ × ℂ × ℝ) →L[ℝ] (Fin 3 → ℂ) :=
  LinearMap.toContinuousLinearMap chartLinearMap

@[simp]
theorem chartLinearCLM_apply (w : ℂ × ℂ × ℝ) :
    chartLinearCLM w = ![w.1, w.2.1, (w.2.2 : ℂ) * Complex.I] := rfl

/-- **The chart splits into a linear part and a radial correction.** -/
theorem sphereChartVec_eq (w : ℂ × ℂ × ℝ) :
    sphereChartVec w = chartLinearCLM w - chartWeight w • eThree := by
  funext i
  fin_cases i <;>
    simp [sphereChartVec, eThree, Complex.real_smul]

/-! ## 2. The radial weight has vanishing differential -/

/-- A squared norm on a factor of the source has zero differential at the origin. -/
theorem hasStrictFDerivAt_normSq_comp {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (L : ChartSrc →L[ℝ] F) (hL : L 0 = 0) :
    HasStrictFDerivAt (fun p : ChartSrc => ‖L p‖ ^ 2) (0 : ChartSrc →L[ℝ] ℝ) 0 := by
  have h := (hasStrictFDerivAt_norm_sq (L 0)).comp (0 : ChartSrc) L.hasStrictFDerivAt
  rw [hL] at h
  simpa using h

theorem hasStrictFDerivAt_chartQ :
    HasStrictFDerivAt
      (fun p : ChartSrc => ‖p.1.1‖ ^ 2 + ‖p.1.2.1‖ ^ 2 + p.1.2.2 ^ 2)
      (0 : ChartSrc →L[ℝ] ℝ) 0 := by
  have h1 : HasStrictFDerivAt (fun p : ChartSrc => ‖p.1.1‖ ^ 2) (0 : ChartSrc →L[ℝ] ℝ) 0 :=
    hasStrictFDerivAt_normSq_comp
      ((ContinuousLinearMap.fst ℝ ℂ (ℂ × ℝ)).comp
        (ContinuousLinearMap.fst ℝ (ℂ × ℂ × ℝ) ℝ)) (by simp)
  have h2 : HasStrictFDerivAt (fun p : ChartSrc => ‖p.1.2.1‖ ^ 2) (0 : ChartSrc →L[ℝ] ℝ) 0 :=
    hasStrictFDerivAt_normSq_comp
      ((ContinuousLinearMap.fst ℝ ℂ ℝ).comp
        ((ContinuousLinearMap.snd ℝ ℂ (ℂ × ℝ)).comp
          (ContinuousLinearMap.fst ℝ (ℂ × ℂ × ℝ) ℝ))) (by simp)
  have h3 : HasStrictFDerivAt (fun p : ChartSrc => ‖p.1.2.2‖ ^ 2) (0 : ChartSrc →L[ℝ] ℝ) 0 :=
    hasStrictFDerivAt_normSq_comp
      ((ContinuousLinearMap.snd ℝ ℂ ℝ).comp
        ((ContinuousLinearMap.snd ℝ ℂ (ℂ × ℝ)).comp
          (ContinuousLinearMap.fst ℝ (ℂ × ℂ × ℝ) ℝ))) (by simp)
  have h3' : HasStrictFDerivAt (fun p : ChartSrc => p.1.2.2 ^ 2) (0 : ChartSrc →L[ℝ] ℝ) 0 := by
    simpa [Real.norm_eq_abs, sq_abs] using h3
  exact ((h1.add h2).add h3').congr_fderiv (by simp)

/-- **The radial weight has zero differential at the origin.**  Its argument is `1` there,
so `Real.sqrt` is strictly differentiable, and the inner quadratic form contributes
nothing. -/
theorem hasStrictFDerivAt_chartWeight :
    HasStrictFDerivAt (fun p : ChartSrc => chartWeight p.1) (0 : ChartSrc →L[ℝ] ℝ) 0 := by
  have hinner : HasStrictFDerivAt
      (fun p : ChartSrc => 1 - (‖p.1.1‖ ^ 2 + ‖p.1.2.1‖ ^ 2 + p.1.2.2 ^ 2))
      (0 : ChartSrc →L[ℝ] ℝ) 0 := by
    exact ((hasStrictFDerivAt_const (1 : ℝ) (0 : ChartSrc)).sub
      hasStrictFDerivAt_chartQ).congr_fderiv (by simp)
  have hval : (fun p : ChartSrc => 1 - (‖p.1.1‖ ^ 2 + ‖p.1.2.1‖ ^ 2 + p.1.2.2 ^ 2))
      (0 : ChartSrc) = 1 := by simp
  have hsqrt : HasStrictFDerivAt Real.sqrt
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (1 / (2 * Real.sqrt 1)))
      ((fun p : ChartSrc => 1 - (‖p.1.1‖ ^ 2 + ‖p.1.2.1‖ ^ 2 + p.1.2.2 ^ 2))
        (0 : ChartSrc)) := by
    rw [hval]
    exact (Real.hasStrictDerivAt_sqrt one_ne_zero).hasStrictFDerivAt
  have h := hsqrt.comp (0 : ChartSrc) hinner
  simpa [chartWeight] using h

/-! ## 3. The derivative of the chart, and of the section -/

theorem hasStrictFDerivAt_sphereChartVec :
    HasStrictFDerivAt (fun p : ChartSrc => sphereChartVec p.1)
      (chartLinearCLM.comp (ContinuousLinearMap.fst ℝ (ℂ × ℂ × ℝ) ℝ)) 0 := by
  have hlin : HasStrictFDerivAt (fun p : ChartSrc => chartLinearCLM p.1)
      (chartLinearCLM.comp (ContinuousLinearMap.fst ℝ (ℂ × ℂ × ℝ) ℝ)) 0 :=
    (chartLinearCLM.comp (ContinuousLinearMap.fst ℝ (ℂ × ℂ × ℝ) ℝ)).hasStrictFDerivAt
  have hrad : HasStrictFDerivAt (fun p : ChartSrc => chartWeight p.1 • eThree)
      (0 : ChartSrc →L[ℝ] (Fin 3 → ℂ)) 0 := by
    have h := hasStrictFDerivAt_chartWeight.smul
      (hasStrictFDerivAt_const (eThree : Fin 3 → ℂ) (0 : ChartSrc))
    simpa using h
  have h := hlin.sub hrad
  have hfe2 : ((fun p : ChartSrc => chartLinearCLM p.1)
      - fun p : ChartSrc => chartWeight p.1 • eThree)
      = fun p : ChartSrc => sphereChartVec p.1 := by
    funext p
    simp only [Pi.sub_apply]
    rw [sphereChartVec_eq]
  rw [hfe2] at h
  exact h.congr_fderiv (by simp)

/-- **The derivative of the trivial block of the manuscript's section at its zero.**

`Φ (w, u) = e₃ + τ(u) • (X w − e₃)`, so the product rule gives
`dτ • (−2 e₃) + (1/2) • dX`, which is `eulerContinuousLinearEquiv`. -/
theorem hasStrictFDerivAt_trivialBlockChart :
    HasStrictFDerivAt (fun p : ChartSrc => trivialBlockChart p.1 p.2)
      (eulerContinuousLinearEquiv : ChartSrc →L[ℝ] (Fin 3 → ℂ)) 0 := by
  -- the circle coordinate
  have hsnd : HasStrictFDerivAt (fun p : ChartSrc => p.2)
      (ContinuousLinearMap.snd ℝ (ℂ × ℂ × ℝ) ℝ) 0 :=
    (ContinuousLinearMap.snd ℝ (ℂ × ℂ × ℝ) ℝ).hasStrictFDerivAt
  have hfe : (fun p : ChartSrc => (1 + p.2) / 2)
      = fun p : ChartSrc => (2⁻¹ : ℝ) • ((1 : ℝ) + p.2) := by
    funext p
    rw [smul_eq_mul]
    ring
  have hτ : HasStrictFDerivAt (fun p : ChartSrc => (1 + p.2) / 2)
      ((2⁻¹ : ℝ) • ((0 : ChartSrc →L[ℝ] ℝ) + ContinuousLinearMap.snd ℝ (ℂ × ℂ × ℝ) ℝ)) 0 := by
    rw [hfe]
    exact ((hasStrictFDerivAt_const (1 : ℝ) (0 : ChartSrc)).add hsnd).const_smul (2⁻¹ : ℝ)
  -- the sphere chart, shifted by `e₃`
  have hY : HasStrictFDerivAt (fun p : ChartSrc => sphereChartVec p.1 - eThree)
      (chartLinearCLM.comp (ContinuousLinearMap.fst ℝ (ℂ × ℂ × ℝ) ℝ)) 0 := by
    simpa using hasStrictFDerivAt_sphereChartVec.sub
      (hasStrictFDerivAt_const (eThree : Fin 3 → ℂ) (0 : ChartSrc))
  have hprod := hτ.smul hY
  have hfull := (hasStrictFDerivAt_const (eThree : Fin 3 → ℂ) (0 : ChartSrc)).add hprod
  have hfun : ((fun _ : ChartSrc => (eThree : Fin 3 → ℂ))
        + (fun p : ChartSrc => (1 + p.2) / 2) • fun p : ChartSrc => sphereChartVec p.1 - eThree)
      = fun p : ChartSrc => trivialBlockChart p.1 p.2 := by
    funext p i
    show eThree i + ((1 + p.2) / 2 : ℝ) • (sphereChartVec p.1 i - eThree i)
        = ((1 - (1 + p.2) / 2 : ℝ) : ℂ) * eThree i
          + (((1 + p.2) / 2 : ℝ) : ℂ) * sphereChartVec p.1 i
    rw [Complex.real_smul]
    push_cast
    ring
  rw [hfun] at hfull
  refine hfull.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun p => ?_
  funext i
  fin_cases i <;> simp [eThree] <;> ring

end GroupApproximation.CharClass
