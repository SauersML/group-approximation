import GroupApproximation.CharClass.LIXProjectiveChartDeriv
import GroupApproximation.CharClass.LIXSectionLocalHomeo

/-!
# The product chart at the full rank

Lane `cc-lix-odd`, the assembly of the two chart factors.

`eulerLocalHomeo` charts the section's trivial block, six real dimensions onto `ℂ³`.
`LIXProjectiveChartDeriv` differentiates the projective block for one factor.  This file
runs the projective block over the whole tower and multiplies the two charts.

The dimensions match: `3 + ∑ⱼ dⱼ = lixRank dd`, and the base has real dimension
`2 (∑ⱼ dⱼ) + 6`, which is twice that.  So the product is a chart at the full rank, which
is what `cc-thom`'s local model asks for.

## Main results

* `cpChartSectionPi` — the projective block over the whole tower.
* `hasStrictFDerivAt_cpChartSectionPi` — its strict derivative at the origin.
* `cpLocalHomeo` — the projective factor of the chart, from the inverse function theorem.
* `lixProductChart` — **the product chart**, with the zero in its source and the origin in
  its target.
-/

noncomputable section

namespace GroupApproximation.CharClass

open GroupApproximation.STW59

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-! ## 1. The projective block over the whole tower -/

/-- The projective block of the section, over every factor at once. -/
def cpChartSectionPi (dd : Fin ℓ → ℕ) (z : ∀ j : Fin ℓ, Fin (dd j) → ℂ) :
    ∀ j : Fin ℓ, Fin (dd j) → ℂ :=
  fun j => cpChartSection (z j)

/-- Componentwise conjugation over the whole tower. -/
def conjPiPiCLE (dd : Fin ℓ → ℕ) :
    (∀ j : Fin ℓ, Fin (dd j) → ℂ) ≃L[ℝ] (∀ j : Fin ℓ, Fin (dd j) → ℂ) :=
  ContinuousLinearEquiv.piCongrRight fun j => conjPiCLE (dd j)

theorem proj_comp_conjPiPiCLE (j : Fin ℓ) :
    (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun k : Fin ℓ => Fin (dd k) → ℂ) j).comp
      (conjPiPiCLE dd : _ →L[ℝ] _)
      = (conjPiCLE (dd j) : (Fin (dd j) → ℂ) →L[ℝ] (Fin (dd j) → ℂ)).comp
        (ContinuousLinearMap.proj (R := ℝ)
          (φ := fun k : Fin ℓ => Fin (dd k) → ℂ) j) := by
  refine ContinuousLinearMap.ext fun z => ?_
  funext i
  simp [conjPiPiCLE]

/-- **The strict derivative of the projective block at the origin.** -/
theorem hasStrictFDerivAt_cpChartSectionPi :
    HasStrictFDerivAt (cpChartSectionPi dd)
      ((conjPiPiCLE dd : (∀ j : Fin ℓ, Fin (dd j) → ℂ) →L[ℝ] _)) 0 := by
  refine hasStrictFDerivAt_pi'.mpr fun j => ?_
  have h := (hasStrictFDerivAt_cpChartSection (d := dd j)).comp (0 : ∀ k : Fin ℓ, Fin (dd k) → ℂ)
    (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun k : Fin ℓ => Fin (dd k) → ℂ) j).hasStrictFDerivAt
  rw [← proj_comp_conjPiPiCLE (dd := dd) j] at h
  exact h

/-! ## 2. The projective factor of the chart -/

/-- The projective factor, from the inverse function theorem. -/
def cpLocalHomeo (dd : Fin ℓ → ℕ) :
    OpenPartialHomeomorph (∀ j : Fin ℓ, Fin (dd j) → ℂ) (∀ j : Fin ℓ, Fin (dd j) → ℂ) :=
  (hasStrictFDerivAt_cpChartSectionPi (dd := dd)).toOpenPartialHomeomorph
    (cpChartSectionPi dd)

theorem cpChartSectionPi_zero :
    cpChartSectionPi dd (0 : ∀ j : Fin ℓ, Fin (dd j) → ℂ) = 0 := by
  funext j i
  simp [cpChartSectionPi, cpChartSection]

theorem zero_mem_cpLocalHomeo_source :
    (0 : ∀ j : Fin ℓ, Fin (dd j) → ℂ) ∈ (cpLocalHomeo dd).source :=
  (hasStrictFDerivAt_cpChartSectionPi (dd := dd)).mem_toOpenPartialHomeomorph_source

theorem cpLocalHomeo_zero :
    cpLocalHomeo dd (0 : ∀ j : Fin ℓ, Fin (dd j) → ℂ)
      = (0 : ∀ j : Fin ℓ, Fin (dd j) → ℂ) := by
  rw [show cpLocalHomeo dd (0 : ∀ j : Fin ℓ, Fin (dd j) → ℂ)
      = cpChartSectionPi dd 0 from
    congrFun (hasStrictFDerivAt_cpChartSectionPi
      (dd := dd)).toOpenPartialHomeomorph_coe 0]
  exact cpChartSectionPi_zero

theorem zero_mem_cpLocalHomeo_target :
    (0 : ∀ j : Fin ℓ, Fin (dd j) → ℂ) ∈ (cpLocalHomeo dd).target := by
  have h := (hasStrictFDerivAt_cpChartSectionPi
    (dd := dd)).image_mem_toOpenPartialHomeomorph_target
  rwa [cpChartSectionPi_zero] at h

/-! ## 3. The product -/

/-- **The product chart**, the trivial block times the projective block. -/
def lixProductChart (dd : Fin ℓ → ℕ) :
    OpenPartialHomeomorph (ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ))
      ((Fin 3 → ℂ) × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) :=
  eulerLocalHomeo.prod (cpLocalHomeo dd)

theorem zero_mem_lixProductChart_source :
    ((0, 0) : ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) ∈ (lixProductChart dd).source :=
  ⟨zero_mem_eulerLocalHomeo_source, zero_mem_cpLocalHomeo_source⟩

theorem zero_mem_lixProductChart_target :
    ((0, 0) : (Fin 3 → ℂ) × (∀ j : Fin ℓ, Fin (dd j) → ℂ))
      ∈ (lixProductChart dd).target :=
  ⟨zero_mem_eulerLocalHomeo_target, zero_mem_cpLocalHomeo_target⟩

theorem lixProductChart_zero :
    lixProductChart dd ((0, 0) : ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ))
      = ((0, 0) : (Fin 3 → ℂ) × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) := by
  refine Prod.ext ?_ ?_
  · exact eulerLocalHomeo_zero
  · exact cpLocalHomeo_zero

end GroupApproximation.CharClass
