import GroupApproximation.CharClass.LIXCircleChart
import GroupApproximation.CharClass.LIXSphereChartHomeo
import GroupApproximation.CharClass.LIXProjectiveTowerChart
import GroupApproximation.CharClass.LIXBaseChart

/-!
# The base chart as a partial homeomorphism

Lane `cc-lix-odd`.

The three factors are now all `OpenPartialHomeomorph`s.  Multiplying them needs one
reordering: the chart source carries the five-sphere coordinates first and the circle
second, while `lixN` is the circle times the rest.  That reordering is a homeomorphism of
products with `rfl` inverses.

## Main results

* `lixChartReorder` — the source reordering.
* `lixBaseChart` — **the base chart, as a partial homeomorphism**.
* `zero_mem_lixBaseChart_source`, `lixBaseChart_zero` — the origin, and where it goes.
-/

noncomputable section

namespace GroupApproximation.CharClass

open Set
open GroupApproximation.STW59

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-! ## 1. The reordering -/

/-- The chart source, with the circle coordinate brought to the front. -/
def lixChartReorder (dd : Fin ℓ → ℕ) :
    (ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) ≃ₜ
      (ℝ × ((ℂ × ℂ × ℝ) × (∀ j : Fin ℓ, Fin (dd j) → ℂ))) where
  toFun p := (p.1.2, (p.1.1, p.2))
  invFun q := ((q.2.1, q.1), q.2.2)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-! ## 2. The chart -/

/-- **The base chart, as a partial homeomorphism onto a neighbourhood of the section's
zero.** -/
def lixBaseChart (dd : Fin ℓ → ℕ) :
    OpenPartialHomeomorph (ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ))
      (↥sphereOne × baseM dd) :=
  (lixChartReorder dd).toOpenPartialHomeomorph.trans
    (circChart.prod (sphereChartHomeo.prod (cpTowerChart dd)))

theorem zero_mem_lixBaseChart_source :
    ((0, 0) : ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) ∈ (lixBaseChart dd).source := by
  refine ⟨mem_univ _, ?_⟩
  refine ⟨?_, ?_, mem_univ _⟩
  · show (0 : ℝ) ∈ Ioo (-1 : ℝ) 1
    constructor <;> norm_num
  · show sphereQ (0 : ℂ × ℂ × ℝ) < 1
    simp [sphereQ]

theorem lixBaseChart_zero :
    lixBaseChart dd ((0, 0) : ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) = lixZero dd := by
  show (circChart 0, (sphereChartHomeo 0, cpTowerChart dd 0)) = lixZero dd
  have h1 : circChart (0 : ℝ) = southPole := circChartFun_zero
  have h2 : sphereChartHomeo (0 : ℂ × ℂ × ℝ) = negEThree := sphereChartFun_zero
  have h3 : cpTowerChart dd (0 : ∀ j : Fin ℓ, Fin (dd j) → ℂ) = baseYPoint dd :=
    cpBaseChartFun_zero
  rw [h1, h2, h3]
  rfl

end GroupApproximation.CharClass
