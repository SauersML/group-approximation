import GroupApproximation.CharClass.LIXSectionManuscript
import GroupApproximation.CharClass.ProjectiveSpaceChart

/-!
# The projective factor of the base chart

Lane `cc-lix-odd`, the third of the base chart's three factors, and the shortest: the
affine chart of `ℂP^d` is already a homeomorphism onto an open set, so this file only runs
it over the tower and pins the origin.

## A duplication hazard, worse than the previous one

`basePoint` exists twice, as `AlgTop.CPn.basePoint` and `CharClass.CPn.basePoint`, with
**identical bodies** over the same `CP d`.  Unlike the two `entry`s, which are `abbrev`
and so interchange during unification, these are plain `def`s: they are definitionally
equal only at default transparency, so `exact` and `rfl` cross them while `rw` and `simp`
do not.  `chartAt_zero` concludes in one of them and `baseYPoint` is built from the other,
so the bridge below is needed and is `rfl`.

## Main results

* `basePoint_eq` — the bridge between the two duplicate definitions.
* `cpBaseChartFun` — the projective factor, over the whole tower.
* `cpBaseChartFun_zero` — the origin is the section's zero on this factor.
-/

noncomputable section

namespace GroupApproximation.CharClass

open GroupApproximation.STW59

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-! ## 1. The bridge -/

/-- **The two `basePoint`s agree.**  Both are `rankOneProj (baseVec d)` with the same
membership proof; they are `def`s rather than `abbrev`s, so this must be stated. -/
theorem basePoint_eq (d : ℕ) : AlgTop.CPn.basePoint d = CPn.basePoint d := rfl

/-! ## 2. The chart over the tower -/

/-- **The projective factor of the base chart.** -/
def cpBaseChartFun (dd : Fin ℓ → ℕ) (z : ∀ j : Fin ℓ, Fin (dd j) → ℂ) : baseY dd :=
  fun j => CPn.chartAt (z j)

theorem continuous_cpBaseChartFun : Continuous (cpBaseChartFun dd) :=
  continuous_pi fun j => CPn.continuous_chartAt.comp (continuous_apply j)

/-- The origin of the chart is the section's zero on this factor. -/
theorem cpBaseChartFun_zero : cpBaseChartFun dd 0 = baseYPoint dd := by
  funext j
  show CPn.chartAt (0 : Fin (dd j) → ℂ) = _
  rw [CPn.chartAt_zero]
  exact (basePoint_eq (dd j)).symm

end GroupApproximation.CharClass
