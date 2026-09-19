import GroupApproximation.CharClass.LIXCircleChart
import GroupApproximation.CharClass.LIXSphereChart
import GroupApproximation.CharClass.LIXProjectiveBaseChart
import GroupApproximation.CharClass.LemmaTwoStepC

/-!
# The base chart, assembled

Lane `cc-lix-odd`.

The three factors are green: the circle at its south pole, the five-sphere at `-e₃`, and
the projective directions at their base points.  This file multiplies them into a single
map from the chart coordinates **into** `lixN dd`, carrying the origin to `lixZero dd`.

This is the object that was missing when `hinj` was described as one application: the
existing chart reads the section and lands in the *fibre*, while restricting a relative
class needs a map into the *base*.

## What this is and is not

It is a continuous map with the zero pinned. It is **not yet** an
`OpenPartialHomeomorph`: for that each factor must be upgraded, which for the projective
directions is immediate from the affine chart's open embedding, and for the five-sphere
needs its inverse on the open lower hemisphere. The circle factor is already there.

## Main results

* `circChartFun_zero` — the circle chart's origin is the south pole.
* `lixBaseChartFun` — **the base chart**, with `continuous_lixBaseChartFun`.
* `lixBaseChartFun_zero` — the origin goes to `lixZero dd`.
-/

noncomputable section

namespace GroupApproximation.CharClass

open GroupApproximation.STW59

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-! ## 1. The circle chart at the origin -/

theorem circChartFun_zero : circChartFun 0 = southPole := by
  refine Subtype.ext ?_
  show circChartVec (circClamp 0) = _
  have h0 : circClamp (0 : ℝ) = 0 := by
    rw [circClamp]
    norm_num
  rw [h0]
  apply WithLp.ofLp_injective
  funext i
  fin_cases i
  · simp [circChartVec, southPole]
  · show -Real.sqrt (1 - (0:ℝ) ^ 2) = _
    norm_num [southPole]

/-! ## 2. The base chart -/

/-- **The base chart**: chart coordinates to a neighbourhood of the section's zero. -/
def lixBaseChartFun (dd : Fin ℓ → ℕ)
    (p : ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) : ↥sphereOne × baseM dd :=
  (circChartFun p.1.2, (sphereChartFun p.1.1, cpBaseChartFun dd p.2))

theorem continuous_lixBaseChartFun : Continuous (lixBaseChartFun dd) := by
  refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_)
  · exact continuous_circChartFun.comp (continuous_snd.comp continuous_fst)
  · exact continuous_sphereChartFun.comp (continuous_fst.comp continuous_fst)
  · exact continuous_cpBaseChartFun.comp continuous_snd

/-- **The origin of the chart is the section's zero.** -/
theorem lixBaseChartFun_zero :
    lixBaseChartFun dd (0 : ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) = lixZero dd := by
  show (circChartFun 0, (sphereChartFun 0, cpBaseChartFun dd 0)) = _
  rw [circChartFun_zero, sphereChartFun_zero, cpBaseChartFun_zero]
  rfl

end GroupApproximation.CharClass
