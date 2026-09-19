import GroupApproximation.CharClass.LIXSectionDeriv

/-!
# The local homeomorphism at the zero

Lane `cc-lix-odd` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

`CharClass/LIXSectionDeriv.lean` proves that the derivative of the manuscript's section,
read in the charts of `CharClass/LIXSectionChart.lean`, is the continuous linear
equivalence `eulerContinuousLinearEquiv`.  The inverse function theorem then turns that
into an `OpenPartialHomeomorph`, which is exactly the shape `cc-thom`'s
`EulerLocalChart.openPartialHomeomorphChartPair` consumes:

```lean
(e : OpenPartialHomeomorph X Y) {z : X} (hz : z ∈ e.source) {o : Y} (ho : o ∈ e.target)
(h0 : e z = o)
```

This file supplies `e`, `hz`, `ho` and `h0`, with `z` and `o` both the origin.  It also
fixes the single degree index `cc-thom`'s `PuncturedAcyclic` and `topChernClass_ne_zero`
consume, in the added form they asked for rather than as a product.

## Main results

* `trivialBlockChart_zero` — the section's trivial block vanishes at the chart origin.
* `eulerLocalHomeo` — **the local homeomorphism**, with `zero_mem_eulerLocalHomeo_source`,
  `zero_mem_eulerLocalHomeo_target` and `eulerLocalHomeo_zero`.
* `lixTopDegree` — `dim N = 1 + 5 + 2 ∑ⱼ dⱼ`, with `lixTopDegree_eq_two_mul_rank`
  identifying it with twice the rank of `V`.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open GroupApproximation.STW59

set_option linter.unusedSectionVars false

/-! ## 1. The section vanishes at the chart origin -/

/-- The chart is centred at the zero: at `w = 0` and `u = 0` the trivial block of the
section is `(1/2) e₃ + (1/2) (−e₃) = 0`. -/
theorem trivialBlockChart_zero : trivialBlockChart 0 0 = (0 : Fin 3 → ℂ) := by
  funext i
  show ((1 - (1 + (0 : ℝ)) / 2 : ℝ) : ℂ) * eThree i
      + (((1 + (0 : ℝ)) / 2 : ℝ) : ℂ) * sphereChartVec 0 i = 0
  rw [show sphereChartVec 0 i = -eThree i from congrFun sphereChartVec_zero i]
  push_cast
  ring

/-! ## 2. The local homeomorphism -/

/-- **The local homeomorphism at the zero.**  The inverse function theorem applied to the
section's trivial block, read in the charts, whose derivative there is the continuous
linear equivalence `eulerContinuousLinearEquiv`. -/
def eulerLocalHomeo : OpenPartialHomeomorph ChartSrc (Fin 3 → ℂ) :=
  hasStrictFDerivAt_trivialBlockChart.toOpenPartialHomeomorph
    (fun p : ChartSrc => trivialBlockChart p.1 p.2)

theorem eulerLocalHomeo_coe :
    (eulerLocalHomeo : ChartSrc → (Fin 3 → ℂ)) = fun p => trivialBlockChart p.1 p.2 :=
  hasStrictFDerivAt_trivialBlockChart.toOpenPartialHomeomorph_coe

/-- The zero is in the source. -/
theorem zero_mem_eulerLocalHomeo_source : (0 : ChartSrc) ∈ eulerLocalHomeo.source :=
  hasStrictFDerivAt_trivialBlockChart.mem_toOpenPartialHomeomorph_source

/-- The chart carries the zero to the origin. -/
theorem eulerLocalHomeo_zero : eulerLocalHomeo (0 : ChartSrc) = (0 : Fin 3 → ℂ) := by
  rw [show eulerLocalHomeo (0 : ChartSrc)
      = (fun p : ChartSrc => trivialBlockChart p.1 p.2) 0 from
    congrFun eulerLocalHomeo_coe 0]
  exact trivialBlockChart_zero

/-- The origin is in the target. -/
theorem zero_mem_eulerLocalHomeo_target : (0 : Fin 3 → ℂ) ∈ eulerLocalHomeo.target := by
  have h := hasStrictFDerivAt_trivialBlockChart.image_mem_toOpenPartialHomeomorph_target
  rwa [show trivialBlockChart (0 : ChartSrc).1 (0 : ChartSrc).2 = (0 : Fin 3 → ℂ) from
    trivialBlockChart_zero] at h

/-! ## 3. The degree index -/

variable {ℓ : ℕ}

/-- **The top degree of `N = S¹ × S⁵ × ∏ⱼ ℂP^{dⱼ}`**, `1 + 5 + 2 ∑ⱼ dⱼ`.

`cc-thom`'s `PuncturedAcyclic` and `topChernClass_ne_zero` take this as a single natural
number index, never as a product, so it is written in added form: a `2 * _` would force a
cast at every use. -/
def lixTopDegree (dd : Fin ℓ → ℕ) : ℕ := 2 * (∑ j, dd j) + 6

/-- The degree really is twice the rank of `V`, which `LemmaTwoParity.trace_Vmat`
computes as `(∑ⱼ dⱼ) + 3`. -/
theorem lixTopDegree_eq_two_mul_rank (dd : Fin ℓ → ℕ) :
    lixTopDegree dd = 2 * ((∑ j, dd j) + 3) := by
  rw [lixTopDegree]
  ring

end GroupApproximation.CharClass
