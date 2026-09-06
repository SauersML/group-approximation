import GroupApproximation.CharClass.LIXSectionLocalHomeo
import GroupApproximation.CharClass.EulerLocalChart
import GroupApproximation.CharClass.RelativeLocalModel

/-!
# The section's zero as a homeomorphism of punctured pairs

Lane `cc-lix-odd` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

`CharClass/LIXSectionLocalHomeo.lean` produced `eulerLocalHomeo`, the local homeomorphism
at the section's single zero, from the inverse function theorem applied to the strict
derivative of `CharClass/LIXSectionDeriv.lean`.  `cc-thom`'s `ThomSectionDetect.lean`
reduced the odd side of Step C to one geometric statement and named `eulerLocalHomeo` as
its route.

This file takes the two steps between them that belong to this lane:

* `lixChartPairHomeo` — the chart as a homeomorphism of **punctured** pairs, via
  `openPartialHomeomorphChartPair`.  Its four inputs are exactly the four facts
  `LIXSectionLocalHomeo` already proves, so this is an application, not a construction.
* `lixLocalRelIso` — the induced isomorphism on relative cohomology, via
  `relCohomologyCongrPoint`.  **Mod 2 a homeomorphism of pairs induces an isomorphism, so
  no degree computation appears anywhere.**

The nondegeneracy of the zero enters exactly once, in `eulerLocalHomeo`, and it enters as
the invertibility of a derivative rather than as a homotopy or a degree.

## What this does and does not close

It supplies the *chart* half of `cc-thom`'s remaining hypothesis: the identification of the
chart's relative group with the local model. It does **not** by itself give their
`hinj`, which is injectivity of the chart composite **after the section**, and that
composite mentions `cc-relative`'s section map. Note also that injectivity of the composite
implies injectivity of the section map whatever the middle object is, so no choice of the
latter can avoid that; in particular taking it to be an isomorphism makes the hypothesis
exactly injectivity of the section map and the chart contributes nothing.

## Main results

* `lixChartPairHomeo` — the punctured-pair homeomorphism at the zero.
* `lixLocalRelIso` — its relative cohomology isomorphism, in every degree.
-/

noncomputable section

namespace GroupApproximation.CharClass

open CategoryTheory

set_option linter.unusedSectionVars false

/-! ## 1. The punctured pair -/

/-- **The section's chart, as a homeomorphism of punctured pairs.**  Source and target are
the chart's source and target with the zero and the origin removed. -/
def lixChartPairHomeo :
    ↥((Subtype.val : ↥eulerLocalHomeo.source → ChartSrc) ⁻¹' ({0}ᶜ : Set ChartSrc))
      ≃ₜ ↥((Subtype.val : ↥eulerLocalHomeo.target → (Fin 3 → ℂ)) ⁻¹'
        ({0}ᶜ : Set (Fin 3 → ℂ))) :=
  openPartialHomeomorphChartPair eulerLocalHomeo zero_mem_eulerLocalHomeo_source
    zero_mem_eulerLocalHomeo_target eulerLocalHomeo_zero

/-! ## 2. The relative cohomology isomorphism -/

/-- **The chart identifies the two relative groups, in every degree.**  Mod 2 a
homeomorphism of pairs induces an isomorphism, so this needs no degree computation and no
Künneth theorem; the only input is that the section's derivative at its zero is
invertible. -/
def lixLocalRelIso (n : ℕ) :
    relCohomology (ZMod 2) (TopCat.of ↥eulerLocalHomeo.source)
        ((Subtype.val : ↥eulerLocalHomeo.source → ChartSrc) ⁻¹' ({0}ᶜ : Set ChartSrc)) n
      ≅ relCohomology (ZMod 2) (TopCat.of ↥eulerLocalHomeo.target)
        ((Subtype.val : ↥eulerLocalHomeo.target → (Fin 3 → ℂ)) ⁻¹'
          ({0}ᶜ : Set (Fin 3 → ℂ))) n :=
  relCohomologyCongrPoint eulerLocalHomeo.toHomeomorphSourceTarget
    zero_mem_eulerLocalHomeo_source zero_mem_eulerLocalHomeo_target
    (Subtype.ext (by simp [eulerLocalHomeo_zero])) n

end GroupApproximation.CharClass
