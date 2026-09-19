import GroupApproximation.CharClass.LIXBaseChartHomeo
import GroupApproximation.CharClass.RelativeLocal
import GroupApproximation.CharClass.RelativeLocalModel

/-!
# Excision at the section's zero

Lane `cc-lix-odd`.

`lixBaseChart` is a partial homeomorphism from chart coordinates onto an open neighbourhood
of the section's zero.  Excision at the point moves the relative group of the pair
`(lixN, lixN ∖ {lixZero})` onto that neighbourhood, and the chart then moves it onto the
chart coordinates.

Both steps are `cc-relative`'s: `excisionIsoPoint` for the first, `relCohomologyCongrPoint`
for the second, the latter taking exactly the marked-point data `lixBaseChart` provides.

## Main results

* `lixZero_mem_lixBaseChart_target` — the zero is in the neighbourhood.
* `lixBaseRelIso` — **the relative group of the pair, on chart coordinates**.
-/

noncomputable section

namespace GroupApproximation.CharClass

open Set CategoryTheory
open GroupApproximation.STW59

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-! ## 1. The ambient is `T1`

`lixN` is a `def`, so instance search does not unfold it and the `T1Space` hypothesis of
`excisionIsoPoint` is not found even though the underlying product carries it. -/

instance instT1SpaceLixN (dd : Fin ℓ → ℕ) : T1Space ↥(lixN dd) :=
  inferInstanceAs (T1Space (↥sphereOne × baseM dd))

/-! ## 2. The zero lies in the chart's image -/

theorem lixZero_mem_lixBaseChart_target :
    lixZero dd ∈ (lixBaseChart dd).target := by
  have h := (lixBaseChart dd).map_source
    (zero_mem_lixBaseChart_source (dd := dd))
  rwa [lixBaseChart_zero] at h

/-! ## 3. Excision, then the chart -/

/-- **The relative group of the pair, carried onto chart coordinates.**

The first isomorphism is excision at the point, onto the chart's image; the second is the
chart itself, as a homeomorphism of punctured pairs. -/
def lixBaseRelIso (dd : Fin ℓ → ℕ) (n : ℕ) :
    relCohomology (ZMod 2) (lixN dd)
        ({lixZero dd}ᶜ : Set (↥sphereOne × baseM dd)) n
      ≅ relCohomology (ZMod 2) (TopCat.of ↥(lixBaseChart dd).source)
        ((Subtype.val : ↥(lixBaseChart dd).source →
          ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) ⁻¹'
          ({(0, 0)}ᶜ : Set (ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ)))) n :=
  (excisionIsoPoint (lixN dd) (lixZero dd) (lixBaseChart dd).target
      (lixBaseChart dd).open_target lixZero_mem_lixBaseChart_target n).trans
    (relCohomologyCongrPoint (lixBaseChart dd).toHomeomorphSourceTarget
      (zero_mem_lixBaseChart_source (dd := dd)) lixZero_mem_lixBaseChart_target
      (Subtype.ext (by simp [lixBaseChart_zero])) n).symm

end GroupApproximation.CharClass
