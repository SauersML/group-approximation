import GroupApproximation.CharClass.LIXExcisionChart
import GroupApproximation.CharClass.LIXFullChart

/-!
# The relative group of the pair, identified with the local model

Lane `cc-lix-odd`.

`lixBaseChart` and `lixFullChart` have the **same source type**, chart coordinates, but
different open sources, both containing the origin.  Restricting each to the other's source
makes the two agree there, and then one homeomorphism of punctured pairs carries the
neighbourhood of the section's zero onto a neighbourhood of the origin in the local model.

Excision at the point on each side turns that into

```text
H^n(lixN, lixN ∖ {lixZero})  ≅  H^n(ℂ^r, ℂ^r ∖ 0),
```

which is `exc ≫ chartIso` in `cc-thom`'s vocabulary, with `r = lixRank dd`.

## Main results

* `lixChartCommon` — the two restrictions, with their sources equal.
* `lixNbhdHomeo` — the neighbourhood of the zero, homeomorphic to one of the origin.
* `lixRelModelIso` — **the identification with the local model**.
-/

noncomputable section

namespace GroupApproximation.CharClass

open Set CategoryTheory
open GroupApproximation.STW59

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-! ## 1. The two charts, restricted to a common source -/

/-- The base chart, cut down to where the section chart is also defined. -/
def lixBC (dd : Fin ℓ → ℕ) :
    OpenPartialHomeomorph (ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ))
      (↥sphereOne × baseM dd) :=
  (lixBaseChart dd).restrOpen (lixFullChart dd).source (lixFullChart dd).open_source

/-- The section chart, cut down the same way. -/
def lixFC (dd : Fin ℓ → ℕ) :
    OpenPartialHomeomorph (ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ))
      (Fin (lixRank dd) → ℂ) :=
  (lixFullChart dd).restrOpen (lixBaseChart dd).source (lixBaseChart dd).open_source

theorem lixBC_source :
    (lixBC dd).source = (lixBaseChart dd).source ∩ (lixFullChart dd).source :=
  OpenPartialHomeomorph.restrOpen_source _ _ _

theorem lixFC_source :
    (lixFC dd).source = (lixFullChart dd).source ∩ (lixBaseChart dd).source :=
  OpenPartialHomeomorph.restrOpen_source _ _ _

theorem lixBC_source_eq_lixFC_source : (lixBC dd).source = (lixFC dd).source := by
  rw [lixBC_source, lixFC_source, inter_comm]

theorem zero_mem_lixBC_source :
    ((0, 0) : ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) ∈ (lixBC dd).source := by
  rw [lixBC_source]
  exact ⟨zero_mem_lixBaseChart_source, zero_mem_lixFullChart_source⟩

theorem zero_mem_lixFC_source :
    ((0, 0) : ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) ∈ (lixFC dd).source :=
  lixBC_source_eq_lixFC_source ▸ zero_mem_lixBC_source

theorem lixBC_zero : lixBC dd ((0, 0) : ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ))
    = lixZero dd := lixBaseChart_zero

theorem lixFC_zero : lixFC dd ((0, 0) : ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ))
    = (0 : Fin (lixRank dd) → ℂ) := lixFullChart_zero

theorem lixZero_mem_lixBC_target : lixZero dd ∈ (lixBC dd).target := by
  have h := (lixBC dd).map_source (zero_mem_lixBC_source (dd := dd))
  rwa [lixBC_zero] at h

theorem zero_mem_lixFC_target : (0 : Fin (lixRank dd) → ℂ) ∈ (lixFC dd).target := by
  have h := (lixFC dd).map_source (zero_mem_lixFC_source (dd := dd))
  rwa [lixFC_zero] at h

/-! ## 2. The neighbourhoods are homeomorphic -/

/-- **A neighbourhood of the section's zero, homeomorphic to one of the origin.** -/
def lixNbhdHomeo (dd : Fin ℓ → ℕ) : ↥(lixBC dd).target ≃ₜ ↥(lixFC dd).target :=
  (lixBC dd).toHomeomorphSourceTarget.symm.trans
    ((Homeomorph.setCongr lixBC_source_eq_lixFC_source).trans
      (lixFC dd).toHomeomorphSourceTarget)

theorem lixNbhdHomeo_zero :
    (lixNbhdHomeo dd ⟨lixZero dd, lixZero_mem_lixBC_target⟩ : ↥(lixFC dd).target)
      = ⟨(0 : Fin (lixRank dd) → ℂ), zero_mem_lixFC_target⟩ := by
  refine Subtype.ext ?_
  show lixFC dd ((lixBC dd).symm (lixZero dd)) = _
  have hsym : (lixBC dd).symm (lixZero dd)
      = ((0, 0) : ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) := by
    rw [← lixBC_zero (dd := dd)]
    exact (lixBC dd).left_inv zero_mem_lixBC_source
  rw [hsym]
  exact lixFC_zero

/-! ## 3. The identification with the local model -/

/-- **The relative group of the pair, identified with the local model.** -/
def lixRelModelIso (dd : Fin ℓ → ℕ) (n : ℕ) :
    relCohomology (ZMod 2) (lixN dd)
        ({lixZero dd}ᶜ : Set (↥sphereOne × baseM dd)) n
      ≅ relCohomology (ZMod 2) (TopCat.of (Fin (lixRank dd) → ℂ))
        (puncturedSet (lixRank dd)) n :=
  (excisionIsoPoint (lixN dd) (lixZero dd) (lixBC dd).target
      (lixBC dd).open_target lixZero_mem_lixBC_target n).trans
    ((relCohomologyCongrPoint (lixNbhdHomeo dd) lixZero_mem_lixBC_target
        zero_mem_lixFC_target lixNbhdHomeo_zero n).trans
      (excisionIsoPoint (TopCat.of (Fin (lixRank dd) → ℂ)) 0 (lixFC dd).target
        (lixFC dd).open_target zero_mem_lixFC_target n).symm)

end GroupApproximation.CharClass
