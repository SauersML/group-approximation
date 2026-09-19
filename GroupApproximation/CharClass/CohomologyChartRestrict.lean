import GroupApproximation.CharClass.CohomologyProjectiveParity

/-!
# The chart-cover restrictions

The layer under the projective-factor Künneth, matching
`CohomologyKunnethSurjHelp` for the sphere: how the two restrictions of the chart
cover behave on classes pulled back from the base, that they agree on the
intersection, and that the projection of the intersection is injective on
cohomology.

The one statement with no sphere analogue is
`KnCP.mvResU_eq_zero_of_mvResV_eq_zero`: the two pieces of this cover are *not*
symmetric — one is the base and the other is `U × ℂP^d` — but a class vanishing on
the punctured piece automatically vanishes on the chart piece, because the chart
piece is the base and the base injects into the intersection.  That is what
replaces the "both restrictions come from one class" step of the sphere argument.

## Main results

* `KnCP.mvResU_pull_cpPrU`, `KnCP.mvResV_pull_cpPrU`.
* `KnCP.pull_cpPrSub_inter_injective`.
* `KnCP.mvResU_eq_zero_of_mvResV_eq_zero`.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.STW59
open GroupApproximation.CharClass.CPn

namespace GroupApproximation.CharClass

noncomputable section

namespace KnCP

variable (U : Type) [TopologicalSpace U] (d : ℕ)

/-! ## 1. Restriction of a pullback from the base -/

theorem mvResU_pull_cpPrU (m : ℕ) (a : Hmod2 (TopCat.of U) m) :
    (mvResU (chartU U d) (punctU U d) (cp_sup U d) m).hom (pull (cpPrU U d) m a)
      = pull (cpPrSub U d (chartUSet U d)) m a := by
  rw [mvResU_eq_pull, cohPullback_apply_eq, ← pull_comp, sInclusion_comp_cpPrSub]

theorem mvResV_pull_cpPrU (m : ℕ) (a : Hmod2 (TopCat.of U) m) :
    (mvResV (chartU U d) (punctU U d) (cp_sup U d) m).hom (pull (cpPrU U d) m a)
      = pull (cpPrSub U d (punctUSet U d)) m a := by
  rw [mvResV_eq_pull, cohPullback_apply_eq, ← pull_comp, sInclusion_comp_cpPrSub]

/-! ## 2. The two restrictions to the intersection agree -/

theorem mvResWU_mvResU_cp (m : ℕ) (z : Hmod2 (cpProdTop U d) m) :
    (mvResWU (chartU U d) (punctU U d) (cp_sup U d) m).hom
        ((mvResU (chartU U d) (punctU U d) (cp_sup U d) m).hom z)
      = pull (sInclusion (interUSet U d)) m z := by
  rw [mvResWU_eq_pull, mvResU_eq_pull, cohPullback_apply_eq, cohPullback_apply_eq,
    ← pull_comp, subInclusion_comp_sInclusion]

theorem mvResWV_mvResV_cp (m : ℕ) (z : Hmod2 (cpProdTop U d) m) :
    (mvResWV (chartU U d) (punctU U d) (cp_sup U d) m).hom
        ((mvResV (chartU U d) (punctU U d) (cp_sup U d) m).hom z)
      = pull (sInclusion (interUSet U d)) m z := by
  rw [mvResWV_eq_pull, mvResV_eq_pull, cohPullback_apply_eq, cohPullback_apply_eq,
    ← pull_comp, subInclusion_comp_sInclusion]

/-! ## 3. The projection of the intersection is injective -/

theorem pull_cpPrSub_inter_injective (m : ℕ) :
    Function.Injective (pull (cpPrSub U d (interUSet U d)) m) := by
  intro c₁ c₂ hc
  refine pull_knPrY_injective U (2 * d + 1) (spherePoint (2 * d + 1)) m ?_
  refine (interPullEquiv U d m).injective ?_
  show pull (cmap (interHomotopyEquiv U d).toFun) m _
    = pull (cmap (interHomotopyEquiv U d).toFun) m _
  rw [pull_interHE_prU, pull_interHE_prU]
  exact hc

/-! ## 4. Vanishing on the punctured piece forces vanishing on the chart -/

set_option maxHeartbeats 1000000 in
/-- **The asymmetric step.**  The chart piece is the base, and the base injects into
the intersection, so a class vanishing on the punctured piece vanishes on the chart
piece as well. -/
theorem mvResU_eq_zero_of_mvResV_eq_zero (m : ℕ) (z : Hmod2 (cpProdTop U d) m)
    (h : (mvResV (chartU U d) (punctU U d) (cp_sup U d) m).hom z = 0) :
    (mvResU (chartU U d) (punctU U d) (cp_sup U d) m).hom z = 0 := by
  obtain ⟨c, hc⟩ := exists_pull_cpPrSub_chart U d m
    ((mvResU (chartU U d) (punctU U d) (cp_sup U d) m).hom z)
  have hzero : pull (cpPrSub U d (interUSet U d)) m c = 0 := by
    rw [← mvResWU_pull_cpPrSub, hc, mvResWU_mvResU_cp, ← mvResWV_mvResV_cp, h,
      map_zero]
  have hc0 : c = 0 := by
    refine pull_cpPrSub_inter_injective U d m ?_
    rw [hzero, pull_zero]
  rw [← hc, hc0, pull_zero]

end KnCP

end

end GroupApproximation.CharClass
