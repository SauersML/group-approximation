import GroupApproximation.CharClass.CohomologyChartFlat

/-!
# Two unconditional components of the flatness loop

The projective-factor Künneth closes through a loop: the decomposition at level
`d` gives that restrictions to the intersection are pulled back from the base,
which gives surjectivity of the restriction to the punctured piece, which with the
kernel statement gives the decomposition at level `d + 1`.

Two parts of that loop need no induction and are recorded here.

**A class that extends is flat.**  If `w` is the restriction of a class on the
whole product, its restriction to the intersection also factors through the chart
piece, and the chart piece *is* the base.  This is the structural reason flatness
and surjectivity are equivalent rather than independent, and it is why the loop
cannot be broken by proving flatness directly: flatness for a general `w` is
exactly surjectivity.

**The bottom of the loop.**  At `d = 0` the punctured piece is `U × ℂP^0`, and
`ℂP^0` is a point, so every class on it is pulled back from `U` outright.

## Main results

* `KnCP.exists_flat_of_mvResV` — a class that extends is flat.
* `KnCP.exists_pull_cpPrSub_punct_zero` — the punctured piece at `d = 0` is the base.
* `KnCP.exists_flat_zero` — flatness at `d = 0`.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.STW59
open GroupApproximation.CharClass.CPn

namespace GroupApproximation.CharClass

noncomputable section

namespace KnCP

variable (U : Type) [TopologicalSpace U] (d : ℕ)

set_option maxHeartbeats 1000000 in
/-- **A class that extends is flat.**  Its restriction to the intersection factors
through the chart piece, which is the base. -/
theorem exists_flat_of_mvResV (k : ℕ) (z : Hmod2 (cpProdTop U d) k) :
    ∃ e : Hmod2 (TopCat.of U) k,
      (mvResWV (chartU U d) (punctU U d) (cp_sup U d) k).hom
          ((mvResV (chartU U d) (punctU U d) (cp_sup U d) k).hom z)
        = pull (cpPrSub U d (interUSet U d)) k e := by
  obtain ⟨e, he⟩ := exists_pull_cpPrSub_chart U d k
    ((mvResU (chartU U d) (punctU U d) (cp_sup U d) k).hom z)
  refine ⟨e, ?_⟩
  rw [mvResWV_mvResV_cp, ← mvResWU_mvResU_cp, ← he, mvResWU_pull_cpPrSub]

/-! ## The bottom of the loop -/

set_option maxHeartbeats 1000000 in
/-- At `d = 0` the punctured piece is the base: `ℂP^0` is a point. -/
theorem exists_pull_cpPrSub_punct_zero (k : ℕ)
    (w : Hmod2 (TopCat.of ↥(punctUSet U 0)) k) :
    ∃ c : Hmod2 (TopCat.of U) k, pull (cpPrSub U 0 (punctUSet U 0)) k c = w := by
  obtain ⟨y, hy⟩ : ∃ y : Hmod2 (TopCat.of (U × CP 0)) k,
      pull (cmap (punctHomotopyEquiv U 0).toFun) k y = w :=
    ⟨(punctPullEquiv U 0 k).symm w, (punctPullEquiv U 0 k).apply_symm_apply w⟩
  obtain ⟨c, hc⟩ : ∃ c : Hmod2 (TopCat.of U) k,
      pull (fstMap U (CP 0)) k c = y := by
    refine ⟨(cohProdContractible U (CP 0) k).symm y, ?_⟩
    rw [← cohProdContractible_apply]
    exact (cohProdContractible U (CP 0) k).apply_symm_apply y
  refine ⟨c, ?_⟩
  rw [← hy, ← hc, pull_punctHE_prU]

set_option maxHeartbeats 1000000 in
/-- **Flatness at the bottom of the loop.** -/
theorem exists_flat_zero (k : ℕ) (w : Hmod2 (TopCat.of ↥(punctUSet U 0)) k) :
    ∃ e : Hmod2 (TopCat.of U) k,
      (mvResWV (chartU U 0) (punctU U 0) (cp_sup U 0) k).hom w
        = pull (cpPrSub U 0 (interUSet U 0)) k e := by
  obtain ⟨c, hc⟩ := exists_pull_cpPrSub_punct_zero U k w
  refine ⟨c, ?_⟩
  rw [← hc, mvResWV_eq_pull, cohPullback_apply_eq, ← pull_comp,
    subInclusion_comp_cpPrSub]

end KnCP

end

end GroupApproximation.CharClass
