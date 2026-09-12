import GroupApproximation.CharClass.CohomologyChartCover

/-!
# No odd cohomology survives a projective factor

`cc-projective`'s `noOddCohomology_CP` is the statement for a single `ℂP^d`.
`cc-wu`'s base is a **product** of projective spaces, so what the even side needs
is that a projective factor preserves the absence of odd cohomology.

The proof is the chart-cover Mayer–Vietoris and the parity corollary of the sphere
Künneth, and nothing else.  In odd degree both pieces of the cover vanish, one by
hypothesis and one by induction, so the class is a connecting-map image from the
intersection, which is `A × S^{2d+1}`, in **even** degree.  There the sphere
statement `(L)` applies: an even class of a product with an odd sphere is pulled
back from the base, and a pullback from the base on the intersection is the
restriction of a class on the chart piece, hence killed by the connecting map.

## Main results

* `KnCP.mvDelta_pull_cpPrSub_inter` — the connecting map kills a pullback from `U`.
* `KnCP.noOddCohomology_prod_CP` — a projective factor preserves the vanishing.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.STW59
open GroupApproximation.CharClass.CPn

namespace GroupApproximation.CharClass

noncomputable section

namespace KnCP

variable (U : Type) [TopologicalSpace U] (d : ℕ)

/-! ## 1. The connecting map kills a pullback from the base -/

theorem mvResWU_pull_cpPrSub (m : ℕ) (c : Hmod2 (TopCat.of U) m) :
    (mvResWU (chartU U d) (punctU U d) (cp_sup U d) m).hom
        (pull (cpPrSub U d (chartUSet U d)) m c)
      = pull (cpPrSub U d (interUSet U d)) m c := by
  rw [mvResWU_eq_pull, cohPullback_apply_eq, ← pull_comp, subInclusion_comp_cpPrSub]

theorem mvDelta_pull_cpPrSub_inter (m : ℕ) (c : Hmod2 (TopCat.of U) m) :
    (mvDelta (chartU U d) (punctU U d) (cp_sup U d) m).hom
      (pull (cpPrSub U d (interUSet U d)) m c) = 0 := by
  refine (mvExactW (chartU U d) (punctU U d) (cp_sup U d) m _).2 ?_
  refine ⟨pull (cpPrSub U d (chartUSet U d)) m c, 0, ?_⟩
  rw [mvResWU_pull_cpPrSub, map_zero, add_zero]

/-! ## 2. The two pieces vanish in odd degree -/

theorem isZero_chart_piece (k : ℕ) (hU : IsZero (Hmod2 (TopCat.of U) k)) :
    IsZero (Hmod2 (TopCat.of ↥(chartUSet U d)) k) :=
  isZero_of_linearEquiv (pullEquivOfHomotopyEquiv (chartHomotopyEquiv U d) k) hU

theorem isZero_punct_piece (k : ℕ)
    (hP : IsZero (Hmod2 (TopCat.of (U × CP d)) k)) :
    IsZero (Hmod2 (TopCat.of ↥(punctUSet U d)) k) :=
  isZero_of_linearEquiv (pullEquivOfHomotopyEquiv (punctHomotopyEquiv U d) k) hP

/-! ## 3. A projective factor preserves the vanishing -/

set_option maxHeartbeats 1000000 in
/-- **The induction step.**  If `U` and `U × ℂP^d` have no odd cohomology, neither
does `U × ℂP^{d+1}`. -/
theorem eq_zero_odd_prod_CP_succ (hU : KnHemi.NoOddCohomology U)
    (hP : KnHemi.NoOddCohomology (U × CP d)) (k : ℕ) (hk : Odd k)
    (z : Hmod2 (cpProdTop U d) k) : z = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by rw [Nat.odd_iff] at hk; omega⟩
  -- both restrictions vanish
  have hzU : (mvResU (chartU U d) (punctU U d) (cp_sup U d) (j + 1)).hom z = 0 := by
    haveI := ModuleCat.subsingleton_of_isZero
      (isZero_chart_piece U d (j + 1) (hU (j + 1) hk))
    exact Subsingleton.elim _ _
  have hzV : (mvResV (chartU U d) (punctU U d) (cp_sup U d) (j + 1)).hom z = 0 := by
    haveI := ModuleCat.subsingleton_of_isZero
      (isZero_punct_piece U d (j + 1) (hP (j + 1) hk))
    exact Subsingleton.elim _ _
  obtain ⟨w, hw⟩ := (mvExactX (chartU U d) (punctU U d) (cp_sup U d) j z).1 ⟨hzU, hzV⟩
  -- the intersection is `U × S^{2d+1}`, and `j` is even
  obtain ⟨w', hw'⟩ : ∃ w', pull (cmap (interHomotopyEquiv U d).toFun) j w' = w :=
    ⟨(interPullEquiv U d j).symm w, (interPullEquiv U d j).apply_symm_apply w⟩
  obtain ⟨c, hc⟩ := KnHemi.even_pulled_back_of_odd_sphere U (2 * d + 1) (by omega) hU
    (by rw [Nat.odd_iff]; omega) j (by rw [Nat.even_iff]; rw [Nat.odd_iff] at hk; omega) w'
  rw [← hw, ← hw', hc, pull_interHE_prU, mvDelta_pull_cpPrSub_inter]

/-- **A projective factor preserves the absence of odd cohomology.** -/
theorem noOddCohomology_prod_CP (hU : KnHemi.NoOddCohomology U) :
    ∀ d : ℕ, KnHemi.NoOddCohomology (U × CP d) := by
  intro d
  induction d with
  | zero =>
    intro j hj
    exact isZero_of_linearEquiv (cohProdContractible U (CP 0) j) (hU j hj)
  | succ e ih =>
    intro j hj
    rw [ModuleCat.isZero_iff_subsingleton]
    refine ⟨fun z w => ?_⟩
    rw [eq_zero_odd_prod_CP_succ U e hU ih j hj z,
      eq_zero_odd_prod_CP_succ U e hU ih j hj w]

end KnCP

end

end GroupApproximation.CharClass
