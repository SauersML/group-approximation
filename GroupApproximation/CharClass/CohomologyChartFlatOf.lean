import GroupApproximation.CharClass.CohomologyChartCoverOf
import GroupApproximation.CharClass.CohomologyChartRankTwo
import GroupApproximation.CharClass.ProjectiveSpaceComputationOf

/-!
# Flat classes and the rank-two decomposition of the chart cover, over a field

The coefficient-generic forms of `ProjectiveSpaceInterVanish` (the even-degree part),
`CohomologyChartFlat`, `CohomologyChartFlatBase` and `CohomologyChartRankTwo`.

**The one sign.**  `CohomologyChartRankTwo.decomposition_zero` removes the pulled-back part of a
class by adding it, which over `F₂` is subtracting it.  Over `K` it is subtracted.

## Main declarations

* `CPn.eq_zero_interSpace_evenOf` — positive even degrees vanish on the intersection.
* `pull_cpPrCP_inter_eq_zeroOf`, `exists_flat_of_mvResVOf`, `exists_flat_zeroOf`.
* `mvResVOf_surjective_zero`, `decomposition_zeroOf` — **the Künneth decomposition with a `ℂP¹`
  factor**, over `K`.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney
open GroupApproximation.STW59
open GroupApproximation.CharClass.CPn

namespace GroupApproximation.CharClass

noncomputable section

namespace CPn

/-- **Every class of positive even degree on the intersection vanishes**, over `K`: `2i` is even
and `2d+1` is odd. -/
theorem eq_zero_interSpace_evenOf (K : Type) [Field K] (d i : ℕ) (hi : i ≠ 0)
    (a : Hmod K (interSpace d) (2 * i)) : a = 0 :=
  (hasSphereCohomologyOf_interSpace K d).2.2 (2 * i) (by omega) (by omega) a

end CPn

namespace KnCP

variable (K : Type) [Field K] (U : Type) [TopologicalSpace U] (d : ℕ)

/-! ## 1. Classes from the projective factor die on the intersection -/

theorem pull_interToInterSpace_eq_zeroOf (i : ℕ) (hi : i ≠ 0)
    (a : Hmod K (interSpace d) (2 * i)) :
    pull (interToInterSpace U d) (2 * i) a = 0 := by
  rw [CPn.eq_zero_interSpace_evenOf K d i hi a, pull_zero]

/-- **A class pulled back from the projective factor dies on the intersection in positive even
degree**, over `K`. -/
theorem pull_cpPrCP_inter_eq_zeroOf (i : ℕ) (hi : i ≠ 0)
    (c : Hmod K (CPtop (d + 1)) (2 * i)) :
    pull (sInclusion (interUSet U d)) (2 * i) (pull (cpPrCP U d) (2 * i) c) = 0 := by
  rw [← pull_comp, ← interToInterSpace_comp, pull_comp,
    pull_interToInterSpace_eq_zeroOf K U d i hi]

/-! ## 2. Flatness -/

set_option maxHeartbeats 1000000 in
/-- **A class that extends is flat**, over `K`. -/
theorem exists_flat_of_mvResVOf (k : ℕ) (z : Hmod K (cpProdTop U d) k) :
    ∃ e : Hmod K (TopCat.of U) k,
      (mvResWVOf K (chartU U d) (punctU U d) (cp_sup U d) k).hom
          ((mvResVOf K (chartU U d) (punctU U d) (cp_sup U d) k).hom z)
        = pull (cpPrSub U d (interUSet U d)) k e := by
  obtain ⟨e, he⟩ := exists_pull_cpPrSub_chartOf K U d k
    ((mvResUOf K (chartU U d) (punctU U d) (cp_sup U d) k).hom z)
  refine ⟨e, ?_⟩
  rw [mvResWVOf_mvResVOf_cp, ← mvResWUOf_mvResUOf_cp, ← he, mvResWUOf_pull_cpPrSub]

set_option maxHeartbeats 1000000 in
/-- At `d = 0` the punctured piece is the base, over `K`: `ℂP^0` is a point. -/
theorem exists_pull_cpPrSub_punct_zeroOf (k : ℕ)
    (w : Hmod K (TopCat.of ↥(punctUSet U 0)) k) :
    ∃ c : Hmod K (TopCat.of U) k, pull (cpPrSub U 0 (punctUSet U 0)) k c = w := by
  obtain ⟨y, hy⟩ : ∃ y : Hmod K (TopCat.of (U × CP 0)) k,
      pull (cmap (punctHomotopyEquiv U 0).toFun) k y = w :=
    ⟨(punctPullEquivOf K U 0 k).symm w, (punctPullEquivOf K U 0 k).apply_symm_apply w⟩
  obtain ⟨c, hc⟩ : ∃ c : Hmod K (TopCat.of U) k,
      pull (fstMap U (CP 0)) k c = y := by
    refine ⟨(cohProdContractibleOf K U (CP 0) k).symm y, ?_⟩
    have happ : cohProdContractibleOf K U (CP 0) k ((cohProdContractibleOf K U (CP 0) k).symm y)
        = pull (fstMap U (CP 0)) k ((cohProdContractibleOf K U (CP 0) k).symm y) := by
      show pull (cmap (prodContractibleEquiv U (CP 0)).toFun) k _ = _
      rw [prodContractibleEquiv_toFun]
    rw [← happ]
    exact (cohProdContractibleOf K U (CP 0) k).apply_symm_apply y
  refine ⟨c, ?_⟩
  rw [← hy, ← hc, pull_punctHE_prUOf]

set_option maxHeartbeats 1000000 in
/-- **Flatness at the bottom of the loop**, over `K`. -/
theorem exists_flat_zeroOf (k : ℕ) (w : Hmod K (TopCat.of ↥(punctUSet U 0)) k) :
    ∃ e : Hmod K (TopCat.of U) k,
      (mvResWVOf K (chartU U 0) (punctU U 0) (cp_sup U 0) k).hom w
        = pull (cpPrSub U 0 (interUSet U 0)) k e := by
  obtain ⟨c, hc⟩ := exists_pull_cpPrSub_punct_zeroOf K U k w
  refine ⟨c, ?_⟩
  rw [← hc, mvResWVOf_eq_pull, cohPullbackK_apply_eq, ← pull_comp,
    subInclusion_comp_cpPrSub]

/-! ## 3. Rank two -/

/-- **The restriction to the punctured piece is onto at the bottom**, over `K`. -/
theorem mvResVOf_surjective_zero (k : ℕ) (w : Hmod K (TopCat.of ↥(punctUSet U 0)) k) :
    ∃ z : Hmod K (cpProdTop U 0) k,
      (mvResVOf K (chartU U 0) (punctU U 0) (cp_sup U 0) k).hom z = w := by
  obtain ⟨c, hc⟩ := exists_pull_cpPrSub_punct_zeroOf K U k w
  exact ⟨pull (cpPrU U 0) k c, by rw [mvResVOf_pull_cpPrU, hc]⟩

set_option maxHeartbeats 1000000 in
/-- **The Künneth decomposition with a `ℂP^1` factor**, over `K`. -/
theorem decomposition_zeroOf (m : ℕ)
    (z : Hmod K (cpProdTop U 0) (2 * 0 + 1 + m + 1)) :
    ∃ (a : Hmod K (TopCat.of U) (2 * 0 + 1 + m + 1)) (b : Hmod K (TopCat.of U) m),
      z = pull (cpPrU U 0) (2 * 0 + 1 + m + 1) a
        + cohCast (aw_degree_left_succ (2 * 0 + 1) m)
            (cup (cpTopOf K U 0) (pull (cpPrU U 0) m b)) := by
  obtain ⟨a, ha⟩ := exists_pull_cpPrSub_punct_zeroOf K U (2 * 0 + 1 + m + 1)
    ((mvResVOf K (chartU U 0) (punctU U 0) (cp_sup U 0) (2 * 0 + 1 + m + 1)).hom z)
  have hz : (mvResVOf K (chartU U 0) (punctU U 0) (cp_sup U 0)
      (2 * 0 + 1 + m + 1)).hom
      (z - pull (cpPrU U 0) (2 * 0 + 1 + m + 1) a) = 0 := by
    rw [map_sub, mvResVOf_pull_cpPrU, ha, sub_self]
  obtain ⟨b, hb⟩ := exists_of_mvResVOf_eq_zero K U 0 m _ hz
  refine ⟨a, b, ?_⟩
  rw [← hb, add_sub_cancel]

end KnCP

end

end GroupApproximation.CharClass
