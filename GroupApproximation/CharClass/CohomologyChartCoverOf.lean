import GroupApproximation.CharClass.CohomologyChartSurj
import GroupApproximation.CharClass.MayerVietorisPullOf
import GroupApproximation.CharClass.CohomologyDeltaCupOf
import GroupApproximation.CharClass.CohomologyKunnethDecompOf
import GroupApproximation.CharClass.CohomologyKunnethSplitOf
import GroupApproximation.CharClass.CohomologyKunnethHemiOf

/-!
# The chart cover of `U × ℂP^{d+1}` over a field: the bottom of the tower

The coefficient-generic forms of `CohomologyChartCover`, the two Mayer–Vietoris lemmas of
`CohomologyProjectiveParity`, `CohomologyChartRestrict`, `CohomologyChartTop` and
`CohomologyChartSurj`.  The spaces, the cover and the homotopy equivalences are coefficient-free
and are the `F₂` files' own; only the cohomological statements are restated over a field `K`,
on top of the Mayer–Vietoris sequence over a field (`MayerVietorisElementOf`/`PullOf`), its
connecting map (`CohomologyDeltaCupOf`) and lix-coeff's Künneth decomposition with a sphere factor
(`CohomologyKunnethDecompOf`).

No sign enters: every Mayer–Vietoris restriction used here is an honest pullback
(`MayerVietorisPullOf`), and the connecting map is linear over the base with the class on the
right (`MVDelta.mvDeltaOf_cup`).

## Main declarations

* `exists_pull_cpPrSub_chartOf`, `interPullEquivOf`, `punctPullEquivOf`.
* `mvResUOf_eq_zero_of_mvResVOf_eq_zero` — vanishing on the punctured piece forces vanishing on
  the chart piece.
* `cpTopOf` — the top power of the tautological class, by the connecting map.
* `exists_of_mvResVOf_eq_zero` — the kernel of the restriction to the punctured piece is
  `cpTopOf ⌣ (pullbacks)`.
* `mvResVOf_surjective_of_lt` — surjectivity of the restriction below the sphere dimension.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney
open GroupApproximation.STW59
open GroupApproximation.CharClass.CPn

namespace GroupApproximation.CharClass

noncomputable section

namespace KnCP

variable (K : Type) [Field K] (U : Type) [TopologicalSpace U] (d : ℕ)

/-! ## 1. The pieces, over `K` -/

/-- **Every class on the chart piece is pulled back from `U`**, over `K`. -/
theorem exists_pull_cpPrSub_chartOf (m : ℕ) (a : Hmod K (TopCat.of ↥(chartUSet U d)) m) :
    ∃ c : Hmod K (TopCat.of U) m, pull (cpPrSub U d (chartUSet U d)) m c = a := by
  refine ⟨(pullEquivOfHomotopyEquivOf K (chartHomotopyEquiv U d) m).symm a, ?_⟩
  rw [cpPrSub_chart_eq]
  exact (pullEquivOfHomotopyEquivOf K (chartHomotopyEquiv U d) m).apply_symm_apply a

/-- Pulling back along the intersection identification is a linear isomorphism over `K`. -/
def interPullEquivOf (k : ℕ) :
    Hmod K (TopCat.of (U × Sphere (2 * d + 1))) k ≃ₗ[K] Hmod K (TopCat.of ↥(interUSet U d)) k :=
  pullEquivOfHomotopyEquivOf K (interHomotopyEquiv U d) k

/-- Pulling back along the punctured identification is a linear isomorphism over `K`. -/
def punctPullEquivOf (k : ℕ) :
    Hmod K (TopCat.of (U × CP d)) k ≃ₗ[K] Hmod K (TopCat.of ↥(punctUSet U d)) k :=
  pullEquivOfHomotopyEquivOf K (punctHomotopyEquiv U d) k

theorem pull_interHE_prUOf (k : ℕ) (c : Hmod K (TopCat.of U) k) :
    pull (cmap (interHomotopyEquiv U d).toFun) k (pull (knPrY U (2 * d + 1)) k c)
      = pull (cpPrSub U d (interUSet U d)) k c := by
  rw [← pull_comp, interHE_comp_prU]

theorem pull_punctHE_prUOf (k : ℕ) (c : Hmod K (TopCat.of U) k) :
    pull (cmap (punctHomotopyEquiv U d).toFun) k
        (pull (cmap ContinuousMap.fst : TopCat.of (U × CP d) ⟶ TopCat.of U) k c)
      = pull (cpPrSub U d (punctUSet U d)) k c := by
  rw [← pull_comp, punctHE_comp_prU]

/-! ## 2. The connecting map kills a pullback from the base -/

theorem mvResWUOf_pull_cpPrSub (m : ℕ) (c : Hmod K (TopCat.of U) m) :
    (mvResWUOf K (chartU U d) (punctU U d) (cp_sup U d) m).hom
        (pull (cpPrSub U d (chartUSet U d)) m c)
      = pull (cpPrSub U d (interUSet U d)) m c := by
  rw [mvResWUOf_eq_pull, cohPullbackK_apply_eq, ← pull_comp, subInclusion_comp_cpPrSub]

theorem mvDeltaOf_pull_cpPrSub_inter (m : ℕ) (c : Hmod K (TopCat.of U) m) :
    (mvDeltaOf K (chartU U d) (punctU U d) (cp_sup U d) m).hom
      (pull (cpPrSub U d (interUSet U d)) m c) = 0 := by
  refine (mvExactWOf K (chartU U d) (punctU U d) (cp_sup U d) m _).2 ?_
  refine ⟨pull (cpPrSub U d (chartUSet U d)) m c, 0, ?_⟩
  rw [mvResWUOf_pull_cpPrSub, map_zero, add_zero]

/-! ## 3. Restriction of a pullback from the base -/

theorem mvResUOf_pull_cpPrU (m : ℕ) (a : Hmod K (TopCat.of U) m) :
    (mvResUOf K (chartU U d) (punctU U d) (cp_sup U d) m).hom (pull (cpPrU U d) m a)
      = pull (cpPrSub U d (chartUSet U d)) m a := by
  rw [mvResUOf_eq_pull, cohPullbackK_apply_eq, ← pull_comp, sInclusion_comp_cpPrSub]

theorem mvResVOf_pull_cpPrU (m : ℕ) (a : Hmod K (TopCat.of U) m) :
    (mvResVOf K (chartU U d) (punctU U d) (cp_sup U d) m).hom (pull (cpPrU U d) m a)
      = pull (cpPrSub U d (punctUSet U d)) m a := by
  rw [mvResVOf_eq_pull, cohPullbackK_apply_eq, ← pull_comp, sInclusion_comp_cpPrSub]

theorem mvResWUOf_mvResUOf_cp (m : ℕ) (z : Hmod K (cpProdTop U d) m) :
    (mvResWUOf K (chartU U d) (punctU U d) (cp_sup U d) m).hom
        ((mvResUOf K (chartU U d) (punctU U d) (cp_sup U d) m).hom z)
      = pull (sInclusion (interUSet U d)) m z := by
  rw [mvResWUOf_eq_pull, mvResUOf_eq_pull, cohPullbackK_apply_eq, cohPullbackK_apply_eq,
    ← pull_comp, subInclusion_comp_sInclusion]

theorem mvResWVOf_mvResVOf_cp (m : ℕ) (z : Hmod K (cpProdTop U d) m) :
    (mvResWVOf K (chartU U d) (punctU U d) (cp_sup U d) m).hom
        ((mvResVOf K (chartU U d) (punctU U d) (cp_sup U d) m).hom z)
      = pull (sInclusion (interUSet U d)) m z := by
  rw [mvResWVOf_eq_pull, mvResVOf_eq_pull, cohPullbackK_apply_eq, cohPullbackK_apply_eq,
    ← pull_comp, subInclusion_comp_sInclusion]

/-- The projection of the intersection is injective in cohomology over `K`. -/
theorem pull_cpPrSub_inter_injectiveOf (m : ℕ) :
    Function.Injective (pull (K := K) (cpPrSub U d (interUSet U d)) m) := by
  intro c₁ c₂ hc
  refine pull_knPrY_injectiveOf K U (2 * d + 1) (spherePoint (2 * d + 1)) m ?_
  refine (interPullEquivOf K U d m).injective ?_
  show pull (cmap (interHomotopyEquiv U d).toFun) m _
    = pull (cmap (interHomotopyEquiv U d).toFun) m _
  rw [pull_interHE_prUOf, pull_interHE_prUOf]
  exact hc

set_option maxHeartbeats 1000000 in
/-- **The asymmetric step over `K`.**  A class vanishing on the punctured piece vanishes on the
chart piece as well. -/
theorem mvResUOf_eq_zero_of_mvResVOf_eq_zero (m : ℕ) (z : Hmod K (cpProdTop U d) m)
    (h : (mvResVOf K (chartU U d) (punctU U d) (cp_sup U d) m).hom z = 0) :
    (mvResUOf K (chartU U d) (punctU U d) (cp_sup U d) m).hom z = 0 := by
  obtain ⟨c, hc⟩ := exists_pull_cpPrSub_chartOf K U d m
    ((mvResUOf K (chartU U d) (punctU U d) (cp_sup U d) m).hom z)
  have hzero : pull (cpPrSub U d (interUSet U d)) m c = 0 := by
    rw [← mvResWUOf_pull_cpPrSub, hc, mvResWUOf_mvResUOf_cp, ← mvResWVOf_mvResVOf_cp, h,
      map_zero]
  have hc0 : c = 0 := by
    refine pull_cpPrSub_inter_injectiveOf K U d m ?_
    rw [hzero, pull_zero]
  rw [← hc, hc0, pull_zero]

/-! ## 4. The top class and the kernel of the restriction to the punctured piece -/

/-- The sphere generator of the intersection over `K`, transported. -/
def interSigmaOf : Hmod K (TopCat.of ↥(interUSet U d)) (2 * d + 1) :=
  pull (cmap (interHomotopyEquiv U d).toFun) (2 * d + 1)
    (knSigmaOf K U (2 * d + 1) (by omega))

/-- **The top power of the tautological class over `K`**, defined by the connecting map of the
chart cover. -/
def cpTopOf : Hmod K (cpProdTop U d) (2 * d + 1 + 1) :=
  (mvDeltaOf K (chartU U d) (punctU U d) (cp_sup U d) (2 * d + 1)).hom (interSigmaOf K U d)

theorem pull_sInclusion_cpPrUOf (S : Set ↥(cpProdTop U d)) (k : ℕ)
    (v : Hmod K (TopCat.of U) k) :
    pull (sInclusion S) k (pull (cpPrU U d) k v) = pull (cpPrSub U d S) k v := by
  rw [← pull_comp, sInclusion_comp_cpPrSub]

set_option maxHeartbeats 1000000 in
/-- **A class restricting to zero on the punctured piece is a multiple of `cpTopOf`**, over
`K`. -/
theorem exists_of_mvResVOf_eq_zero (m : ℕ)
    (z : Hmod K (cpProdTop U d) (2 * d + 1 + m + 1))
    (h : (mvResVOf K (chartU U d) (punctU U d) (cp_sup U d)
      (2 * d + 1 + m + 1)).hom z = 0) :
    ∃ b : Hmod K (TopCat.of U) m,
      z = cohCast (aw_degree_left_succ (2 * d + 1) m)
            (cup (cpTopOf K U d) (pull (cpPrU U d) m b)) := by
  have hU := mvResUOf_eq_zero_of_mvResVOf_eq_zero K U d (2 * d + 1 + m + 1) z h
  obtain ⟨w, hw⟩ := (mvExactXOf K (chartU U d) (punctU U d) (cp_sup U d)
    (2 * d + 1 + m) z).1 ⟨hU, h⟩
  obtain ⟨w', hw'⟩ :
      ∃ w', pull (cmap (interHomotopyEquiv U d).toFun) (2 * d + 1 + m) w' = w :=
    ⟨(interPullEquivOf K U d (2 * d + 1 + m)).symm w,
      (interPullEquivOf K U d (2 * d + 1 + m)).apply_symm_apply w⟩
  obtain ⟨c, b, hcb⟩ := KnHemi.kunneth_decompositionOf K U (2 * d + 1) (by omega)
    (2 * d + 1 + m) m rfl w'
  refine ⟨b, ?_⟩
  have hsplit : w = pull (cpPrSub U d (interUSet U d)) (2 * d + 1 + m) c
      + pull (cmap (interHomotopyEquiv U d).toFun) (2 * d + 1 + m)
          (cup (knSigmaOf K U (2 * d + 1) (by omega))
            (pull (knPrY U (2 * d + 1)) m b)) := by
    rw [← hw', hcb, pull_add, pull_interHE_prUOf, cohCast_self]
  rw [← hw, hsplit, map_add, mvDeltaOf_pull_cpPrSub_inter, zero_add, pull_cup,
    pull_interHE_prUOf, ← pull_sInclusion_cpPrUOf, MVDelta.mvDeltaOf_cup]
  rfl

/-! ## 5. Surjectivity of the restriction below the sphere dimension -/

/-- **Below the sphere dimension the intersection is all pullbacks**, over `K`. -/
theorem exists_flat_of_ltOf (k : ℕ) (hk : k < 2 * d + 1)
    (x : Hmod K (TopCat.of ↥(interUSet U d)) k) :
    ∃ e : Hmod K (TopCat.of U) k, x = pull (cpPrSub U d (interUSet U d)) k e := by
  obtain ⟨x', hx'⟩ :
      ∃ x', pull (cmap (interHomotopyEquiv U d).toFun) k x' = x :=
    ⟨(interPullEquivOf K U d k).symm x, (interPullEquivOf K U d k).apply_symm_apply x⟩
  obtain ⟨e, he⟩ := KnHemi.kunneth_lowOf K U (2 * d + 1) k hk x'
  refine ⟨e, ?_⟩
  rw [← hx', he, pull_interHE_prUOf]

set_option maxHeartbeats 1000000 in
/-- **A class on the punctured piece extends when its restriction to the intersection is a
pullback from the base**, over `K`. -/
theorem mvResVOf_surjective_of_flat (k : ℕ)
    (w : Hmod K (TopCat.of ↥(punctUSet U d)) k) (e : Hmod K (TopCat.of U) k)
    (he : (mvResWVOf K (chartU U d) (punctU U d) (cp_sup U d) k).hom w
      = pull (cpPrSub U d (interUSet U d)) k e) :
    ∃ z : Hmod K (cpProdTop U d) k,
      (mvResVOf K (chartU U d) (punctU U d) (cp_sup U d) k).hom z = w := by
  obtain ⟨z, _, hz⟩ := (mvExactSumOf K (chartU U d) (punctU U d) (cp_sup U d) k
    (pull (cpPrSub U d (chartUSet U d)) k e) w).1
    (by rw [mvResWUOf_pull_cpPrSub, he])
  exact ⟨z, hz⟩

set_option maxHeartbeats 1000000 in
/-- **Surjectivity of the restriction below the sphere dimension**, over `K`. -/
theorem mvResVOf_surjective_of_lt (k : ℕ) (hk : k < 2 * d + 1)
    (w : Hmod K (TopCat.of ↥(punctUSet U d)) k) :
    ∃ z : Hmod K (cpProdTop U d) k,
      (mvResVOf K (chartU U d) (punctU U d) (cp_sup U d) k).hom z = w := by
  obtain ⟨e, he⟩ := exists_flat_of_ltOf K U d k hk
    ((mvResWVOf K (chartU U d) (punctU U d) (cp_sup U d) k).hom w)
  exact mvResVOf_surjective_of_flat K U d k w e he

end KnCP

end

end GroupApproximation.CharClass
