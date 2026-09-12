import GroupApproximation.CharClass.CohomologyChartTautClassOf
import GroupApproximation.CharClass.CohomologyChartInduction
import GroupApproximation.CharClass.ProjectiveSpaceComputationOf
import GroupApproximation.CharClass.CoeffLine
import GroupApproximation.CharClass.CupOneComm

/-!
# Rank-two Leray–Hirsch for `U × ℂP^1`, over a field

The coefficient-generic form of `CohomologyChartRankTwoInterface`: the three hypotheses of
`LH.bijective_lhSum_two` for the projection `U × ℂP^1 → U`, with the degree-two class the
pullback of an **arbitrary nonzero** `h ∈ H^2(ℂP^1; K)`.

Over `F₂` the connecting-map class `cpTop U 0` *is* the pulled-back generator.  Over `K` it is a
scalar multiple of the pullback of `h`, because `H^2(ℂP^1; K)` is a line
(`ProjectiveSpaceComputationOf.hasCPCohomologyOf_CP`); the scalar is never inverted, so no
nonvanishing of it is needed.  The two places the `F₂` proof added a class to itself to cancel it
subtract it instead.

## Main declarations

* `KnCP.cpTopPtOf_zero_eq_smul`, `KnCP.cpTopOf_zero_eq_smul` — `cpTopOf` against `h`.
* `KnCP.lhLowOf`, `KnCP.lhSurjOf`, `KnCP.lhUniqOf` — **the three hypotheses, over `K`**.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.STW59
open GroupApproximation.CharClass.CPn

namespace GroupApproximation.CharClass

noncomputable section

namespace KnCP

variable (K : Type) [Field K] (U : Type) [TopologicalSpace U]

/-! ## 1. The connecting class against an arbitrary nonzero class -/

/-- `H^2(ℂP^1; K)` is a line, so the connecting class is a multiple of any nonzero class. -/
theorem cpTopPtOf_zero_eq_smul (h : Hmod K (CPtop 1) 2) (h0 : h ≠ 0) :
    ∃ c : K, cpTopPtOf K 0 = c • h := by
  obtain ⟨e⟩ := (hasCPCohomologyOf_CP K 1).1 1 le_rfl
  exact exists_smul_of_line e h0 (cpTopPtOf K 0)

/-- **`cpTopOf` at rank two is a multiple of the pulled-back class.** -/
theorem cpTopOf_zero_eq_smul (h : Hmod K (CPtop 1) 2) (h0 : h ≠ 0) :
    ∃ c : K, cpTopOf K U 0 = c • pull (cpPrCP U 0) 2 h := by
  obtain ⟨c, hc⟩ := cpTopPtOf_zero_eq_smul K h h0
  refine ⟨c, ?_⟩
  have h1 := cpTopOf_eq_pull_cpTopPtOf K U 0
  rw [hc, pull_smul] at h1
  exact h1

/-! ## 2. The projection is bijective below degree two -/

theorem pull_cpPrU_injectiveOf (k : ℕ) : Function.Injective (pull (K := K) (cpPrU U 0) k) := by
  obtain ⟨p⟩ := nonempty_CPtop 1
  intro c₁ c₂ hc
  have h := congrArg (pull (cpSlice U p) k) hc
  rwa [← pull_comp, ← pull_comp, cpSlice_comp_cpPrU, pull_id, pull_id] at h

theorem cohProdContractibleOf_apply_eq (k : ℕ) (c : Hmod K (TopCat.of U) k) :
    cohProdContractibleOf K U (CP 0) k c = pull (fstMap U (CP 0)) k c := by
  show pull (cmap (prodContractibleEquiv U (CP 0)).toFun) k c = _
  rw [prodContractibleEquiv_toFun]

theorem pull_cpPrSub_punct_zero_injectiveOf (k : ℕ) :
    Function.Injective (pull (K := K) (cpPrSub U 0 (punctUSet U 0)) k) := by
  intro c₁ c₂ hc
  refine (cohProdContractibleOf K U (CP 0) k).injective ?_
  refine (punctPullEquivOf K U 0 k).injective ?_
  show pull (cmap (punctHomotopyEquiv U 0).toFun) k ((cohProdContractibleOf K U (CP 0) k) c₁)
    = pull (cmap (punctHomotopyEquiv U 0).toFun) k ((cohProdContractibleOf K U (CP 0) k) c₂)
  rw [cohProdContractibleOf_apply_eq, cohProdContractibleOf_apply_eq, pull_punctHE_prUOf,
    pull_punctHE_prUOf]
  exact hc

set_option maxHeartbeats 1000000 in
theorem exists_pull_cpPrU_of_ltOf (k : ℕ) (hk : k < 2) (z : Hmod K (cpProdTop U 0) k) :
    ∃ a : Hmod K (TopCat.of U) k, z = pull (cpPrU U 0) k a := by
  obtain ⟨a, ha⟩ := exists_pull_cpPrSub_punct_zeroOf K U k
    ((mvResVOf K (chartU U 0) (punctU U 0) (cp_sup U 0) k).hom z)
  have hV : (mvResVOf K (chartU U 0) (punctU U 0) (cp_sup U 0) k).hom
      (z - pull (cpPrU U 0) k a) = 0 := by
    rw [map_sub, mvResVOf_pull_cpPrU, ha, sub_self]
  have hU : (mvResUOf K (chartU U 0) (punctU U 0) (cp_sup U 0) k).hom
      (z - pull (cpPrU U 0) k a) = 0 :=
    mvResUOf_eq_zero_of_mvResVOf_eq_zero K U 0 k _ hV
  have hzero : z - pull (cpPrU U 0) k a = 0 := by
    match k with
    | 0 => exact mvExactZeroOf K (chartU U 0) (punctU U 0) (cp_sup U 0) hU hV
    | 1 =>
      obtain ⟨w, hw⟩ :=
        (mvExactXOf K (chartU U 0) (punctU U 0) (cp_sup U 0) 0 _).1 ⟨hU, hV⟩
      obtain ⟨w', hw'⟩ :
          ∃ w', pull (cmap (interHomotopyEquiv U 0).toFun) 0 w' = w :=
        ⟨(interPullEquivOf K U 0 0).symm w, (interPullEquivOf K U 0 0).apply_symm_apply w⟩
      obtain ⟨c, hcw⟩ := KnHemi.kunneth_lowOf K U (2 * 0 + 1) 0 (by omega) w'
      rw [← hw, ← hw', hcw, pull_interHE_prUOf, mvDeltaOf_pull_cpPrSub_inter]
    | (n + 2) => exact absurd hk (by omega)
  exact ⟨a, sub_eq_zero.mp hzero⟩

theorem lhLowOf (n : ℕ) (hn : n < 2) : Function.Bijective (pull (K := K) (cpPrU U 0) n) :=
  ⟨pull_cpPrU_injectiveOf K U n, fun z => by
    obtain ⟨a, ha⟩ := exists_pull_cpPrU_of_ltOf K U n hn z
    exact ⟨a, ha.symm⟩⟩

/-! ## 3. The decomposition and its uniqueness -/

theorem exists_of_mvResVOf_eq_zero' (d k m : ℕ) (hk : 2 * d + 1 + m + 1 = k)
    (hc : 2 * d + 1 + 1 + m = k) (z : Hmod K (cpProdTop U d) k)
    (h : (mvResVOf K (chartU U d) (punctU U d) (cp_sup U d) k).hom z = 0) :
    ∃ b : Hmod K (TopCat.of U) m,
      z = cohCast hc (cup (cpTopOf K U d) (pull (cpPrU U d) m b)) := by
  subst hk
  exact exists_of_mvResVOf_eq_zero K U d m z h

set_option maxHeartbeats 1000000 in
/-- **Existence of the rank-two decomposition over `K`**, against any nonzero `h`. -/
theorem lhSurjOf (h : Hmod K (CPtop 1) 2) (h0 : h ≠ 0) (n : ℕ)
    (z : Hmod K (cpProdTop U 0) (n + 2)) :
    ∃ (a : Hmod K (TopCat.of U) (n + 2)) (b : Hmod K (TopCat.of U) n),
      z = pull (cpPrU U 0) (n + 2) a + cup (pull (cpPrU U 0) n b) (pull (cpPrCP U 0) 2 h) := by
  obtain ⟨c, hc⟩ := cpTopOf_zero_eq_smul K U h h0
  obtain ⟨a, ha⟩ := exists_pull_cpPrSub_punct_zeroOf K U (n + 2)
    ((mvResVOf K (chartU U 0) (punctU U 0) (cp_sup U 0) (n + 2)).hom z)
  have hV : (mvResVOf K (chartU U 0) (punctU U 0) (cp_sup U 0) (n + 2)).hom
      (z - pull (cpPrU U 0) (n + 2) a) = 0 := by
    rw [map_sub, mvResVOf_pull_cpPrU, ha, sub_self]
  obtain ⟨b, hb⟩ := exists_of_mvResVOf_eq_zero' K U 0 (n + 2) n (by omega)
    (Nat.add_comm 2 n) _ hV
  refine ⟨a, c • b, ?_⟩
  have key : cup (pull (cpPrU U 0) n (c • b)) (pull (cpPrCP U 0) 2 h)
      = cohCast (Nat.add_comm 2 n) (cup (cpTopOf K U 0) (pull (cpPrU U 0) n b)) := by
    rw [hc, cup_smul_left, cohCast_smul, pull_smul, cup_smul_left,
      cup_comm_of_even_right even_two (pull (cpPrU U 0) n b) (pull (cpPrCP U 0) 2 h)]
  rw [key, ← hb, add_sub_cancel]

/-- A class pulled back from `ℂP^1` dies on the punctured piece, which is `U × ℂP^0`. -/
theorem pull_sInclusion_punct_cpPrCP_zeroOf (c : Hmod K (CPtop 1) 2) :
    pull (sInclusion (punctUSet U 0)) 2 (pull (cpPrCP U 0) 2 c) = 0 := by
  have hz : pull (punctIncl 0) 2 c = 0 :=
    (hasCPCohomologyOf_punctSpace K 0 (hasCPCohomologyOf_zero K)).2 2
      (fun n hn => by omega) _
  rw [← pull_comp, ← punctToPunctSpace_comp_punctIncl, pull_comp, hz, pull_zero]

set_option maxHeartbeats 1000000 in
/-- **Uniqueness of the rank-two decomposition over `K`**, against any nonzero `h`. -/
theorem lhUniqOf (h : Hmod K (CPtop 1) 2) (h0 : h ≠ 0) (n : ℕ)
    (a : Hmod K (TopCat.of U) (n + 2)) (b : Hmod K (TopCat.of U) n)
    (hsum : pull (cpPrU U 0) (n + 2) a
      + cup (pull (cpPrU U 0) n b) (pull (cpPrCP U 0) 2 h) = 0) : a = 0 ∧ b = 0 := by
  have hcup : (mvResVOf K (chartU U 0) (punctU U 0) (cp_sup U 0) (n + 2)).hom
      (cup (pull (cpPrU U 0) n b) (pull (cpPrCP U 0) 2 h)) = 0 := by
    rw [mvResVOf_eq_pull, cohPullbackK_apply_eq, pull_cup,
      pull_sInclusion_punct_cpPrCP_zeroOf K U h, cup_zero]
  have ha : a = 0 := by
    refine pull_cpPrSub_punct_zero_injectiveOf K U (n + 2) ?_
    rw [pull_zero, ← mvResVOf_pull_cpPrU]
    have := congrArg (mvResVOf K (chartU U 0) (punctU U 0) (cp_sup U 0) (n + 2)).hom hsum
    rwa [map_add, hcup, add_zero, map_zero] at this
  refine ⟨ha, ?_⟩
  rw [ha, pull_zero, zero_add, cup_comm_of_even_right even_two, cohCast_eq_zero_iff] at hsum
  obtain ⟨c, hc⟩ := cpTopOf_zero_eq_smul K U h h0
  refine cpTop_cup_injective_zeroOf K U n b ?_
  have h2 : cup (c • pull (cpPrCP U 0) 2 h) (pull (cpPrU U 0) n b) = 0 := by
    rw [cup_smul_left, hsum, smul_zero]
  rw [hc]
  exact h2

end KnCP

end

end GroupApproximation.CharClass
