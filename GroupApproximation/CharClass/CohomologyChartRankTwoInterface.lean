import GroupApproximation.CharClass.CohomologyChartTautClass
import GroupApproximation.CharClass.SteenrodCupOne

/-!
# Rank-two Leray–Hirsch, in `cc-projective`'s interface shape

`LH.bijective_lhSum_two` takes three hypotheses about a projection and a
degree-two class: bijectivity below degree two, existence of the decomposition,
and uniqueness of its two coefficients.  This file supplies all three for the
projection of `U × ℂP^1` onto an arbitrary `U`, with the class being the
tautological generator pulled back.

The class is the tautological one and not a comparable substitute:
`cpTop_zero_eq_pull_cpGen` says the connecting-map class **is** the pullback of
`cpGen`, so no change of basis intervenes.

## Main results

* `KnCP.lhLow`, `KnCP.lhSurj`, `KnCP.lhUniq` — the three hypotheses.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.STW59
open GroupApproximation.CharClass.CPn

namespace GroupApproximation.CharClass

noncomputable section

namespace KnCP

variable (U : Type) [TopologicalSpace U]

/-- The tautological degree-two class of `U × ℂP^1`. -/
def cpTaut : Hmod2 (cpProdTop U 0) 2 := pull (cpPrCP U 0) 2 (cpGen 1 (by omega))

theorem cpTop_zero_eq_cpTaut : cpTop U 0 = cpTaut U :=
  cpTop_zero_eq_pull_cpGen U

/-! ## 1. The projection is bijective below degree two -/

theorem pull_cpPrSub_punct_zero_injective (k : ℕ) :
    Function.Injective (pull (cpPrSub U 0 (punctUSet U 0)) k) := by
  intro c₁ c₂ hc
  refine (cohProdContractible U (CP 0) k).injective ?_
  refine (punctPullEquiv U 0 k).injective ?_
  show pull (cmap (punctHomotopyEquiv U 0).toFun) k
      ((cohProdContractible U (CP 0) k) c₁)
    = pull (cmap (punctHomotopyEquiv U 0).toFun) k
      ((cohProdContractible U (CP 0) k) c₂)
  rw [cohProdContractible_apply, cohProdContractible_apply, pull_punctHE_prU,
    pull_punctHE_prU]
  exact hc

/-- A slice of the projection, so the pullback is split injective. -/
def cpSlice (p : CP 1) : TopCat.of U ⟶ cpProdTop U 0 :=
  cmap (ContinuousMap.prodMk (ContinuousMap.id U) (ContinuousMap.const U p))

theorem cpSlice_comp_cpPrU (p : CP 1) :
    cpSlice U p ≫ cpPrU U 0 = 𝟙 (TopCat.of U) := rfl

theorem pull_cpPrU_injective (k : ℕ) : Function.Injective (pull (cpPrU U 0) k) := by
  obtain ⟨p⟩ := nonempty_CPtop 1
  intro c₁ c₂ hc
  have h := congrArg (pull (cpSlice U p) k) hc
  rwa [← pull_comp, ← pull_comp, cpSlice_comp_cpPrU, pull_id, pull_id] at h

set_option maxHeartbeats 1000000 in
theorem exists_pull_cpPrU_of_lt (k : ℕ) (hk : k < 2)
    (z : Hmod2 (cpProdTop U 0) k) :
    ∃ a : Hmod2 (TopCat.of U) k, z = pull (cpPrU U 0) k a := by
  obtain ⟨a, ha⟩ := exists_pull_cpPrSub_punct_zero U k
    ((mvResV (chartU U 0) (punctU U 0) (cp_sup U 0) k).hom z)
  have hV : (mvResV (chartU U 0) (punctU U 0) (cp_sup U 0) k).hom
      (z + pull (cpPrU U 0) k a) = 0 := by
    rw [map_add, mvResV_pull_cpPrU, ha, add_self_eq_zero_two]
  have hU : (mvResU (chartU U 0) (punctU U 0) (cp_sup U 0) k).hom
      (z + pull (cpPrU U 0) k a) = 0 :=
    mvResU_eq_zero_of_mvResV_eq_zero U 0 k _ hV
  have hzero : z + pull (cpPrU U 0) k a = 0 := by
    match k with
    | 0 => exact mvExactZero (chartU U 0) (punctU U 0) (cp_sup U 0) hU hV
    | 1 =>
      obtain ⟨w, hw⟩ := (mvExactX (chartU U 0) (punctU U 0) (cp_sup U 0) 0 _).1 ⟨hU, hV⟩
      obtain ⟨w', hw'⟩ :
          ∃ w', pull (cmap (interHomotopyEquiv U 0).toFun) 0 w' = w :=
        ⟨(interPullEquiv U 0 0).symm w, (interPullEquiv U 0 0).apply_symm_apply w⟩
      obtain ⟨c, hcw⟩ := KnHemi.kunneth_low U (2 * 0 + 1) 0 (by omega) w'
      rw [← hw, ← hw', hcw, pull_interHE_prU, mvDelta_pull_cpPrSub_inter]
    | (n + 2) => exact absurd hk (by omega)
  refine ⟨a, ?_⟩
  have := congrArg (fun y => y + pull (cpPrU U 0) k a) hzero
  simpa only [add_assoc, add_self_eq_zero_two, add_zero, zero_add] using this

theorem lhLow (n : ℕ) (hn : n < 2) : Function.Bijective (pull (cpPrU U 0) n) :=
  ⟨pull_cpPrU_injective U n, fun z => by
    obtain ⟨a, ha⟩ := exists_pull_cpPrU_of_lt U n hn z
    exact ⟨a, ha.symm⟩⟩

/-! ## 2. The decomposition and its uniqueness -/

theorem exists_of_mvResV_eq_zero' (d k m : ℕ) (hk : 2 * d + 1 + m + 1 = k)
    (hc : 2 * d + 1 + 1 + m = k) (z : Hmod2 (cpProdTop U d) k)
    (h : (mvResV (chartU U d) (punctU U d) (cp_sup U d) k).hom z = 0) :
    ∃ b : Hmod2 (TopCat.of U) m,
      z = cohCast hc (cup (cpTop U d) (pull (cpPrU U d) m b)) := by
  subst hk
  exact exists_of_mvResV_eq_zero U d m z h

theorem cup_cpTaut (n : ℕ) (b : Hmod2 (TopCat.of U) n) :
    cup (pull (cpPrU U 0) n b) (cpTaut U)
      = cohCast (Nat.add_comm 2 n) (cup (cpTop U 0) (pull (cpPrU U 0) n b)) := by
  rw [cpTop_zero_eq_cpTaut, cup_comm]

set_option maxHeartbeats 1000000 in
theorem lhSurj (n : ℕ) (z : Hmod2 (cpProdTop U 0) (n + 2)) :
    ∃ (a : Hmod2 (TopCat.of U) (n + 2)) (b : Hmod2 (TopCat.of U) n),
      z = pull (cpPrU U 0) (n + 2) a + cup (pull (cpPrU U 0) n b) (cpTaut U) := by
  obtain ⟨a, ha⟩ := exists_pull_cpPrSub_punct_zero U (n + 2)
    ((mvResV (chartU U 0) (punctU U 0) (cp_sup U 0) (n + 2)).hom z)
  have hV : (mvResV (chartU U 0) (punctU U 0) (cp_sup U 0) (n + 2)).hom
      (z + pull (cpPrU U 0) (n + 2) a) = 0 := by
    rw [map_add, mvResV_pull_cpPrU, ha, add_self_eq_zero_two]
  obtain ⟨b, hb⟩ := exists_of_mvResV_eq_zero' U 0 (n + 2) n (by omega)
    (Nat.add_comm 2 n) _ hV
  refine ⟨a, b, ?_⟩
  rw [cup_cpTaut, ← hb, add_comm z, ← add_assoc, add_self_eq_zero_two, zero_add]

set_option maxHeartbeats 1000000 in
theorem mvResV_cpTop_zero :
    (mvResV (chartU U 0) (punctU U 0) (cp_sup U 0) (2 * 0 + 1 + 1)).hom
      (cpTop U 0) = 0 :=
  ((mvExactX (chartU U 0) (punctU U 0) (cp_sup U 0) (2 * 0 + 1)
    (cpTop U 0)).2 ⟨interSigma U 0, rfl⟩).2

theorem pull_sInclusion_punct_cpTop_zero :
    pull (sInclusion (punctUSet U 0)) 2 (cpTop U 0) = 0 := by
  have h := mvResV_cpTop_zero U
  rw [mvResV_eq_pull, cohPullback_apply_eq] at h
  exact h

set_option maxHeartbeats 1000000 in
theorem lhUniq (n : ℕ) (a : Hmod2 (TopCat.of U) (n + 2))
    (b : Hmod2 (TopCat.of U) n)
    (h : pull (cpPrU U 0) (n + 2) a
      + cup (pull (cpPrU U 0) n b) (cpTaut U) = 0) : a = 0 ∧ b = 0 := by
  have hcup : (mvResV (chartU U 0) (punctU U 0) (cp_sup U 0) (n + 2)).hom
      (cup (pull (cpPrU U 0) n b) (cpTaut U)) = 0 := by
    rw [mvResV_eq_pull, cohPullback_apply_eq, pull_cup, cpTaut,
      ← cpTop_zero_eq_pull_cpGen, pull_sInclusion_punct_cpTop_zero, cup_zero]
  have ha : a = 0 := by
    refine pull_cpPrSub_punct_zero_injective U (n + 2) ?_
    rw [pull_zero, ← mvResV_pull_cpPrU]
    have := congrArg (mvResV (chartU U 0) (punctU U 0) (cp_sup U 0) (n + 2)).hom h
    rwa [map_add, hcup, add_zero, map_zero] at this
  refine ⟨ha, ?_⟩
  rw [ha, pull_zero, zero_add, cup_cpTaut, cohCast_eq_zero_iff] at h
  exact cpTop_cup_injective_zero U n b h

end KnCP

end

end GroupApproximation.CharClass
