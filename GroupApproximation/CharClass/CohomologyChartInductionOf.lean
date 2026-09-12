import GroupApproximation.CharClass.CohomologyChartSplitOf
import GroupApproximation.CharClass.ProjectiveSpaceStableOf
import GroupApproximation.CharClass.CohomologyLHDegreewiseOf

/-!
# The projective-factor Künneth at every rank, by induction on the fibre, over a field

The coefficient-generic form of `CohomologyChartInduction`.  The base `CPSplitOf K 1` is the
rank-two decomposition `lhSurjOf`, unconditionally; the step `CPSplitOf K d → CPSplitOf K (d+1)` is
Mayer–Vietoris for the chart cover of `U × ℂP^{d+1}`, over generation on `ℂP^{d+1}`.

Two changes from `F₂`, both forced by the absence of a canonical generator.  The class at the
smaller rank is the pullback `pull (cpIncl d) 2 h` of the class at the larger one, which is nonzero
because the hyperplane inclusion is bijective on `H^2(-; K)` (`bijective_pull_cpInclOf`), and it
restricts to itself across the retraction of the punctured piece with no generator computation
(`pull_punctIncl_hOf`).  And every step the `F₂` proof closed by adding a class to itself
subtracts it.

## Main declarations

* `KnCP.pull_punctIncl_hOf`, `KnCP.pull_sInclusion_cpPrCP_hOf`, `KnCP.pull_cpIncl_ne_zeroOf`.
* `KnCP.mvResVOf_surjective_of_cpSplit_allOf`, `KnCP.eq_zero_of_mvResVOf_eq_zero_of_lt`.
* `KnCP.exists_cup_gen_cpTopOf`.
* `KnCP.cpSplitOf_one`, `KnCP.cpSplitOf_succ`, `KnCP.cpSplitOf_of_cpGenHypOf` — **the induction**.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.STW59
open GroupApproximation.CharClass.CPn

namespace GroupApproximation.CharClass

noncomputable section

namespace KnCP

variable (K : Type) [Field K] (U : Type) [TopologicalSpace U] (d : ℕ)

/-! ## 1. The class of the fibre restricts to its pullback along the hyperplane -/

/-- Pullback along `ℂP^d ⊆ ℂP^{d+1} ∖ {pt}` undoes pullback along the retraction, over `K`. -/
theorem pull_cpInclP_pull_punctOpenHEOf (n : ℕ) (c : Hmod K (CPtop d) n) :
    pull (cpInclP d) n (pull (cmap (punctOpenHomotopyEquiv d).toFun) n c) = c :=
  (pullEquivOfHomotopyEquivOf K (punctOpenHomotopyEquiv d) n).symm_apply_apply c

/-- **A class on `ℂP^{d+1}` restricts to the punctured space as its pullback to `ℂP^d`**, moved
across the retraction. -/
theorem pull_punctIncl_hOf (h : Hmod K (CPtop (d + 1)) 2) :
    pull (punctIncl d) 2 h
      = pull (cmap (punctOpenHomotopyEquiv d).toFun) 2 (pull (cpIncl d) 2 h) := by
  refine (bijective_pull_cpInclPOf K d 2).1 ?_
  rw [pull_cpInclP_pull_punctOpenHEOf]
  exact (pull_comp (cpInclP d) (punctIncl d) 2 h).symm

/-- **The class, restricted to the punctured piece of the product**, is the pulled-back class of
the smaller product. -/
theorem pull_sInclusion_cpPrCP_hOf (h : Hmod K (CPtop (d + 1)) 2) :
    pull (sInclusion (punctUSet U d)) 2 (pull (cpPrCP U d) 2 h)
      = pull (cmap (punctHomotopyEquiv U d).toFun) 2
          (pull (cpSnd U d) 2 (pull (cpIncl d) 2 h)) := by
  have h1 : pull (sInclusion (punctUSet U d)) 2 (pull (cpPrCP U d) 2 h)
      = pull (punctToPunctSpace U d) 2 (pull (punctIncl d) 2 h) := by
    rw [← pull_comp, ← pull_comp, punctToPunctSpace_comp_punctIncl]
  have h2 : ∀ c : Hmod K (CPtop d) 2,
      pull (punctToPunctSpace U d) 2 (pull (cmap (punctOpenHomotopyEquiv d).toFun) 2 c)
        = pull (cmap (punctHomotopyEquiv U d).toFun) 2 (pull (cpSnd U d) 2 c) := by
    intro c
    rw [← pull_comp, ← pull_comp, punctToPunctSpace_comp_HE]
  rw [h1, pull_punctIncl_hOf K d h, h2]

/-- The pullback of a nonzero class along the hyperplane inclusion is nonzero, for `d ≥ 1`. -/
theorem pull_cpIncl_ne_zeroOf (hd : 1 ≤ d) (h : Hmod K (CPtop (d + 1)) 2) (h0 : h ≠ 0) :
    pull (cpIncl d) 2 h ≠ 0 := fun h1 =>
  h0 ((bijective_pull_cpInclOf K d hd).1 (h1.trans (pull_zero _ 2).symm))

/-! ## 2. Restriction to the punctured piece -/

set_option maxHeartbeats 1000000 in
/-- **Surjectivity of the restriction in every degree**, over the product form, over `K`. -/
theorem mvResVOf_surjective_of_cpSplit_allOf (hd : 1 ≤ d) (h : Hmod K (CPtop d) 2)
    (h0 : h ≠ 0) (hsplit : CPSplitOf K d) (k : ℕ)
    (w : Hmod K (TopCat.of ↥(punctUSet U d)) k) :
    ∃ z : Hmod K (cpProdTop U d) k,
      (mvResVOf K (chartU U d) (punctU U d) (cp_sup U d) k).hom z = w := by
  rcases Nat.lt_or_ge k (2 * d + 1) with hk | hk
  · exact mvResVOf_surjective_of_lt K U d k hk w
  · obtain ⟨j, rfl⟩ : ∃ j, k = 2 + j := ⟨k - 2, by omega⟩
    exact mvResVOf_surjective_of_cpSplitOf K U d h h0 hsplit j w

set_option maxHeartbeats 1000000 in
/-- **Injectivity of the restriction below `2d+2`**, over `K`. -/
theorem eq_zero_of_mvResVOf_eq_zero_of_lt (k : ℕ) (hk : k < 2 * d + 2)
    (z : Hmod K (cpProdTop U d) k)
    (h : (mvResVOf K (chartU U d) (punctU U d) (cp_sup U d) k).hom z = 0) : z = 0 := by
  have hU := mvResUOf_eq_zero_of_mvResVOf_eq_zero K U d k z h
  match k with
  | 0 => exact mvExactZeroOf K (chartU U d) (punctU U d) (cp_sup U d) hU h
  | (j + 1) =>
    obtain ⟨w, hw⟩ := (mvExactXOf K (chartU U d) (punctU U d) (cp_sup U d) j z).1 ⟨hU, h⟩
    obtain ⟨w', hw'⟩ :
        ∃ w', pull (cmap (interHomotopyEquiv U d).toFun) j w' = w :=
      ⟨(interPullEquivOf K U d j).symm w, (interPullEquivOf K U d j).apply_symm_apply w⟩
    obtain ⟨c, hcw⟩ := KnHemi.kunneth_lowOf K U (2 * d + 1) j (by omega) w'
    rw [← hw, ← hw', hcw, pull_interHE_prUOf, mvDeltaOf_pull_cpPrSub_inter]

/-! ## 3. The top class is the class cupped with something -/

set_option maxHeartbeats 1000000 in
/-- **`cpTopOf` is a multiple of the pulled-back class**, given generation on the fibre. -/
theorem exists_cup_gen_cpTopOf (hgen : CPGenHypOf K (d + 1)) (h : Hmod K (CPtop (d + 1)) 2)
    (h0 : h ≠ 0) :
    ∃ γ : Hmod K (cpProdTop U d) (2 * d),
      cpTopOf K U d = cohCast (show 2 + 2 * d = 2 * d + 1 + 1 by omega)
        (cup (pull (cpPrCP U d) 2 h) γ) := by
  obtain ⟨c', hc'⟩ := hgen h h0 (2 * d)
    (cohCast (show 2 * d + 1 + 1 = 2 + 2 * d by omega) (cpTopPtOf K d))
  refine ⟨pull (cpPrCP U d) (2 * d) c', ?_⟩
  have hpt : cpTopPtOf K d = cohCast (show 2 + 2 * d = 2 * d + 1 + 1 by omega)
      (cup h c') := by
    rw [← hc', cohCast_cohCast, cohCast_self]
  rw [cpTopOf_eq_pull_cpTopPtOf, hpt, KnHemi.pull_cohCastOf, pull_cup]

/-! ## 4. The base of the induction -/

set_option maxHeartbeats 1000000 in
/-- **The product form at rank two over `K`**, unconditionally. -/
theorem cpSplitOf_one : CPSplitOf K 1 := by
  intro V _inst h h0 m z
  show ∃ (a : Hmod K (TopCat.of V) (2 + m)) (y : Hmod K (cpProdTop V 0) m),
      z = pull (cpPrU V 0) (2 + m) a + cup (pull (cpPrCP V 0) 2 h) y
  obtain ⟨a, b, hab⟩ := lhSurjOf K V h h0 m (cohCast (Nat.add_comm 2 m) z)
  refine ⟨cohCast (Nat.add_comm m 2) a, pull (cpPrU V 0) m b, ?_⟩
  have hz' := congrArg (cohCast (Nat.add_comm m 2)) hab
  rw [cohCast_cohCast, cohCast_self, cohCast_add, ← KnHemi.pull_cohCastOf] at hz'
  rw [hz', cup_comm_of_even_right even_two (pull (cpPrU V 0) m b) (pull (cpPrCP V 0) 2 h),
    cohCast_cohCast, cohCast_self]

/-! ## 5. The inductive step -/

set_option maxHeartbeats 1000000 in
/-- **The inductive step over `K`.** -/
theorem cpSplitOf_succ (hd : 1 ≤ d) (hgen : CPGenHypOf K (d + 1)) (hsplit : CPSplitOf K d) :
    CPSplitOf K (d + 1) := by
  intro V _inst h h0 m z
  show ∃ (a : Hmod K (TopCat.of V) (2 + m)) (y : Hmod K (cpProdTop V d) m),
      z = pull (cpPrU V d) (2 + m) a + cup (pull (cpPrCP V d) 2 h) y
  obtain ⟨w', hw'⟩ : ∃ w', pull (cmap (punctHomotopyEquiv V d).toFun) (2 + m) w'
      = (mvResVOf K (chartU V d) (punctU V d) (cp_sup V d) (2 + m)).hom z :=
    ⟨(punctPullEquivOf K V d (2 + m)).symm _, (punctPullEquivOf K V d (2 + m)).apply_symm_apply _⟩
  obtain ⟨a, y₀, hay⟩ := hsplit V (pull (cpIncl d) 2 h) (pull_cpIncl_ne_zeroOf K d hd h h0) m w'
  obtain ⟨Y, hY⟩ := mvResVOf_surjective_of_cpSplit_allOf K V d hd (pull (cpIncl d) 2 h)
    (pull_cpIncl_ne_zeroOf K d hd h h0) hsplit m
    (pull (cmap (punctHomotopyEquiv V d).toFun) m y₀)
  have hYp : pull (sInclusion (punctUSet V d)) m Y
      = pull (cmap (punctHomotopyEquiv V d).toFun) m y₀ := by
    have h' := hY
    rw [mvResVOf_eq_pull, cohPullbackK_apply_eq] at h'
    exact h'
  have hres : (mvResVOf K (chartU V d) (punctU V d) (cp_sup V d) (2 + m)).hom
      (pull (cpPrU V d) (2 + m) a + cup (pull (cpPrCP V d) 2 h) Y)
      = (mvResVOf K (chartU V d) (punctU V d) (cp_sup V d) (2 + m)).hom z := by
    rw [map_add, mvResVOf_pull_cpPrU, ← hw', hay, pull_add, pull_punctHE_prUOf]
    congr 1
    rw [mvResVOf_eq_pull, cohPullbackK_apply_eq, pull_cup,
      pull_sInclusion_cpPrCP_hOf K V d h, hYp, ← pull_cup]
  have hzero : (mvResVOf K (chartU V d) (punctU V d) (cp_sup V d) (2 + m)).hom
      (z - (pull (cpPrU V d) (2 + m) a + cup (pull (cpPrCP V d) 2 h) Y)) = 0 := by
    rw [map_sub, hres, sub_self]
  rcases Nat.lt_or_ge (2 + m) (2 * d + 2) with hlt | hge
  · have hdiff := eq_zero_of_mvResVOf_eq_zero_of_lt K V d (2 + m) hlt _ hzero
    exact ⟨a, Y, sub_eq_zero.mp hdiff⟩
  · obtain ⟨j, hj⟩ : ∃ j, 2 + m = 2 * d + 1 + j + 1 := ⟨m - 2 * d, by omega⟩
    obtain ⟨b, hb⟩ :=
      exists_of_mvResVOf_eq_zero' K V d (2 + m) j hj.symm (by omega) _ hzero
    obtain ⟨γ, hγ⟩ := exists_cup_gen_cpTopOf K V d hgen h h0
    have hcup : cup (pull (cpPrCP V d) 2 h)
        (cohCast (show 2 * d + j = m by omega) (cup γ (pull (cpPrU V d) j b)))
        = cohCast (show 2 * d + 1 + 1 + j = 2 + m by omega)
            (cup (cpTopOf K V d) (pull (cpPrU V d) j b)) := by
      rw [cup_cohCast_right, hγ, cup_cohCast_left, cup_assoc', cohCast_cohCast,
        cohCast_cohCast]
    refine ⟨a, Y + cohCast (show 2 * d + j = m by omega) (cup γ (pull (cpPrU V d) j b)), ?_⟩
    rw [cup_add_right, hcup, ← hb]
    abel

/-! ## 6. The induction -/

/-- **The projective-factor Künneth at every rank over `K`, from generation on the fibre.** -/
theorem cpSplitOf_of_cpGenHypOf (hgen : ∀ e : ℕ, 2 ≤ e → CPGenHypOf K e) :
    ∀ e : ℕ, 1 ≤ e → CPSplitOf K e := by
  intro e
  induction e with
  | zero => exact fun h => absurd h (by omega)
  | succ n ih =>
    intro _hn
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact cpSplitOf_one K
    · exact cpSplitOf_succ K n (by omega) (hgen (n + 1) (by omega)) (ih (by omega))

end KnCP

end

end GroupApproximation.CharClass
