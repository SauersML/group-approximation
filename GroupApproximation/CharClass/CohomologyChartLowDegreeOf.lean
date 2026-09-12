import GroupApproximation.CharClass.CohomologyChartInductionOf

/-!
# The projection of `U × ℂP^d` below degree two, over a field

The coefficient-generic form of `CohomologyChartLowDegree`: pullback along `U × ℂP^d → U` is
injective in every degree (a slice) and surjective below degree two (fibre connectivity, by
induction on `d` over the injectivity of the restriction below `2d + 2`).  No generation hypothesis
is used.

## Main declarations

* `KnCP.pull_cpFst_injectiveOf`, `KnCP.exists_pull_cpFst_of_ltOf`, `KnCP.lhLow_generalOf`.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.STW59
open GroupApproximation.CharClass.CPn

namespace GroupApproximation.CharClass

noncomputable section

namespace KnCP

variable (K : Type) [Field K] (U : Type) [TopologicalSpace U] (d : ℕ)

/-- **Pullback along the projection is injective in every degree**, at any rank, over `K`. -/
theorem pull_cpFst_injectiveOf (k : ℕ) :
    Function.Injective (pull (K := K) (cpFst U d) k) := by
  obtain ⟨p⟩ := nonempty_CPtop d
  intro c₁ c₂ hc
  have h := congrArg (pull (cpSliceGen U d p) k) hc
  rwa [← pull_comp, ← pull_comp, cpSliceGen_comp_cpFst, pull_id, pull_id] at h

set_option maxHeartbeats 1000000 in
/-- **Below degree two every class is pulled back from the base**, at any rank, over `K`. -/
theorem exists_pull_cpFst_of_ltOf (k : ℕ) (hk : k < 2) :
    ∀ z : Hmod K (TopCat.of (U × CP d)) k,
      ∃ a : Hmod K (TopCat.of U) k, z = pull (cpFst U d) k a := by
  induction d with
  | zero =>
    intro z
    refine ⟨(cohProdContractibleOf K U (CP 0) k).symm z, ?_⟩
    have h := (cohProdContractibleOf K U (CP 0) k).apply_symm_apply z
    rw [cohProdContractibleOf_apply_eq] at h
    exact h.symm
  | succ e ih =>
    intro z
    obtain ⟨w', hw'⟩ : ∃ w', pull (cmap (punctHomotopyEquiv U e).toFun) k w'
        = (mvResVOf K (chartU U e) (punctU U e) (cp_sup U e) k).hom z :=
      ⟨(punctPullEquivOf K U e k).symm _, (punctPullEquivOf K U e k).apply_symm_apply _⟩
    obtain ⟨a, ha⟩ := ih w'
    refine ⟨a, ?_⟩
    have hV : (mvResVOf K (chartU U e) (punctU U e) (cp_sup U e) k).hom
        (z - pull (cpPrU U e) k a) = 0 := by
      rw [map_sub, mvResVOf_pull_cpPrU, ← hw', ha, pull_punctHE_prUOf, sub_self]
    have hzero := eq_zero_of_mvResVOf_eq_zero_of_lt K U e k (by omega) _ hV
    exact sub_eq_zero.mp hzero

/-- **The floor of the ladder at an arbitrary fibre, over `K`.** -/
theorem lhLow_generalOf (n : ℕ) (hn : n < 2) :
    Function.Bijective (pull (K := K) (cpFst U d) n) :=
  ⟨pull_cpFst_injectiveOf K U d n, fun z => by
    obtain ⟨a, ha⟩ := exists_pull_cpFst_of_ltOf K U d n hn z
    exact ⟨a, ha.symm⟩⟩

end KnCP

end

end GroupApproximation.CharClass
