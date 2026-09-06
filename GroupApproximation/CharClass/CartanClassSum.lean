import GroupApproximation.CharClass.CartanRhsSum

/-!
# Classes of sums, and of padded cochains

Taking the class of the right-hand side means taking the class of a sum, and of
each summand, which is a cochain placed in a degree.  This file supplies both,
and the bridge from a degree cast on cochains to one on classes.

## Main results

* `cocycleClass_cochainCast` — a cast on cochains is a cast on classes.
* `cocycleClass_finset_sum` — the class of a sum is the sum of the classes.
* `padCochain_cocycle`, `cocycleClass_padCochain_of_eq`,
  `cocycleClass_padCochain_of_ne` — the class of a padded cochain.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

/-- The coboundary of the zero cochain. -/
theorem cochainCoboundary_of_zero (X : TopCat.{0}) (m : ℕ) :
    cochainCoboundary (ZMod 2) X m (0 : singularCochainGroup (ZMod 2) X m) = 0 := by
  apply cochain_ext
  intro σ
  rw [cochainCoboundary_eval, cochainEval_zero]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [cochainEval_zero, mul_zero]

/-- **A degree cast on cochains is a degree cast on classes.** -/
theorem cocycleClass_cochainCast (X : TopCat.{0}) {m m' : ℕ} (h : m = m')
    (φ : singularCochainGroup (ZMod 2) X m)
    (hφ : cochainCoboundary (ZMod 2) X m φ = 0)
    (hφ' : cochainCoboundary (ZMod 2) X m' (cochainCast h φ) = 0) :
    cocycleClass X m' (cochainCast h φ) hφ' = cohCast h (cocycleClass X m φ hφ) := by
  subst h
  rw [cohCast_rfl]
  exact cocycleClass_congr X m (cochainCast_rfl φ) hφ' hφ

/-! ## Sums -/

theorem cochainCoboundary_finset_sum {ι : Type} (X : TopCat.{0}) (m : ℕ) (s : Finset ι)
    (f : ι → singularCochainGroup (ZMod 2) X m)
    (hf : ∀ i, cochainCoboundary (ZMod 2) X m (f i) = 0) :
    cochainCoboundary (ZMod 2) X m (∑ i ∈ s, f i) = 0 := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty]
    exact cochainCoboundary_of_zero X m
  · intro a t ha ih
    rw [Finset.sum_insert ha, cochainCoboundary_add, hf a, ih, add_zero]

/-- **The class of a sum is the sum of the classes.** -/
theorem cocycleClass_finset_sum {ι : Type} (X : TopCat.{0}) (m : ℕ) (s : Finset ι)
    (f : ι → singularCochainGroup (ZMod 2) X m)
    (hf : ∀ i, cochainCoboundary (ZMod 2) X m (f i) = 0) :
    ∀ hs : cochainCoboundary (ZMod 2) X m (∑ i ∈ s, f i) = 0,
      cocycleClass X m (∑ i ∈ s, f i) hs = ∑ i ∈ s, cocycleClass X m (f i) (hf i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · intro hs
    refine Eq.trans (cocycleClass_congr X m Finset.sum_empty hs
      (cochainCoboundary_of_zero X m)) ?_
    rw [Finset.sum_empty]
    exact cocycleClass_zero X m _
  · intro a t ha ih hs
    have hsum : cochainCoboundary (ZMod 2) X m (f a + ∑ i ∈ t, f i) = 0 := by
      rw [← Finset.sum_insert ha]
      exact hs
    have ht : cochainCoboundary (ZMod 2) X m (∑ i ∈ t, f i) = 0 :=
      cochainCoboundary_finset_sum X m t f hf
    refine Eq.trans (cocycleClass_congr X m (Finset.sum_insert ha) hs hsum) ?_
    rw [cocycleClass_add X m (f a) (∑ i ∈ t, f i) (hf a) ht hsum, ih ht,
      Finset.sum_insert ha]

/-! ## Padded cochains -/

theorem padCochain_cocycle (X : TopCat.{0}) (k m : ℕ)
    (γ : singularCochainGroup (ZMod 2) X k)
    (hγ : cochainCoboundary (ZMod 2) X k γ = 0) :
    cochainCoboundary (ZMod 2) X m (padCochain X k m γ) = 0 := by
  unfold padCochain
  by_cases h : k = m
  · rw [dif_pos h]
    exact cochainCoboundary_cochainCast_eq_zero h γ hγ
  · rw [dif_neg h]
    exact cochainCoboundary_of_zero X m

theorem cocycleClass_padCochain_of_eq (X : TopCat.{0}) {k m : ℕ} (h : k = m)
    (γ : singularCochainGroup (ZMod 2) X k)
    (hγ : cochainCoboundary (ZMod 2) X k γ = 0) :
    cocycleClass X m (padCochain X k m γ) (padCochain_cocycle X k m γ hγ)
      = cohCast h (cocycleClass X k γ hγ) := by
  subst h
  refine Eq.trans (cocycleClass_congr X k (show padCochain X k k γ = γ from by
    unfold padCochain
    rw [dif_pos rfl, cochainCast_rfl]) _ hγ) ?_
  rw [cohCast_rfl]

theorem cocycleClass_padCochain_of_ne (X : TopCat.{0}) {k m : ℕ} (h : ¬ k = m)
    (γ : singularCochainGroup (ZMod 2) X k)
    (hγ : cochainCoboundary (ZMod 2) X k γ = 0) :
    cocycleClass X m (padCochain X k m γ) (padCochain_cocycle X k m γ hγ) = 0 := by
  refine Eq.trans (cocycleClass_congr X m (show padCochain X k m γ = 0 from by
    unfold padCochain
    rw [dif_neg h]) _ (cochainCoboundary_of_zero X m)) ?_
  exact cocycleClass_zero X m _

end

end GroupApproximation.CharClass
