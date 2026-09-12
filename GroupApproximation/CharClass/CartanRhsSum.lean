import GroupApproximation.CharClass.CartanClassId

/-!
# The right-hand side as a sum of cochains

`cartanRhsCochain` is a cochain named by the function it is, which was the right
shape for the evaluated identity but the wrong one for taking classes.  This file
presents the same cochain as a sum, one summand per splitting of the resolution
index, so that the class of the whole is the sum of the classes.

The summands are placed in the ambient degree by `padCochain`, which is the
totalisation recipe applied to cochains: a cochain of the wrong degree becomes
zero rather than a cast.  That is exactly what the evaluated form said, since
`evAt` already vanishes off its own degree.

## Main results

* `padCochain` — a cochain placed in a degree, or zero.
* `cartanRhsCochain_eq_sum` — the right-hand side, as a sum.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

/-- A cochain placed in degree `m`, and `0` if its own degree is not `m`. -/
noncomputable def padCochain (X : TopCat.{0}) (k m : ℕ)
    (γ : singularCochainGroup (ZMod 2) X k) : singularCochainGroup (ZMod 2) X m :=
  if h : k = m then cochainCast h γ else 0

theorem cochainEval_padCochain (X : TopCat.{0}) (k m : ℕ)
    (γ : singularCochainGroup (ZMod 2) X k) (σ : singularSimplices X m) :
    cochainEval m (padCochain X k m γ) σ = evAt X k γ m σ := by
  unfold padCochain
  by_cases h : k = m
  · subst h
    rw [dif_pos rfl, cochainCast_rfl, evAt_self]
  · rw [dif_neg h, cochainEval_zero, evAt_of_ne X k γ m (fun hh => h hh.symm)]

theorem cochainEval_finset_sum {ι : Type} (X : TopCat.{0}) (m : ℕ) (s : Finset ι)
    (f : ι → singularCochainGroup (ZMod 2) X m) (σ : singularSimplices X m) :
    cochainEval m (∑ i ∈ s, f i) σ = ∑ i ∈ s, cochainEval m (f i) σ := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, cochainEval_zero]
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, cochainEval_add, ih]

/-- The right-hand side of the Cartan formula, as a sum of cochains. -/
noncomputable def cartanRhsSum (X : TopCat.{0}) (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (d e : ℕ) : singularCochainGroup (ZMod 2) X (d + 1) :=
  ∑ j' ∈ Finset.range (e + 1),
    padCochain X (p + p - j' + (q + q - (e - j'))) (d + 1)
      (cochainCup (p + p - j') (q + q - (e - j'))
        (cochainCupI j' p p (p + p - j') α α)
        (cochainCupI (e - j') q q (q + q - (e - j')) β β))

theorem cartanRhsCochain_eq_sum (X : TopCat.{0}) (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (d e : ℕ) :
    cartanRhsCochain X p q α β d e = cartanRhsSum X p q α β d e := by
  apply cochain_ext
  intro σ
  rw [cartanRhsCochain, cochainEval_cochainOfFun, cartanRhsSum,
    cochainEval_finset_sum]
  exact Finset.sum_congr rfl fun j' _ =>
    (cochainEval_padCochain X _ (d + 1) _ σ).symm

end

end GroupApproximation.CharClass
