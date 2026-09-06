import GroupApproximation.CharClass.SteenrodCochain

/-!
# The cup-`i` product vanishes when a factor outranks the simplex

`cochainCupI_of_degree_ne` is one of the two reasons a cup-`i` product is zero:
the bidegree is wrong.  This file supplies the other, which the Cartan
reindexing needs and which the bidegree condition does not cover.

A cut of an `n`-simplex hands each factor a set of vertices, and there are only
`n + 1` of them.  So an `a`-cochain, which needs `a + 1`, contributes nothing
once `a` exceeds `n`, whatever the bidegree says.  That is cochain-level
instability: the cup-`i` square of an `a`-cochain vanishes once `i` exceeds `a`,
which is exactly the range of the Cartan sum that has to disappear.

## Main results

* `cochainCupI_eq_zero_of_lt_left`, `..._right` — a factor outranking the
  simplex kills the product.
* `cochainCupI_self_eq_zero_of_lt` — **cochain-level instability**.
-/

open CategoryTheory Limits AlgebraicTopology Simplicial SimplexCategory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation.CharClass

noncomputable section

variable {X : TopCat.{0}}

theorem cochainCupI_eq_zero_of_lt_left (i a b n : ℕ) (h : n < a)
    (γ : singularCochainGroup (ZMod 2) X a) (δ : singularCochainGroup (ZMod 2) X b) :
    cochainCupI i a b n γ δ = 0 := by
  apply cochain_ext
  intro σ
  rw [cochainCupI_eval, cochainEval_zero]
  refine Finset.sum_eq_zero fun S _ => ?_
  refine mul_eq_zero_of_left (faceVal_of_card_ne γ σ ?_) _
  have hcard : (cutU S).card ≤ n + 1 := by
    have hle := Finset.card_le_univ (cutU S)
    simpa using hle
  omega

theorem cochainCupI_eq_zero_of_lt_right (i a b n : ℕ) (h : n < b)
    (γ : singularCochainGroup (ZMod 2) X a) (δ : singularCochainGroup (ZMod 2) X b) :
    cochainCupI i a b n γ δ = 0 := by
  apply cochain_ext
  intro σ
  rw [cochainCupI_eval, cochainEval_zero]
  refine Finset.sum_eq_zero fun S _ => ?_
  refine mul_eq_zero_of_right _ (faceVal_of_card_ne δ σ ?_)
  have hcard : (cutV S).card ≤ n + 1 := by
    have hle := Finset.card_le_univ (cutV S)
    simpa using hle
  omega

/-- **Cochain-level instability.**  The cup-`i` square of an `a`-cochain, at the
degree it lands in, vanishes once `i` exceeds `a`.  For a positive degree the
simplex is too small for either factor; in degree zero the bidegree fails
instead. -/
theorem cochainCupI_self_eq_zero_of_lt (a i : ℕ) (h : a < i)
    (γ : singularCochainGroup (ZMod 2) X a) :
    cochainCupI i a a (a + a - i) γ γ = 0 := by
  by_cases ha : a = 0
  · subst ha
    exact cochainCupI_of_degree_ne i 0 0 (0 + 0 - i) (by omega) γ γ
  · exact cochainCupI_eq_zero_of_lt_left i a a (a + a - i) (by omega) γ γ

end

end GroupApproximation.CharClass
