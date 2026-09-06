import GroupApproximation.CharClass.CartanTotalTerm

/-!
# Each summand of the Cartan right-hand side, in the three cases

A summand vanishes when either cup-`i` square is out of range, because a cut of
the simplex cannot hand a factor more vertices than the simplex has.  Otherwise
it is the product of the two squares.

The two vanishing cases are what makes the reindexing possible: the sum runs
over the splittings of the resolution index, the formula's sum runs over the
squares' own indices, and the ranges agree only after both sets of out-of-range
terms are dropped.

## Main results

* `cupSqTerm_eq_zero_left`, `..._right` — the two vanishing cases.
* `totalOf_term_of_good` — the surviving case, as a product of two squares.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

theorem padCochain_zero (X : TopCat.{0}) (k m : ℕ) :
    padCochain X k m (0 : singularCochainGroup (ZMod 2) X k) = 0 := by
  unfold padCochain
  by_cases h : k = m
  · rw [dif_pos h, cochainCast_zero]
  · rw [dif_neg h]

theorem cupSqTerm_eq_zero_left (X : TopCat.{0}) (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (e j' : ℕ) (h : p < j') : cupSqTerm X p q α β e j' = 0 := by
  unfold cupSqTerm
  rw [cochainCupI_self_eq_zero_of_lt p j' h α, cochainCup_zero_left]

theorem cupSqTerm_eq_zero_right (X : TopCat.{0}) (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (e j' : ℕ) (h : q < e - j') : cupSqTerm X p q α β e j' = 0 := by
  unfold cupSqTerm
  rw [cochainCupI_self_eq_zero_of_lt q (e - j') h β, cochainCup_zero_right]

/-- The summand vanishes when either square is out of range. -/
theorem totalOf_term_of_zero (X : TopCat.{0}) (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (hα : cochainCoboundary (ZMod 2) X p α = 0)
    (hβ : cochainCoboundary (ZMod 2) X q β = 0)
    (d e j' : ℕ) (h : cupSqTerm X p q α β e j' = 0) :
    TotalH.of X (d + 1)
        (cocycleClass X (d + 1)
          (padCochain X (p + p - j' + (q + q - (e - j'))) (d + 1)
            (cupSqTerm X p q α β e j'))
          (padCochain_cocycle X _ (d + 1) _
            (cupSqTerm_cocycle X p q α β hα hβ e j'))) = 0 := by
  refine Eq.trans (congrArg (TotalH.of X (d + 1))
    (cocycleClass_congr X (d + 1)
      (show padCochain X (p + p - j' + (q + q - (e - j'))) (d + 1)
          (cupSqTerm X p q α β e j') = 0 from by rw [h, padCochain_zero])
      _ (cochainCoboundary_of_zero X (d + 1)))) ?_
  rw [cocycleClass_zero X (d + 1)]
  exact map_zero _

/-- **The surviving case**: the summand is the product of the two squares. -/
theorem totalOf_term_of_good (X : TopCat.{0}) (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (hα : cochainCoboundary (ZMod 2) X p α = 0)
    (hβ : cochainCoboundary (ZMod 2) X q β = 0)
    (d e j' : ℕ) (hj' : j' ≤ p) (hej : e - j' ≤ q)
    (hK : p + p - j' + (q + q - (e - j')) = d + 1) :
    TotalH.of X (d + 1)
        (cocycleClass X (d + 1)
          (padCochain X (p + p - j' + (q + q - (e - j'))) (d + 1)
            (cupSqTerm X p q α β e j'))
          (padCochain_cocycle X _ (d + 1) _
            (cupSqTerm_cocycle X p q α β hα hβ e j')))
      = TotalH.of X (p - j' + p) (Sq (p - j') (cocycleClass X p α hα))
        * TotalH.of X (q - (e - j') + q)
            (Sq (q - (e - j')) (cocycleClass X q β hβ)) := by
  rw [cocycleClass_padCochain_of_eq X hK (cupSqTerm X p q α β e j')
      (cupSqTerm_cocycle X p q α β hα hβ e j'), Steenrod.of_cohCast]
  exact totalOf_cupSqTerm X p q α β hα hβ e j' hj' hej

end

end GroupApproximation.CharClass
