import GroupApproximation.CharClass.CartanClassSum
import GroupApproximation.CharClass.CartanCupIVanishing
import GroupApproximation.CharClass.SteenrodTotal

/-!
# One summand of the Cartan right-hand side, in the total ring

Each summand is the cup product of two cup-`i` squares, placed in the ambient
degree.  In the total ring its class is the product of the two squares, with no
cast anywhere: the degrees there are plain naturals, so equal values name the
same component and `of_cohCast` absorbs every transport.

That is why the reindexing has to happen here and not at cochain level.  Below
the total ring the same numbers are types, and two spellings of one number are
two different types.

## Main results

* `totalOf_cupI_self` — the class of a cup-`i` square is the square.
* `totalOf_cupSqTerm` — **one summand, as a product of two squares**.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

/-- The cup-`i` square of a cocycle, in the total ring, is the Steenrod square of
its class. -/
theorem totalOf_cupI_self (X : TopCat.{0}) (p : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (hα : cochainCoboundary (ZMod 2) X p α = 0)
    (j' A : ℕ) (hj' : j' ≤ p) (hA : p - j' + p = A)
    (hcoc : cochainCoboundary (ZMod 2) X A (cochainCupI j' p p A α α) = 0) :
    TotalH.of X A (cocycleClass X A (cochainCupI j' p p A α α) hcoc)
      = TotalH.of X (p - j' + p) (Sq (p - j') (cocycleClass X p α hα)) := by
  subst hA
  rw [Sq_mk (p - j') p α hα]
  refine congrArg (TotalH.of X (p - j' + p)) ?_
  refine cocycleClass_congr X (p - j' + p) ?_ hcoc _
  unfold sqCochain
  rw [show p - (p - j') = j' from by omega]

/-- One summand of the right-hand side, before it is placed in the ambient
degree. -/
noncomputable def cupSqTerm (X : TopCat.{0}) (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (e j' : ℕ) : singularCochainGroup (ZMod 2) X (p + p - j' + (q + q - (e - j'))) :=
  cochainCup (p + p - j') (q + q - (e - j'))
    (cochainCupI j' p p (p + p - j') α α)
    (cochainCupI (e - j') q q (q + q - (e - j')) β β)

theorem cupSqTerm_cocycle (X : TopCat.{0}) (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (hα : cochainCoboundary (ZMod 2) X p α = 0)
    (hβ : cochainCoboundary (ZMod 2) X q β = 0) (e j' : ℕ) :
    cochainCoboundary (ZMod 2) X (p + p - j' + (q + q - (e - j')))
        (cupSqTerm X p q α β e j') = 0 :=
  cochainCupZMod2_respects_cocycles _ _ _ _
    (cochainCupI_self_cocycle j' p _ α hα)
    (cochainCupI_self_cocycle (e - j') q _ β hβ)

/-- **One summand, as a product of two squares.** -/
theorem totalOf_cupSqTerm (X : TopCat.{0}) (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (hα : cochainCoboundary (ZMod 2) X p α = 0)
    (hβ : cochainCoboundary (ZMod 2) X q β = 0)
    (e j' : ℕ) (hj' : j' ≤ p) (hej : e - j' ≤ q) :
    TotalH.of X (p + p - j' + (q + q - (e - j')))
        (cocycleClass X (p + p - j' + (q + q - (e - j')))
          (cupSqTerm X p q α β e j') (cupSqTerm_cocycle X p q α β hα hβ e j'))
      = TotalH.of X (p - j' + p) (Sq (p - j') (cocycleClass X p α hα))
        * TotalH.of X (q - (e - j') + q)
            (Sq (q - (e - j')) (cocycleClass X q β hβ)) := by
  rw [show cocycleClass X (p + p - j' + (q + q - (e - j')))
        (cupSqTerm X p q α β e j') (cupSqTerm_cocycle X p q α β hα hβ e j')
      = cup (cocycleClass X (p + p - j')
              (cochainCupI j' p p (p + p - j') α α)
              (cochainCupI_self_cocycle j' p _ α hα))
            (cocycleClass X (q + q - (e - j'))
              (cochainCupI (e - j') q q (q + q - (e - j')) β β)
              (cochainCupI_self_cocycle (e - j') q _ β hβ)) from
      (cup_mk _ _ _ _).symm,
    TotalH.of_mul,
    totalOf_cupI_self X p α hα j' (p + p - j') hj' (by omega) _,
    totalOf_cupI_self X q β hβ (e - j') (q + q - (e - j')) hej (by omega) _]

end

end GroupApproximation.CharClass
