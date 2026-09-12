import GroupApproximation.CharClass.LerayHirschChartTwo
import GroupApproximation.CharClass.BundleProjOver
import GroupApproximation.CharClass.BundleLineTriv

/-!
# The chart step for a projectivised line bundle

`LHOver_two_of_prodIso` asks for an isomorphism of situations; over a chart of a
line bundle `cc-bundle` supplies it in two halves.  `projOverHomeo` identifies the
projectivisation of the restricted bundle with the part of the projectivisation
lying over the open set, and `projPlusOneHomeoCPOne` trivialises that as a product
with `ℂP^1`.  Both are over the base, so the square commutes on the nose.

`restrictTo_plusOne` holds definitionally, which is what lets the two halves
compose with no transport between them: the projectivisation of the restricted
sum and the restriction of the projectivised sum are the *same type*.

The one thing left as a hypothesis is the identification of the classes, which is
cohomology rather than geometry.

## Main declarations

* `chartProdIso` — the isomorphism of situations over a chart.
* `LHOver_two_chart` — **the chart step**, over the class identification.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory TopologicalSpace

noncomputable section

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The projection of the projectivised sum, as a morphism of spaces. -/
abbrev projMap (p : Bundle X ι) :
    TopCat.of (Bundle.Proj p.plusOne) ⟶ TopCat.of X :=
  cmap (Bundle.projPi p.plusOne)

/-- **The isomorphism of situations over a chart**: the part of the projectivised
sum lying over `U` is `U × ℂP^1`, over `U`. -/
def chartProdIso (p : Bundle X ι) (U : Opens (TopCat.of X))
    (hp : ∀ x : ↥((U : Opens (TopCat.of X)) : Set X),
      ((p.restrictTo ((U : Opens (TopCat.of X)) : Set X)) x).trace = 1)
    (i : ι)
    (hi : ∀ x : ↥((U : Opens (TopCat.of X)) : Set X),
      (p.restrictTo ((U : Opens (TopCat.of X)) : Set X)) x i i ≠ 0) :
    opSpace (opensComap (projMap p) U)
      ≅ KnCP.cpProdTop ↥((U : Opens (TopCat.of X)) : Set X) 0 :=
  TopCat.isoOfHomeo
    ((Bundle.projOverHomeo p.plusOne ((U : Opens (TopCat.of X)) : Set X)).symm.trans
      (Bundle.projPlusOneHomeoCPOne
        (p.restrictTo ((U : Opens (TopCat.of X)) : Set X)) hp i hi))

/-- **Leray–Hirsch over a chart of a line bundle**, once the two classes are
identified. -/
theorem LHOver_two_chart (p : Bundle X ι) (U : Opens (TopCat.of X))
    (hp : ∀ x : ↥((U : Opens (TopCat.of X)) : Set X),
      ((p.restrictTo ((U : Opens (TopCat.of X)) : Set X)) x).trace = 1)
    (i : ι)
    (hi : ∀ x : ↥((U : Opens (TopCat.of X)) : Set X),
      (p.restrictTo ((U : Opens (TopCat.of X)) : Set X)) x i i ≠ 0)
    (ξ : Hmod2 (TopCat.of (Bundle.Proj p.plusOne)) 2)
    (hξ : pull (chartProdIso p U hp i hi).hom 2
        (KnCP.cpTaut ↥((U : Opens (TopCat.of X)) : Set X))
      = lhClass (projMap p) ξ U) :
    LHOver (projMap p) ξ 2 U :=
  LHOver_two_of_prodIso (projMap p) ξ U _ (Iso.refl (opSpace U))
    (chartProdIso p U hp i hi) rfl hξ

end

end LH
end CharClass
end GroupApproximation
