import GroupApproximation.CharClass.LerayHirschChartGeneral
import GroupApproximation.CharClass.BundleProjOver
import GroupApproximation.CharClass.BundleLineTriv
import GroupApproximation.CharClass.BundleInvariance

/-!
# The chart step for a projectivised bundle, at general rank

`LerayHirschChartBundle` does this for a projectivised line-plus-trivial, where the
fibre is `ℂP^1`; this is the same assembly at an arbitrary rank, and it is the same
two halves.  `projOverHomeo` identifies the part of `P(E)` lying over an open set
with `P(E|_U)`, and a local trivialisation of `E` there, followed by
`projTrivHomeoCP`, turns that into a product with `ℂP^r`.  Both are over the base,
so the square commutes on the nose.

What is left as a hypothesis is the identification of the classes, which is
cohomology rather than geometry — exactly as at rank two, where it was the last
thing to fall.

## Main declarations

* `projMapOf` — the projection of a projectivised bundle.
* `chartProdIsoOf` — the isomorphism of situations over a trivialising open.
* `LHOver_chart_of_triv` — **the chart step**, over the class identification.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory TopologicalSpace
open GroupApproximation.STW59
open GroupApproximation.CharClass.Bundle

noncomputable section

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The projection of a projectivised bundle, as a morphism of spaces. -/
abbrev projMapOf (p : Bundle X ι) :
    TopCat.of (Proj p) ⟶ TopCat.of X :=
  cmap (projPi p)

/-- **The isomorphism of situations over a trivialising open.**  The part of `P(E)`
lying over `U` is `U × ℂP^r`, over `U`. -/
def chartProdIsoOf (p : Bundle X ι) (U : Opens (TopCat.of X)) (r : ℕ)
    (e : BundleIso (p.restrictTo ((U : Opens (TopCat.of X)) : Set X))
      (triv ↥((U : Opens (TopCat.of X)) : Set X) (Fin (r + 1)))) :
    opSpace (opensComap (projMapOf p) U)
      ≅ TopCat.of (↥((U : Opens (TopCat.of X)) : Set X) × CP r) :=
  TopCat.isoOfHomeo
    ((projOverHomeo p ((U : Opens (TopCat.of X)) : Set X)).symm.trans
      ((BundleIso.projHomeo e).trans projTrivHomeoCP))

/-- **The chart step at general rank**, over the class identification. -/
theorem LHOver_chart_of_triv (p : Bundle X ι) (U : Opens (TopCat.of X)) (r : ℕ)
    (hr : 1 ≤ r)
    (e : BundleIso (p.restrictTo ((U : Opens (TopCat.of X)) : Set X))
      (triv ↥((U : Opens (TopCat.of X)) : Set X) (Fin (r + 1))))
    (hfree : HasFreeTuple (KnCP.cpFst ↥((U : Opens (TopCat.of X)) : Set X) r)
      (pull (KnCP.cpSnd ↥((U : Opens (TopCat.of X)) : Set X) r) 2 (cpGen r hr)) (r + 1))
    (ξ : Hmod2 (TopCat.of (Proj p)) 2)
    (hξ : pull (chartProdIsoOf p U r e).hom 2
        (pull (KnCP.cpSnd ↥((U : Opens (TopCat.of X)) : Set X) r) 2 (cpGen r hr))
      = lhClass (projMapOf p) ξ U) :
    LHOver (projMapOf p) ξ (r + 1) U :=
  LHOver_of_prodIso (projMapOf p) ξ U r hr _ hfree (Iso.refl (opSpace U))
    (chartProdIsoOf p U r e) rfl hξ

end

end LH
end CharClass
end GroupApproximation
