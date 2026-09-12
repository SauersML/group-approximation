import GroupApproximation.CharClass.LerayHirschChartBundleGen

/-!
# The chart step from a homeomorphism, not an isomorphism of bundles

`LerayHirschChartBundleGen` asks for a local trivialisation as a `BundleIso`.  That
is the wrong request, and expensively so: `cc-bundle`'s intertwiner over a
trivialising set is invertible but not unitary, and turning it into a family of
partial isometries needs a continuous inverse square root of a positive matrix
field, which is not in the tree at this pin.

Nothing in the chart step wants a bundle isomorphism.  The hypothesis was used in
exactly one place, and only to produce a homeomorphism of the part of `P(E)` over
the open set with a product.  So this file asks for that homeomorphism directly,
together with the one property the square needs, which is that it is over the base.
`cc-bundle`'s `projTrivStd` is that homeomorphism and its base compatibility is
`rfl`.

`cc-thom` met the same obstruction on the total-space side and dissolved it the same
way, by consuming `totalTrivStd` rather than an isomorphism.  Under rule 11 the
earlier statements keep their names; these are new ones.

## Main declarations

* `chartProdIsoOfHomeo` — the isomorphism of situations, from a homeomorphism.
* `LHOver_chart_of_homeo` — **the chart step**, over that and the class identification.
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

/-- **The isomorphism of situations, from a homeomorphism.**  No bundle isomorphism
is involved; `projOverHomeo` is composed with whatever trivialisation of the
restricted projective bundle the caller has. -/
def chartProdIsoOfHomeo (p : Bundle X ι) (U : Opens (TopCat.of X)) (r : ℕ)
    (h : Proj (p.restrictTo ((U : Opens (TopCat.of X)) : Set X))
      ≃ₜ ↥((U : Opens (TopCat.of X)) : Set X) × CP r) :
    opSpace (opensComap (projMapOf p) U)
      ≅ TopCat.of (↥((U : Opens (TopCat.of X)) : Set X) × CP r) :=
  TopCat.isoOfHomeo
    ((projOverHomeo p ((U : Opens (TopCat.of X)) : Set X)).symm.trans h)

/-- **The chart step at general rank, from a homeomorphism over the base.** -/
theorem LHOver_chart_of_homeo (p : Bundle X ι) (U : Opens (TopCat.of X)) (r : ℕ)
    (hr : 1 ≤ r)
    (h : Proj (p.restrictTo ((U : Opens (TopCat.of X)) : Set X))
      ≃ₜ ↥((U : Opens (TopCat.of X)) : Set X) × CP r)
    (hbase : ∀ z, (h z).1 = projPi (p.restrictTo ((U : Opens (TopCat.of X)) : Set X)) z)
    (hfree : HasFreeTuple (KnCP.cpFst ↥((U : Opens (TopCat.of X)) : Set X) r)
      (pull (KnCP.cpSnd ↥((U : Opens (TopCat.of X)) : Set X) r) 2 (cpGen r hr)) (r + 1))
    (ξ : Hmod2 (TopCat.of (Proj p)) 2)
    (hξ : pull (chartProdIsoOfHomeo p U r h).hom 2
        (pull (KnCP.cpSnd ↥((U : Opens (TopCat.of X)) : Set X) r) 2 (cpGen r hr))
      = lhClass (projMapOf p) ξ U) :
    LHOver (projMapOf p) ξ (r + 1) U :=
  LHOver_of_prodIso (projMapOf p) ξ U r hr _ hfree (Iso.refl (opSpace U))
    (chartProdIsoOfHomeo p U r h)
    (TopCat.hom_ext (ContinuousMap.ext fun z =>
      hbase ((projOverHomeo p ((U : Opens (TopCat.of X)) : Set X)).symm z))) hξ

end

end LH
end CharClass
end GroupApproximation
