import GroupApproximation.CharClass.LerayHirschChartHomeo
import GroupApproximation.CharClass.LerayHirschChartGeneralOf

/-!
# The chart step from a homeomorphism, over a coefficient ring

The coefficient-generic twin of `LerayHirschChartHomeo.LHOver_chart_of_homeo`.  The
homeomorphism, its base compatibility and `chartProdIsoOfHomeo` carry no coefficients and are the
`F₂` file's own.  The free-module statement stays an argument, as in `F₂`, and the fibre class is
an arbitrary `hfib ∈ H^2(ℂP^r; K)`.

## Main declarations

* `LH.LHOver_chart_of_homeoOf` — **the chart step**, from a homeomorphism over the base, over `K`.
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

/-- **The chart step at general rank over `K`, from a homeomorphism over the base.** -/
theorem LHOver_chart_of_homeoOf (K : Type) [CommRing K] (p : Bundle X ι)
    (U : Opens (TopCat.of X)) (r : ℕ)
    (h : Proj (p.restrictTo ((U : Opens (TopCat.of X)) : Set X))
      ≃ₜ ↥((U : Opens (TopCat.of X)) : Set X) × CP r)
    (hbase : ∀ z, (h z).1 = projPi (p.restrictTo ((U : Opens (TopCat.of X)) : Set X)) z)
    (hfib : Hmod K (CPtop r) 2)
    (hfree : HasFreeTuple (KnCP.cpFst ↥((U : Opens (TopCat.of X)) : Set X) r)
      (pull (KnCP.cpSnd ↥((U : Opens (TopCat.of X)) : Set X) r) 2 hfib) (r + 1))
    (ξ : Hmod K (TopCat.of (Proj p)) 2)
    (hξ : pull (chartProdIsoOfHomeo p U r h).hom 2
        (pull (KnCP.cpSnd ↥((U : Opens (TopCat.of X)) : Set X) r) 2 hfib)
      = lhClass (projMapOf p) ξ U) :
    LHOver (projMapOf p) ξ (r + 1) U :=
  LHOver_of_prodIsoOf K (projMapOf p) ξ U r _ hfib hfree (Iso.refl (opSpace U))
    (chartProdIsoOfHomeo p U r h)
    (TopCat.hom_ext (ContinuousMap.ext fun z =>
      hbase ((projOverHomeo p ((U : Opens (TopCat.of X)) : Set X)).symm z))) hξ

end

end LH
end CharClass
end GroupApproximation
