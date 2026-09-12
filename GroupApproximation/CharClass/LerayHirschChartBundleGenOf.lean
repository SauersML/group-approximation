import GroupApproximation.CharClass.LerayHirschChartBundleGen
import GroupApproximation.CharClass.LerayHirschChartGeneralOf

/-!
# The chart step for a projectivised bundle, at general rank, over a coefficient ring

The coefficient-generic twin of `LerayHirschChartBundleGen.LHOver_chart_of_triv`.  The
isomorphism of situations `chartProdIsoOf` carries no coefficients and is the `F₂` file's own;
only the fibre class changes, from `cpGen r hr` to an arbitrary `hfib ∈ H^2(ℂP^r; K)`.

## Main declarations

* `LH.LHOver_chart_of_trivOf` — **the chart step**, over the class identification, over `K`.
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

/-- **The chart step at general rank over `K`**, over the class identification. -/
theorem LHOver_chart_of_trivOf (K : Type) [CommRing K] (p : Bundle X ι)
    (U : Opens (TopCat.of X)) (r : ℕ)
    (e : BundleIso (p.restrictTo ((U : Opens (TopCat.of X)) : Set X))
      (triv ↥((U : Opens (TopCat.of X)) : Set X) (Fin (r + 1))))
    (hfib : Hmod K (CPtop r) 2)
    (hfree : HasFreeTuple (KnCP.cpFst ↥((U : Opens (TopCat.of X)) : Set X) r)
      (pull (KnCP.cpSnd ↥((U : Opens (TopCat.of X)) : Set X) r) 2 hfib) (r + 1))
    (ξ : Hmod K (TopCat.of (Proj p)) 2)
    (hξ : pull (chartProdIsoOf p U r e).hom 2
        (pull (KnCP.cpSnd ↥((U : Opens (TopCat.of X)) : Set X) r) 2 hfib)
      = lhClass (projMapOf p) ξ U) :
    LHOver (projMapOf p) ξ (r + 1) U :=
  LHOver_of_prodIsoOf K (projMapOf p) ξ U r _ hfib hfree (Iso.refl (opSpace U))
    (chartProdIsoOf p U r e) rfl hξ

end

end LH
end CharClass
end GroupApproximation
