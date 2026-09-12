import GroupApproximation.CharClass.LerayHirschChartHomeoOf
import GroupApproximation.CharClass.LerayHirschTrivOpen

/-!
# The chart step over a trivialising open, over a coefficient ring

The coefficient-generic form of `LerayHirschTrivOpen.LHOver_trivOpen`.  `cc-bundle`'s
`projTrivStdOn` is the homeomorphism over an arbitrary subset of a trivialising set, its base
compatibility is `projTrivStdOn_over_base`, and both carry no coefficients.  So over `K` the chart
step `LHOver_chart_of_homeoOf` applies with the free-module statement and the class identification
left as the two inputs, for any fibre class `hfib ∈ H^2(ℂP^{d+1}; K)` and any class `ξ` on the total
space.

## Main declarations

* `LHOver_trivOpenOf` — **the chart step over a trivialising open, over `K`**, over the free-module
  statement and the class identification.
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

/-- **The chart step over a trivialising open, over `K`.**  Everything is discharged except the
free-module statement for the product with the fibre class and the class identification. -/
theorem LHOver_trivOpenOf (K : Type) [CommRing K] (q : Bundle X ι) (x₀ : X)
    (W : Opens (TopCat.of X)) (d : ℕ) (hrank : q.rank x₀ = d + 1 + 1)
    (hfib : Hmod K (CPtop (d + 1)) 2)
    (hfree : HasFreeTuple
      (KnCP.cpFst ↥((trivOpen q x₀ ⊓ W : Opens (TopCat.of X)) : Set X) (d + 1))
      (pull (KnCP.cpSnd ↥((trivOpen q x₀ ⊓ W : Opens (TopCat.of X)) : Set X) (d + 1)) 2 hfib)
      (d + 1 + 1))
    (ξ : Hmod K (TopCat.of (Proj q)) 2)
    (hξ : pull (chartProdIsoOfHomeo q (trivOpen q x₀ ⊓ W) (d + 1)
          (projTrivStdOn q x₀
            ((trivOpen q x₀ ⊓ W : Opens (TopCat.of X)) : Set X)
            (trivInter_subset q x₀ W) (d + 1) hrank)).hom 2
        (pull (KnCP.cpSnd ↥((trivOpen q x₀ ⊓ W : Opens (TopCat.of X)) : Set X) (d + 1)) 2 hfib)
      = lhClass (projMapOf q) ξ (trivOpen q x₀ ⊓ W)) :
    LHOver (projMapOf q) ξ (d + 2) (trivOpen q x₀ ⊓ W) :=
  LHOver_chart_of_homeoOf K q (trivOpen q x₀ ⊓ W) (d + 1)
    (projTrivStdOn q x₀ _ (trivInter_subset q x₀ W) (d + 1) hrank)
    (fun z => projTrivStdOn_over_base q x₀ _ (trivInter_subset q x₀ W) (d + 1) hrank z)
    hfib hfree ξ hξ

end

end LH
end CharClass
end GroupApproximation
