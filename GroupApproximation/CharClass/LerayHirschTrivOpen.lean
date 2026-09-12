import GroupApproximation.CharClass.LerayHirschRankOne
import GroupApproximation.CharClass.LerayHirschChartHomeo
import GroupApproximation.CharClass.LerayHirschBundle
import GroupApproximation.CharClass.BundleLocalOn

/-!
# The chart step over a trivialising open

`LHOver_chart_of_homeo` takes four inputs; three of them are now available for a
trivialising open of any bundle, and this file supplies them.  `cc-bundle`'s
`projTrivStdOn` is the homeomorphism, over an arbitrary subset of a trivialising
set, which is what the cover induction needs since its predicate must be closed
under intersection with anything.  Its base compatibility is `rfl`, and the
free-module statement is the ladder, unconditional.

What is left is the class identification at the chart, which is the last piece of
geometry in this chain and is waiting on an intertwiner from `cc-bundle`.

## Main declarations

* `trivInter_subset` — the intersection is still trivialising.
* `LHOver_trivOpen` — **the chart step over a trivialising open**, over the class
  identification.
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

/-- Cutting a trivialising set down leaves it inside the trivialising set, which is
what the cover induction needs. -/
theorem trivInter_subset (q : Bundle X ι) (x₀ : X) (W : Opens (TopCat.of X)) :
    ((trivOpen q x₀ ⊓ W : Opens (TopCat.of X)) : Set X) ⊆ trivSet q x₀ := by
  intro x hx
  exact hx.1

/-- **The chart step over a trivialising open**, with everything discharged except
the class identification. -/
theorem LHOver_trivOpen (q : Bundle X ι) (x₀ : X) (W : Opens (TopCat.of X)) (d : ℕ)
    (hrank : q.rank x₀ = d + 1 + 1)
    (hξ : pull (chartProdIsoOfHomeo q (trivOpen q x₀ ⊓ W) (d + 1)
          (projTrivStdOn q x₀
            ((trivOpen q x₀ ⊓ W : Opens (TopCat.of X)) : Set X)
            (trivInter_subset q x₀ W) (d + 1) hrank)).hom 2
        (pull (KnCP.cpSnd
          ↥((trivOpen q x₀ ⊓ W : Opens (TopCat.of X)) : Set X) (d + 1)) 2
          (cpGen (d + 1) (by omega)))
      = lhClass (projMapOf q) (tautEulerOf q) (trivOpen q x₀ ⊓ W)) :
    LHOver (projMapOf q) (tautEulerOf q) (d + 2) (trivOpen q x₀ ⊓ W) :=
  LHOver_chart_of_homeo q (trivOpen q x₀ ⊓ W) (d + 1) (by omega)
    (projTrivStdOn q x₀ _ (trivInter_subset q x₀ W) (d + 1) hrank)
    (fun z => projTrivStdOn_over_base q x₀ _ (trivInter_subset q x₀ W) (d + 1)
      hrank z)
    (hasFreeTuple_cpProd _ d (by omega)) (tautEulerOf q) hξ

end

end LH
end CharClass
end GroupApproximation
