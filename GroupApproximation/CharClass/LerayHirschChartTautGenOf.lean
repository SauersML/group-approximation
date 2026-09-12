import GroupApproximation.CharClass.LerayHirschChartTautGen
import GroupApproximation.CharClass.LerayHirschChartClassIsoOf
import GroupApproximation.CharClass.BundleRankCard

/-!
# The class identification at a trivialising chart, over a coefficient field

The coefficient-generic form of `LerayHirschCompact.hxi_trivOpen`.  The chart maps
(`chartInclOf`, `chartCPOf`), the identification of the tautological lines
(`chartTautIsoGen`) and the trivialisation `projTrivStdOn` carry no coefficients and are the `F₂`
files' own; the cohomological content is `pull_prodIso_fibClassOf` at those maps.

## Main declarations

* `LH.rank_le_one_add_tautCardOf` — the rank bound the fibre class is computed at.
* `LH.hxi_trivOpenOf` — **the class identification at a trivialising chart**, over `K`.
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

/-- The fibre of a projectivised bundle of rank `d + 2` is `ℂP^{d+1}`, and `d + 1` is at most
the index size the tautological class is computed at. -/
theorem rank_le_one_add_tautCardOf (q : Bundle X ι) (x₀ : X) (d : ℕ)
    (hrank : q.rank x₀ = d + 1 + 1) : d + 1 ≤ 1 + tautCardOf ι := by
  have h := rank_le_card q x₀
  rw [hrank] at h
  show d + 1 ≤ 1 + Fintype.card ι
  omega

/-- **The class identification at a trivialising chart, over `K`.**  The tautological class
relative to `hgen`, restricted to the part over a trivialising open, is the pulled-back fibre
class. -/
theorem hxi_trivOpenOf (K : Type) [Field K] (q : Bundle X ι) (x₀ : X)
    (W : Opens (TopCat.of X)) (d : ℕ) (hrank : q.rank x₀ = d + 1 + 1)
    (hgen : Hmod K (CPtop (1 + tautCardOf ι)) 2) :
    pull (chartProdIsoOfHomeo q (trivOpen q x₀ ⊓ W) (d + 1)
          (projTrivStdOn q x₀ _ (trivInter_subset q x₀ W) (d + 1) hrank)).hom 2
        (pull (KnCP.cpSnd
          ↥((trivOpen q x₀ ⊓ W : Opens (TopCat.of X)) : Set X) (d + 1)) 2
          (fibClassOf K hgen (d + 1) (rank_le_one_add_tautCardOf q x₀ d hrank)))
      = lhClass (projMapOf q) (tautEulerOfK K hgen q) (trivOpen q x₀ ⊓ W) :=
  pull_prodIso_fibClassOf K q (trivOpen q x₀ ⊓ W) (d + 1) _
    (chartCPOf q x₀ (trivOpen q x₀ ⊓ W) (trivInter_subset q x₀ W) (d + 1) hrank) rfl
    (chartInclOf q (trivOpen q x₀ ⊓ W)) rfl (rank_le_one_add_tautCardOf q x₀ d hrank)
    (chartTautIsoGen q x₀ (trivOpen q x₀ ⊓ W) (trivInter_subset q x₀ W) (d + 1) hrank) hgen

end

end LH
end CharClass
end GroupApproximation
