import GroupApproximation.CharClass.LerayHirschTrivOpen
import GroupApproximation.CharClass.LerayHirschChartClassIso
import GroupApproximation.CharClass.BundleChartTaut

/-!
# The class identification at a trivialising chart

`cc-bundle`'s `tautLineIsoChartCP` says the chart trivialisation carries the
tautological line to the pullback of the tautological line of `ℂP^d`, at every rank.
That was the last piece of geometry in this chain, and it is what the rank-two case
got from `tautLineIsoCPOne`.

Pulling it back along the identification of the part over the open set with the
projectivisation of the restriction turns it into the hypothesis the class
identification takes, and every transport is `rfl`, for the reason that has held all
the way through: nothing in the bundle lane touches the base coordinate.

## Main declarations

* `chartInclOf`, `chartProjOf`, `chartCPOf` — the three maps out of the part over `U`.
* `chartTautIsoGen` — **the tautological lines agree**, at every rank.
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

/-- The inclusion of the part of `P(q)` lying over `U`. -/
def chartInclOf (q : Bundle X ι) (U : Opens (TopCat.of X)) :
    C(↥(opSpace (opensComap (projMapOf q) U)), Proj q) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- That part, identified with the projectivisation of the restriction. -/
def chartProjOf (q : Bundle X ι) (U : Opens (TopCat.of X)) :
    C(↥(opSpace (opensComap (projMapOf q) U)),
      Proj (q.restrictTo ((U : Opens (TopCat.of X)) : Set X))) :=
  ⟨(projOverHomeo q ((U : Opens (TopCat.of X)) : Set X)).symm,
    (projOverHomeo q ((U : Opens (TopCat.of X)) : Set X)).symm.continuous⟩

/-- The `ℂP^d` component of the chart, on the part over `U`. -/
def chartCPOf (q : Bundle X ι) (x₀ : X) (U : Opens (TopCat.of X))
    (hV : ((U : Opens (TopCat.of X)) : Set X) ⊆ trivSet q x₀) (d : ℕ)
    (hr : q.rank x₀ = d + 1) :
    C(↥(opSpace (opensComap (projMapOf q) U)), CP d) :=
  (_root_.GroupApproximation.CharClass.Bundle.chartCP q x₀
    ((U : Opens (TopCat.of X)) : Set X) hV d hr).comp (chartProjOf q U)

/-- **The tautological lines agree, at every rank.**  `cc-bundle`'s chart
identification, pulled back to the part over `U`. -/
def chartTautIsoGen (q : Bundle X ι) (x₀ : X) (U : Opens (TopCat.of X))
    (hV : ((U : Opens (TopCat.of X)) : Set X) ⊆ trivSet q x₀) (d : ℕ)
    (hr : q.rank x₀ = d + 1) :
    BundleIso (comap (chartInclOf q U) (tautLine q))
      (comap (chartCPOf q x₀ U hV d hr) (cpTaut d)) :=
  comapIso (chartProjOf q U)
    (_root_.GroupApproximation.CharClass.Bundle.tautLineIsoChartCP q x₀
      ((U : Opens (TopCat.of X)) : Set X) hV d hr)

end

end LH
end CharClass
end GroupApproximation
