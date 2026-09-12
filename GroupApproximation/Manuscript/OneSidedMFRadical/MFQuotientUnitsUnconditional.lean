import GroupApproximation.Manuscript.OneSidedMFRadical.MFQuotientUnits
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:mf-quotient-units` from the Ara--Goodearl--Pardo inputs alone

`Manuscript/OneSidedMFRadical/MFQuotientUnits.lean` proves the printed theorem
from five hypotheses: the four propositions quoted from Ara--Goodearl--Pardo,
and `thm:full-defect-ring` in its rank-two form,

`FullDefectRankTwo.PrintedFullComplementaryIdempotentsRankTwo`.

That fifth hypothesis is no longer open.  `PropertyT/IntegralColumnPlaneClosure.lean`
closed the coefficient-general Ershov--Jaikin-Zapirain input unconditionally, and
`FullDefectRingEJZUnconditional.lean` spends it, so

`manuscriptFullComplementaryIdempotentsRankTwoAllCharacteristics`

is a theorem in every characteristic with nothing assumed.  This module
discharges it, leaving exactly the four literature propositions the printed
proof cites.

Nothing is reproved here.  The point is that the hypothesis list of the printed
theorem should name the literature it actually depends on and nothing else: a
reader auditing `thm:mf-quotient-units` should not have to check whether the
fifth binder is open, and the census should not register a conditional row for a
proposition the tree closes.
-/

namespace GroupApproximation
namespace MFQuotientUnits

/-- **`thm:mf-quotient-units` from the four Ara--Goodearl--Pardo inputs.**

Identical in content to `printedMFQuotientUnits_of_agp`, with
`thm:full-defect-ring`'s rank-two form discharged rather than assumed.  The
remaining hypotheses are exactly the printed citations:

* `AGPMatrixReduction` --- Ara--Goodearl--Pardo, Corollary 1.7;
* `AGPUnitK1` --- Ara--Goodearl--Pardo, Theorem 2.4;
* `AGPMenalMoncasiReduction` --- Theorem 2.4 Step 2 with Menal--Moncasi;
* `AGPStepOne` --- Theorem 2.4 Step 1.

The printed "a countable abelian group is MF" is not among them: it is proved by
`countableAbelianMF`. -/
theorem printedMFQuotientUnits_of_agpOnly
    (hMat : AGPMatrixReduction) (hK1 : AGPUnitK1)
    (hMM : AGPMenalMoncasiReduction) (hS1 : AGPStepOne) :
    PrintedMFQuotientUnits :=
  printedMFQuotientUnits_of_agp
    GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional.manuscriptFullComplementaryIdempotentsRankTwoAllCharacteristics
    hMat hK1 hMM hS1

end MFQuotientUnits
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.MFQuotientUnits.printedMFQuotientUnits_of_agpOnly
