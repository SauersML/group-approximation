import GroupApproximation.Manuscript.OneSidedMFRadical.MFQuotientUnitsKOne
import GroupApproximation.Algebra.PurelyInfiniteSimpleMatrix

/-!
# `AGPMatrixReduction` is closed

`non_mf_groups_exist.tex`, inside the proof of `thm:mf-quotient-units`:

> The ring `M_n(R)` is again countable, purely infinite, and
> simple~\cite[Corollary~1.7]{AGP} …

`MFQuotientUnits.lean` quoted that sentence as the hypothesis
`AGPMatrixReduction`.  `Algebra/PurelyInfiniteSimpleMatrix.lean` proves it, so
this module discharges the hypothesis wherever the printed theorem took it, and
`thm:mf-quotient-units` now rests on **three** Ara--Goodearl--Pardo propositions
rather than four.

Of the sentence's three adjectives, all three are now the tree's own:

* *countable* — `Algebra/CountableMatrixUnits.lean`;
* *simple* — Mathlib's `IsSimpleRing.matrix`;
* *purely infinite* — `isPurelyInfiniteSimpleRing_matrix`.

## What remains cited

`AGPUnitK1` / `AGPUnitKappa` (AGP Theorem 2.4), `AGPMenalMoncasiReduction`
(Theorem 2.4 Step 2 with Menal--Moncasi) and `AGPStepOne` (Theorem 2.4 Step 1).
Those are the substance of AGP §2 and are not touched here.  `MoritaKOne` also
remains open in general; `AlgebraicK.moritaKOne_of_selfSimilar` closes it for the
self-similar rings the manuscript actually uses.
-/

namespace GroupApproximation

namespace MFQuotientUnits

/-- **Ara--Goodearl--Pardo, Corollary 1.7**, as the manuscript quotes it: matrix
rings over a countable purely infinite simple ring are again purely infinite
simple.  Countability of `M_n(R)` is automatic and is not part of the
statement. -/
theorem agpMatrixReduction : AGPMatrixReduction := by
  intro R _ _ hR n hn
  exact isPurelyInfiniteSimpleRing_matrix hR n hn

/-- **`thm:mf-quotient-units` from the three remaining Ara--Goodearl--Pardo
inputs.**  The matrix-reduction hypothesis is discharged. -/
theorem printedMFQuotientUnits_of_agpThree
    (hK1 : AGPUnitK1) (hMM : AGPMenalMoncasiReduction) (hS1 : AGPStepOne) :
    PrintedMFQuotientUnits :=
  printedMFQuotientUnits_of_agpOnly agpMatrixReduction hK1 hMM hS1

end MFQuotientUnits

namespace MFQuotientUnitsKOne

open MFQuotientUnits

/-- **`thm:mf-quotient-units` at every rank, with the quotient named
`K_1(M_n(R))`, from three inputs.** -/
theorem printedMFQuotientUnitsKOneAllRanks_of_agpThree
    (hK : AGPUnitKappa) (hMM : AGPMenalMoncasiReduction) (hS1 : AGPStepOne) :
    PrintedMFQuotientUnitsKOneAllRanks :=
  printedMFQuotientUnitsKOneAllRanks_of_agp agpMatrixReduction hK hMM hS1

/-- **The printed conclusion at `K_1(R)`**, from the three Ara--Goodearl--Pardo
inputs plus the printed Morita step. -/
theorem printedMFQuotientUnitsKOneAtBaseRing_of_agpThree
    (hK : AGPUnitKappa) (hMM : AGPMenalMoncasiReduction) (hS1 : AGPStepOne)
    (hMor : MoritaKOne) :
    PrintedMFQuotientUnitsKOneAtBaseRing :=
  printedMFQuotientUnitsKOneAtBaseRing_of_agp agpMatrixReduction hK hMM hS1 hMor

end MFQuotientUnitsKOne

end GroupApproximation

/-! ### Axiom audit -/

#audit_closed_axioms GroupApproximation.MFQuotientUnits.agpMatrixReduction
#audit_axioms GroupApproximation.MFQuotientUnits.printedMFQuotientUnits_of_agpThree
#audit_axioms
  GroupApproximation.MFQuotientUnitsKOne.printedMFQuotientUnitsKOneAllRanks_of_agpThree
#audit_axioms
  GroupApproximation.MFQuotientUnitsKOne.printedMFQuotientUnitsKOneAtBaseRing_of_agpThree
