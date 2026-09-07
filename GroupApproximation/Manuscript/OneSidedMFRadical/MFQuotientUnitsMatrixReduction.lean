import GroupApproximation.Manuscript.OneSidedMFRadical.MFQuotientUnitsKOne
import GroupApproximation.Algebra.PurelyInfiniteSimpleMatrix
import GroupApproximation.Manuscript.OneSidedMFRadical.MFQuotientMatrices
import GroupApproximation.Manuscript.OneSidedMFRadical.MFQuotientUnitsStepOne
import GroupApproximation.Manuscript.OneSidedMFRadical.MFQuotientUnitsPeirce

/-!
# Matrix reduction and the supported-unit step are closed

`non_mf_groups_exist.tex`, inside the proof of `thm:mf-quotient-units`:

> The ring `M_n(R)` is again countable, purely infinite, and
> simple~\cite[Corollary~1.7]{AGP} …

`MFQuotientUnits.lean` quoted that sentence as the hypothesis
`AGPMatrixReduction`.  `Algebra/PurelyInfiniteSimpleMatrix.lean` proves it, so
this module discharges that hypothesis wherever the printed theorem took it.
It also exports the supported-unit proof and the abstract abelianization
construction. The new all-rank group-theoretic entry point therefore has only
the Menal--Moncasi reduction left as input; the earlier three-input entry
points remain available to existing callers.

Of the sentence's three adjectives, all three are now the tree's own:

* *countable* — `Algebra/CountableMatrixUnits.lean`;
* *simple* — Mathlib's `IsSimpleRing.matrix`;
* *purely infinite* — `isPurelyInfiniteSimpleRing_matrix`.

## What remains cited

`MFQuotientUnitsStepOne` now proves `AGPStepOne`. The abstract `AGPUnitK1`
package is supplied below by abelianization: its definition asks only for an
abstract countable abelian quotient with commutator kernel, so it does not
assert anything about the constructed algebraic K₁. Consequently
`printedMFQuotientUnits_of_menalMoncasi` has just the Menal--Moncasi reduction
left as input. `MFQuotientMatrices` already proves the group-theoretic
classification at every rank at least two with no such input.

The canonical `AGPUnitKappa` and general `MoritaKOne` remain separate
obligations. `AlgebraicK.moritaKOne_of_selfSimilar` closes Morita invariance
for the self-similar rings the manuscript uses.
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

/-- The abstract quotient package is abelianization. This does not identify
that quotient with the separately constructed canonical algebraic K₁. -/
theorem abstractUnitAbelianization : AGPUnitK1 := by
  intro R _ _ _
  haveI : Countable Rˣ := Function.Injective.countable
    (f := (Units.val : Rˣ → R)) (fun _ _ h ↦ Units.ext h)
  haveI : Countable (Abelianization Rˣ) :=
    (QuotientGroup.mk'_surjective (commutator Rˣ)).countable
  exact ⟨Abelianization Rˣ, inferInstance, inferInstance, Abelianization.of,
    QuotientGroup.mk'_surjective (commutator Rˣ), Abelianization.ker_of Rˣ⟩

/-- The all-rank group-theoretic classification now requires only the step
that moves arbitrary units to supported form. Rank one is the remaining case. -/
theorem printedMFQuotientUnits_of_menalMoncasi
    (hMM : AGPMenalMoncasiReduction) : PrintedMFQuotientUnits :=
  printedMFQuotientUnits_of_agpThree abstractUnitAbelianization hMM agpStepOne

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
#audit_closed_axioms GroupApproximation.MFQuotientUnits.abstractUnitAbelianization
#audit_axioms GroupApproximation.MFQuotientUnits.printedMFQuotientUnits_of_menalMoncasi
#audit_axioms GroupApproximation.MFQuotientUnits.printedMFQuotientUnits_of_agpThree
#audit_axioms
  GroupApproximation.MFQuotientUnitsKOne.printedMFQuotientUnitsKOneAllRanks_of_agpThree
#audit_axioms
  GroupApproximation.MFQuotientUnitsKOne.printedMFQuotientUnitsKOneAtBaseRing_of_agpThree
