import GroupApproximation.Dynamics.TransientCells
import GroupApproximation.Dynamics.TransientIdealLocallyMatricial
import GroupApproximation.Dynamics.InvolutionLocalizationRingClosed
import GroupApproximation.Dynamics.InvolutionLocalizationClosed
import GroupApproximation.Meta.AxiomGuard

/-!
# The cells, local matriciality of the transient ideal, and lem:involution-localization: closed

`non_mf_groups_exist.tex`, `\label{lem:transient-matrices}` (tex 1476, "The ideal $I$ is locally
matricial"; proof tex 1489–1513) and `\label{lem:involution-localization}` (tex 1663–1694).

The chain:

* `exists_transientCells` (TransientCells) proves the cells over the defect cover of
  lem:chain-core-models, which is closed (`chainCoreDefectCoverStatement_holds`,
  InvolutionLocalizationRingClosed), so `transientCellsStatement_holds : TransientCellsStatement`;
* ms-units' tower family, expansion and assembly (TransientIdealLocallyMatricial) give local
  matriciality over every finite field and over `F₂` from `TransientCellsStatement`, and with it the
  finite matrix argument of thm:core-mf-radical and local finiteness of `K_1(I)`;
* `printedInvolutionLocalization_of_matricial` (InvolutionLocalizationClosed) then gives the printed
  lemma with no binder.

Closed endpoints:

* `transientCellsStatement_holds`;
* `transientIdealLocallyMatricialStatement_holds` (lem:transient-matrices, locally matricial clause);
* `transientIdealLocallyMatricialFTwoStatement_holds`;
* `coreKernelElementaryStatement_holds`, `unitKernelLocallyFiniteStatement_holds`;
* `printedInvolutionLocalization_closed` (lem:involution-localization).
-/

namespace GroupApproximation

namespace ClopenCrossedProduct

open ChainCore

/-- The cells of lem:transient-matrices over the defect cover. -/
theorem transientCellsStatement_of_cover (hcover : ChainCoreDefectCoverStatement) :
    TransientCellsStatement :=
  fun X _ _ _ T k _ F hF => exists_transientCells hcover X T k F hF

/-- **The cells of lem:transient-matrices** (tex 1492–1511), closed. -/
theorem transientCellsStatement_holds : TransientCellsStatement :=
  transientCellsStatement_of_cover chainCoreDefectCoverStatement_holds

/-- **lem:transient-matrices, locally matricial clause** (tex 1476), closed. -/
theorem transientIdealLocallyMatricialStatement_holds : TransientIdealLocallyMatricialStatement :=
  transientIdealLocallyMatricial_of_cells transientCellsStatement_holds

/-- Local matriciality of the transient ideal over `F₂`, in chain-radical's interface shape, closed. -/
theorem transientIdealLocallyMatricialFTwoStatement_holds :
    TransientIdealLocallyMatricialFTwoStatement :=
  transientIdealLocallyMatricialFTwo_of_cells transientCellsStatement_holds

/-- The finite matrix argument of thm:core-mf-radical (tex 1691–1693), closed. -/
theorem coreKernelElementaryStatement_holds : CoreKernelElementaryStatement :=
  coreKernelElementaryStatement_of_cells transientCellsStatement_holds

/-- Local finiteness of `K_1(I)` (tex 1693), closed. -/
theorem unitKernelLocallyFiniteStatement_holds :
    DynamicRankBudget.UnitKernelLocallyFiniteStatement :=
  unitKernelLocallyFinite_of_cells transientCellsStatement_holds

/-- **lem:involution-localization** (tex 1663–1670), as printed, closed. -/
theorem printedInvolutionLocalization_closed : PrintedInvolutionLocalization :=
  printedInvolutionLocalization_of_matricial transientIdealLocallyMatricialFTwoStatement_holds

end ClopenCrossedProduct

end GroupApproximation

#audit_axioms GroupApproximation.ClopenCrossedProduct.transientCellsStatement_of_cover
#audit_closed_axioms GroupApproximation.ClopenCrossedProduct.transientCellsStatement_holds
#audit_closed_axioms GroupApproximation.ClopenCrossedProduct.transientIdealLocallyMatricialStatement_holds
#audit_closed_axioms GroupApproximation.ClopenCrossedProduct.transientIdealLocallyMatricialFTwoStatement_holds
#audit_closed_axioms GroupApproximation.ClopenCrossedProduct.coreKernelElementaryStatement_holds
#audit_closed_axioms GroupApproximation.ClopenCrossedProduct.unitKernelLocallyFiniteStatement_holds
#audit_closed_axioms GroupApproximation.ClopenCrossedProduct.printedInvolutionLocalization_closed
