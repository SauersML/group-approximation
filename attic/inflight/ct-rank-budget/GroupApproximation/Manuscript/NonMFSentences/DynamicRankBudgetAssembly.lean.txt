import GroupApproximation.Manuscript.NonMFSentences.DynamicRankBudgetTorsionTransfer
import GroupApproximation.Manuscript.NonMFSentences.DynamicRankBudgetReturnTransientIdeal
import GroupApproximation.Manuscript.ChainCore.ClopenCrossedProductCountableConsumers
import GroupApproximation.Manuscript.ChainCore.BilateralThreeCoreModels
import GroupApproximation.Dynamics.TransientCellsClosed
import GroupApproximation.Dynamics.ReturnRingCrossedProduct
import GroupApproximation.Meta.AxiomGuard

/-!
# `cor:dynamic-rank-budget`: the assembly over the open inputs

`non_mf_groups_exist.tex`, Corollary `cor:dynamic-rank-budget` (tex 1696–1767), and the Introduction's
aperiodic sentence (tex 257–259).

`printedDynamicRankBudget_of_openPieces` composes the printed proof with every producer on main:

* countability of `R_X` (`countableCrossedProductStatement`);
* the return ring `P_C ≅ LC(C,k) ⋊_{S_C} ℤ` (`returnRingCrossedProductStatement_holds`);
* `lem:involution-localization`, closed (`printedInvolutionLocalization_closed`), its `F₂` clause;
* `K_n(I) ⊆ EL_n(R_X)` and local finiteness of `K_1(I)` over `F₂` (`coreKernelElementaryStatement_holds`,
  `unitKernelLocallyFiniteStatement_holds`);
* `θ⁻¹(p_C I p_C) ⊆ I_C` (`returnTransientIdealStatement_holds`);
* the embeddings, placement and bridge (`returnEmbeddingStatement_of_pieces`);
* the elementary transfer from `prop:torsion-defect-ring`
  (`torsionDefectTransferStatement_of_countable`, inside `printedDynamicRankBudget_of_residuals`);
* the general linear transfer from `prop:bilateral-three`
  (`bilateralThreeTransferStatement_of_nonzeroDefect`), with "some defect is nonzero" from the core
  models (`clopenCrossedProductNonzeroDefectStatement_of_coreModels`).

The remaining open inputs, with their owners:

| Prop | printed content | owner |
|---|---|---|
| `CoreRingReflectionStatement` | thm:core-ring-reflection, last sentence | chain-reflection, ct-return-tower |
| `CoreModelsLEFStatement` | lem:chain-core-models, "$R_Y$ is LEF" | chain-itinerary |
| `CoreMFRadicalKillStatement` | thm:core-mf-radical, the kill half and local finiteness | chain-radical, ms-core-4, ms-core-5 |
-/

namespace GroupApproximation.ChainCore.DynamicRankBudget

open GroupApproximation.Manuscript.ChainCore

/-- **The return embeddings of `cor:dynamic-rank-budget`, closed** (tex 1707–1757): the section and
tower, the four embeddings over every finite field, and over `F₂` the conjugation of every core
kernel element into the image of the return core kernel. -/
theorem returnEmbeddingStatement_holds : ReturnEmbeddingStatement :=
  returnEmbeddingStatement_of_pieces returnRingCrossedProductStatement_holds
    (And.right ClopenCrossedProduct.printedInvolutionLocalization_closed)
    ClopenCrossedProduct.coreKernelElementaryStatement_holds
    returnTransientIdealStatement_holds

/-- **The elementary transfer of `cor:dynamic-rank-budget`, closed** (tex 1765): over a finite field,
if `R_X` is not directly finite then `EL_n(R_X)`, `n ≥ 4`, has a nontrivial element in its MF
radical. -/
theorem torsionDefectTransferStatement_holds : TorsionDefectTransferStatement :=
  torsionDefectTransferStatement_of_countable GroupApproximation.countableCrossedProductStatement

/-- **`cor:dynamic-rank-budget` over its open inputs** (tex 1696–1767). -/
theorem printedDynamicRankBudget_of_openPieces (hRefl : CoreRingReflectionStatement)
    (hModels : CoreModelsLEFStatement) (hRad : CoreMFRadicalKillStatement) :
    PrintedDynamicRankBudget :=
  printedDynamicRankBudget_of_pieces hRefl hModels GroupApproximation.countableCrossedProductStatement
    hRad
    (BilateralThree.bilateralThreeTransferStatement_of_nonzeroDefect
      (BilateralThree.clopenCrossedProductNonzeroDefectStatement_of_coreModels hModels))
    torsionDefectTransferStatement_holds
    ClopenCrossedProduct.unitKernelLocallyFiniteStatement_holds
    returnEmbeddingStatement_holds

/-- **The Introduction's aperiodic sentence over the same open inputs** (tex 257–259). -/
theorem printedIntroductionAperiodicSentence_of_openPieces (hRefl : CoreRingReflectionStatement)
    (hModels : CoreModelsLEFStatement) (hRad : CoreMFRadicalKillStatement) :
    PrintedIntroductionAperiodicSentence :=
  printedIntroductionAperiodicSentence_of_budget
    (printedDynamicRankBudget_of_openPieces hRefl hModels hRad) hModels

end GroupApproximation.ChainCore.DynamicRankBudget

/-! ### Audit -/

#audit_closed_axioms GroupApproximation.ChainCore.DynamicRankBudget.returnEmbeddingStatement_holds
#audit_closed_axioms GroupApproximation.ChainCore.DynamicRankBudget.torsionDefectTransferStatement_holds
#audit_axioms GroupApproximation.ChainCore.DynamicRankBudget.printedDynamicRankBudget_of_openPieces
#audit_axioms GroupApproximation.ChainCore.DynamicRankBudget.printedIntroductionAperiodicSentence_of_openPieces
