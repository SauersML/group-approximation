import GroupApproximation.Manuscript.NonMFSentences.DynamicRankBudgetAssembly
import GroupApproximation.Manuscript.NonMFSentences.CoreModelsLEFClosed
import GroupApproximation.Manuscript.ChainCore.BilateralThreeCoreModels
import GroupApproximation.Manuscript.NonMFSentences.CoreRingReflection
import GroupApproximation.Manuscript.ChainCore.CoreMFRadical
import GroupApproximation.Dynamics.TwoEndedUnitsLEF
import GroupApproximation.Meta.AxiomGuard

/-!
# `sec:chain-core`: the closed endpoints

`non_mf_groups_exist.tex`, Section `sec:chain-core` (tex 1338–1807) and the Introduction (tex 249–259).

Once "`R_Y` is LEF" (`lem:chain-core-models`, tex 1372) is closed (`coreModelsLEFStatement`, ms-core-2),
every result of the section that was proved over it becomes closed.  This module records each of them
as a closed endpoint:

* `printedBilateralThree_closed` (`prop:bilateral-three`, tex 1541–1547),
  `printedIntroDirectlyFiniteIffGLThreeMF_closed` (tex 253–255), `bilateralThreeTransferStatement_holds`
  (tex 1763–1765), from ct-bilateral-mf's `_of_coreModels`;
* `printedCoreRingReflection_closed` (`thm:core-ring-reflection`, tex 1516–1523),
  `coreRingReflectionStatement_holds`, from ct-return-tower's `_of_coreModels`;
* `printedCoreMFRadical_closed` (`thm:core-mf-radical`, tex 1609–1622), `coreMFRadicalKillStatement_holds`,
  from ms-core-4's `_of_coreModels`;
* `printedDynamicRankBudget_closed` (`cor:dynamic-rank-budget`, tex 1696–1705),
  `printedIntroductionAperiodicSentence_closed` (tex 257–259), from
  `printedDynamicRankBudget_of_openPieces`;
* `printedTwoEndedUnitsLEFGLThreeNotMF_closed` (tex 1769–1792), from ct-two-ended's
  `_of_bilateralThree`.
-/

namespace GroupApproximation.ChainCore.ChainCoreClosures

universe w

/-- **`prop:bilateral-three`, closed** (tex 1541–1547): for every finite field `k` and `n ≥ 3`,
`GL_n(R_X)` is MF iff LEF iff `R_X` is directly finite, and every homomorphism to an MF group kills
`EL_n(R_X, I)`. -/
theorem printedBilateralThree_closed :
    GroupApproximation.Manuscript.ChainCore.BilateralThree.PrintedBilateralThree :=
  GroupApproximation.Manuscript.ChainCore.BilateralThree.printedBilateralThree_of_coreModels
    GroupApproximation.ChainCore.coreModelsLEFStatement

/-- **The Introduction, closed** (tex 253–255): "$R_X$ is directly finite exactly when $\GL_3(R_X)$ is
MF". -/
theorem printedIntroDirectlyFiniteIffGLThreeMF_closed :
    GroupApproximation.Manuscript.ChainCore.BilateralThree.PrintedIntroDirectlyFiniteIffGLThreeMF :=
  GroupApproximation.Manuscript.ChainCore.BilateralThree.printedIntroDirectlyFiniteIffGLThreeMF_of_coreModels
    GroupApproximation.ChainCore.coreModelsLEFStatement

/-- **The general linear transfer of `cor:dynamic-rank-budget`, closed** (tex 1763–1765). -/
theorem bilateralThreeTransferStatement_holds :
    GroupApproximation.ChainCore.DynamicRankBudget.BilateralThreeTransferStatement :=
  GroupApproximation.Manuscript.ChainCore.BilateralThree.bilateralThreeTransferStatement_of_coreModels
    GroupApproximation.ChainCore.coreModelsLEFStatement

/-- **The last sentence of `thm:core-ring-reflection`, closed** (tex 1521–1523). -/
theorem coreRingReflectionStatement_holds :
    GroupApproximation.ChainCore.DynamicRankBudget.CoreRingReflectionStatement :=
  GroupApproximation.ChainCore.CoreRingReflection.coreRingReflectionStatement_of_coreModels
    GroupApproximation.ChainCore.coreModelsLEFStatement

/-- **`thm:core-ring-reflection`, closed** (tex 1516–1523). -/
theorem printedCoreRingReflection_closed :
    GroupApproximation.ChainCore.CoreRingReflection.PrintedCoreRingReflection.{w} :=
  GroupApproximation.ChainCore.CoreRingReflection.printedCoreRingReflection_of_coreModels
    GroupApproximation.ChainCore.coreModelsLEFStatement

/-- **The kill half of `thm:core-mf-radical`, closed** (tex 1614–1618, 1643–1646). -/
theorem coreMFRadicalKillStatement_holds :
    GroupApproximation.ChainCore.DynamicRankBudget.CoreMFRadicalKillStatement :=
  GroupApproximation.ChainCore.CoreMFRadical.coreMFRadicalKillStatement_of_coreModels
    GroupApproximation.ChainCore.coreModelsLEFStatement

/-- **`thm:core-mf-radical`, closed** (tex 1609–1622). -/
theorem printedCoreMFRadical_closed : GroupApproximation.ChainCore.CoreMFRadical.PrintedCoreMFRadical :=
  GroupApproximation.ChainCore.CoreMFRadical.printedCoreMFRadical_of_coreModels
    GroupApproximation.ChainCore.coreModelsLEFStatement

/-- **`cor:dynamic-rank-budget`, closed** (tex 1696–1705). -/
theorem printedDynamicRankBudget_closed :
    GroupApproximation.ChainCore.DynamicRankBudget.PrintedDynamicRankBudget :=
  GroupApproximation.ChainCore.DynamicRankBudget.printedDynamicRankBudget_of_openPieces
    coreRingReflectionStatement_holds GroupApproximation.ChainCore.coreModelsLEFStatement
    coreMFRadicalKillStatement_holds

/-- **The Introduction's aperiodic sentence, closed** (tex 257–259). -/
theorem printedIntroductionAperiodicSentence_closed :
    GroupApproximation.ChainCore.DynamicRankBudget.PrintedIntroductionAperiodicSentence :=
  GroupApproximation.ChainCore.DynamicRankBudget.printedIntroductionAperiodicSentence_of_openPieces
    coreRingReflectionStatement_holds GroupApproximation.ChainCore.coreModelsLEFStatement
    coreMFRadicalKillStatement_holds

/-- **The two-ended shift, closed** (tex 1791–1792): "Thus $R_X^\times$ is LEF although $\GL_3(R_X)$ is
not MF". -/
theorem printedTwoEndedUnitsLEFGLThreeNotMF_closed :
    GroupApproximation.TwoEndedShift.PrintedTwoEndedUnitsLEFGLThreeNotMF :=
  GroupApproximation.TwoEndedShift.printedTwoEndedUnitsLEFGLThreeNotMF_of_bilateralThree
    printedBilateralThree_closed

end GroupApproximation.ChainCore.ChainCoreClosures

/-! ### Audit -/

#audit_closed_axioms GroupApproximation.ChainCore.ChainCoreClosures.printedBilateralThree_closed
#audit_closed_axioms GroupApproximation.ChainCore.ChainCoreClosures.printedIntroDirectlyFiniteIffGLThreeMF_closed
#audit_closed_axioms GroupApproximation.ChainCore.ChainCoreClosures.bilateralThreeTransferStatement_holds
#audit_closed_axioms GroupApproximation.ChainCore.ChainCoreClosures.coreRingReflectionStatement_holds
#audit_closed_axioms GroupApproximation.ChainCore.ChainCoreClosures.printedCoreRingReflection_closed
#audit_closed_axioms GroupApproximation.ChainCore.ChainCoreClosures.coreMFRadicalKillStatement_holds
#audit_closed_axioms GroupApproximation.ChainCore.ChainCoreClosures.printedCoreMFRadical_closed
#audit_closed_axioms GroupApproximation.ChainCore.ChainCoreClosures.printedDynamicRankBudget_closed
#audit_closed_axioms GroupApproximation.ChainCore.ChainCoreClosures.printedIntroductionAperiodicSentence_closed
#audit_closed_axioms GroupApproximation.ChainCore.ChainCoreClosures.printedTwoEndedUnitsLEFGLThreeNotMF_closed
