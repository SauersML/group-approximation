import GroupApproximation.GGT.VanKampen.Estimating.OsinGreendlingerWaistV6
import GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV2Copy
import GroupApproximation.Meta.AxiomGuard

/-!
# The top of `sec:torsion-free` over the leaf residuals of the Greendlinger waist

`non_mf_groups_exist.tex`, `sec:torsion-free`: the endpoints of `TorsionFreeResidualsV6`, restated
additively over the fifteen named leaf residuals of
`GGT.VanKampen.relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV6`:
`OsinLemma94ClassEndLoopsBudgetInput`, `SameCellPocketCellFreeValueStatement`,
`SameCellPocketLoopCutStatement`, `EnclosedSubdiagramLoopCutSuccStatement`,
`ClosedWalkEnclosedSubdiagramSuccStatement`, `OsinLemma94CaseOneSpurEnclosureStatement`,
`OsinLemma94ClassCaseGapSpanStatement`, `OsinTwoGonEulerWalkSectionStatement`,
`OsinTwoGonEulerGapSectionStatement`, `NoninterleavingVertexCountStatement`,
`CellPocketWalkNoninterleavingStatement`, `CellPocketOuterPinchStepSectionStatement`,
`CellPocketWalkProperArcsSectionStatement`, `OsinSectionPocketFaceSetTwoArcSectionStatement` and
`PocketOuterPinchStepSectionStatement` (at `.{0, 0, 0}`, and `.{0}` for the vertex count).  The closed
walls are applied as in `TorsionFreeResidualsV2Copy`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreeResidualsV6

open GGT.VanKampen

section Residuals

variable (hbudget : OsinLemma94ClassEndLoopsBudgetInput.{0, 0, 0})
  (hvalue : SameCellPocketCellFreeValueStatement.{0, 0, 0})
  (hcut : SameCellPocketLoopCutStatement.{0, 0, 0})
  (hloop : EnclosedSubdiagramLoopCutSuccStatement.{0, 0, 0})
  (hsub : ClosedWalkEnclosedSubdiagramSuccStatement.{0, 0, 0})
  (hencl : OsinLemma94CaseOneSpurEnclosureStatement.{0, 0, 0})
  (hspan : OsinLemma94ClassCaseGapSpanStatement.{0, 0, 0})
  (htwowalk : OsinTwoGonEulerWalkSectionStatement.{0, 0, 0})
  (htwogap : OsinTwoGonEulerGapSectionStatement.{0, 0, 0})
  (hcount : NoninterleavingVertexCountStatement.{0})
  (hni : CellPocketWalkNoninterleavingStatement.{0, 0, 0})
  (hcellStep : CellPocketOuterPinchStepSectionStatement.{0, 0, 0})
  (hproper : CellPocketWalkProperArcsSectionStatement.{0, 0, 0})
  (hfaces : OsinSectionPocketFaceSetTwoArcSectionStatement.{0, 0, 0})
  (hstep : PocketOuterPinchStepSectionStatement.{0, 0, 0})

include hbudget hvalue hcut hloop hsub hencl hspan htwowalk htwogap hcount hni hcellStep hproper
  hfaces hstep

/-- Osin's Lemma 4.4 at least-area diagrams, from the fifteen leaf residuals of the Greendlinger waist. -/
theorem greendlinger_of_residualsV6 : RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV6 hbudget hvalue hcut hloop hsub
    hencl hspan htwowalk htwogap hcount hni hcellStep hproper hfaces hstep

/-- **`thm:torsion-free`, exactly as printed** (tex line 284), and the abstract's torsion-free
clause, over the leaf residuals. -/
theorem manuscriptTorsionFreeTheorem_of_residualsV6 : TorsionFreePrinted.PrintedTorsionFreeTheorem :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptTorsionFreeTheorem_of_hullLeaves
    (greendlinger_of_residualsV6 hbudget hvalue hcut hloop hsub hencl hspan htwowalk htwogap
      hcount hni hcellStep hproper hfaces hstep)
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed

/-- **`thm:torsion-free` in the radical form**, over the leaf residuals. -/
theorem manuscriptTorsionFreeFullMFRadical_of_residualsV6 :
    TheoremC.PrintedTorsionFreeFullMFRadical :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptTorsionFreeFullMFRadical_of_hullLeaves
    (greendlinger_of_residualsV6 hbudget hvalue hcut hloop hsub hencl hspan htwowalk htwogap
      hcount hni hcellStep hproper hfaces hstep)
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed

/-- **`thm:torsion-free` at Osin's notion**, over the leaf residuals. -/
theorem manuscriptTorsionFreeTheoremOsin_of_residualsV6 :
    TorsionFreeOsinNotion.PrintedTorsionFreeTheoremOsin :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptTorsionFreeTheoremOsin_of_hullLeaves
    (greendlinger_of_residualsV6 hbudget hvalue hcut hloop hsub hencl hspan htwowalk htwogap
      hcount hni hcellStep hproper hfaces hstep)
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed

/-- **`thm:torsion-free` at the limit-set notion**, over the leaf residuals. -/
theorem printedTorsionFreeTheoremLimitSet_of_residualsV6 :
    TorsionFreeLimitSetNotion.PrintedTorsionFreeTheoremLimitSet :=
  TorsionFreeGreendlingerLeaf.printedTorsionFreeTheoremLimitSet_of_greendlinger
    (greendlinger_of_residualsV6 hbudget hvalue hcut hloop hsub hencl hspan htwowalk htwogap
      hcount hni hcellStep hproper hfaces hstep)

/-- **`cor:regular-nonmf-algebra`, along the printed proof**, over the leaf residuals. -/
theorem manuscriptRegularNonMFAlgebra_of_residualsV6 :
    TorsionFreePrinted.PrintedRegularNonMFAlgebra :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptRegularNonMFAlgebra_of_hullLeaves
    (greendlinger_of_residualsV6 hbudget hvalue hcut hloop hsub hencl hspan htwowalk htwogap
      hcount hni hcellStep hproper hfaces hstep)
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed
    TorsionFreeSectionAssembly.simpleUniqueTraceAtHypEmbedded_closed
    TorsionFreePrinted.gerasimovaOsinTheorem11Printed

/-- **`cor:regular-nonmf-algebra` at Osin's notion**, over the leaf residuals. -/
theorem manuscriptRegularNonMFAlgebraOsin_of_residualsV6 :
    TorsionFreeOsinNotion.PrintedRegularNonMFAlgebraOsin :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptRegularNonMFAlgebraOsin_of_hullLeaves
    (greendlinger_of_residualsV6 hbudget hvalue hcut hloop hsub hencl hspan htwowalk htwogap
      hcount hni hcellStep hproper hfaces hstep)
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed
    TorsionFreeSectionAssembly.simpleUniqueTraceAtHypEmbedded_closed
    TorsionFreePrinted.gerasimovaOsinTheorem11Printed

/-- **`cor:regular-nonmf-algebra` at the limit-set notion**, over the leaf residuals. -/
theorem printedRegularNonMFAlgebraLimitSet_of_residualsV6 :
    TorsionFreeLimitSetNotion.PrintedRegularNonMFAlgebraLimitSet :=
  TorsionFreeGreendlingerLeaf.printedRegularNonMFAlgebraLimitSet_of_greendlinger
    (greendlinger_of_residualsV6 hbudget hvalue hcut hloop hsub hencl hspan htwowalk htwogap
      hcount hni hcellStep hproper hfaces hstep)

/-- **`thm:hull`, as printed** (tex line 1636), over the leaf residuals. -/
theorem printedHullTheorem_of_residualsV6 :
    TorsionFreeSectionSentences.PrintedHullSmallCancellationCurrent.{0} :=
  TorsionFreeGreendlingerLeaf.printedHullTheorem_of_greendlinger
    (greendlinger_of_residualsV6 hbudget hvalue hcut hloop hsub hencl hspan htwowalk htwogap
      hcount hni hcellStep hproper hfaces hstep)

/-- **`thm:hull` at Osin's notion**, over the leaf residuals. -/
theorem printedHullTheoremOsin_of_residualsV6 :
    TorsionFreeOsinNotion.PrintedHullSmallCancellationOsin :=
  TorsionFreeGreendlingerLeaf.printedHullTheoremOsin_of_greendlinger
    (greendlinger_of_residualsV6 hbudget hvalue hcut hloop hsub hencl hspan htwowalk htwogap
      hcount hni hcellStep hproper hfaces hstep)

/-- **`thm:hull` at the limit-set notion**, over the leaf residuals. -/
theorem printedHullTheoremLimitSet_of_residualsV6 :
    TorsionFreeLimitSetNotion.PrintedHullSmallCancellationLimitSet :=
  TorsionFreeGreendlingerLeaf.printedHullTheoremLimitSet_of_greendlinger
    (greendlinger_of_residualsV6 hbudget hvalue hcut hloop hsub hencl hspan htwowalk htwogap
      hcount hni hcellStep hproper hfaces hstep)

/-- **`thm:hull` at a torsion-free ambient group**, over the leaf residuals. -/
theorem hullSmallCancellationTorsionFreePrinted_of_residualsV6 :
    TorsionFreePrinted.HullSmallCancellationTorsionFreePrinted.{0} :=
  TorsionFreeGreendlingerLeaf.hullSmallCancellationTorsionFreePrinted_of_greendlinger
    (greendlinger_of_residualsV6 hbudget hvalue hcut hloop hsub hencl hspan htwowalk htwogap
      hcount hni hcellStep hproper hfaces hstep)

/-- **The paragraph after `thm:hull`** (tex 1644–1648), over the leaf residuals. -/
theorem printedHullProofParagraph_of_residualsV6 :
    TorsionFreeSectionSentencesFourLeaves.PrintedHullProofParagraph :=
  TorsionFreeGreendlingerLeaf.printedHullProofParagraph_of_greendlinger
    (greendlinger_of_residualsV6 hbudget hvalue hcut hloop hsub hencl hspan htwowalk htwogap
      hcount hni hcellStep hproper hfaces hstep)

/-- **`lem:saturation`, as printed**, over the leaf residuals. -/
theorem printedSaturation_of_residualsV6 : TorsionFreePrinted.PrintedSaturationNoOmega.{0} :=
  TorsionFreeGreendlingerLeaf.printedSaturation_of_greendlinger
    (greendlinger_of_residualsV6 hbudget hvalue hcut hloop hsub hencl hspan htwowalk htwogap
      hcount hni hcellStep hproper hfaces hstep)

/-- **`lem:saturation` at Osin's notion**, over the leaf residuals. -/
theorem printedSaturationOsin_of_residualsV6 : TorsionFreeOsinNotion.PrintedSaturationOsin :=
  TorsionFreeGreendlingerLeaf.printedSaturationOsin_of_greendlinger
    (greendlinger_of_residualsV6 hbudget hvalue hcut hloop hsub hencl hspan htwowalk htwogap
      hcount hni hcellStep hproper hfaces hstep)

/-- **`lem:saturation` at the limit-set notion**, over the leaf residuals. -/
theorem printedSaturationLimitSet_of_residualsV6 :
    TorsionFreeLimitSetNotion.PrintedSaturationLimitSet :=
  TorsionFreeGreendlingerLeaf.printedSaturationLimitSet_of_greendlinger
    (greendlinger_of_residualsV6 hbudget hvalue hcut hloop hsub hencl hspan htwowalk htwogap
      hcount hni hcellStep hproper hfaces hstep)

/-- **The Hull 5.7 and 5.8 pair and "Hull's theorem again applies"**, over the leaf residuals. -/
theorem printedSaturationPairAndHullAgain_of_residualsV6 :
    TorsionFreeSectionSentencesFourLeaves.PrintedSaturationPairAndHullAgain :=
  TorsionFreeGreendlingerLeaf.printedSaturationPairAndHullAgain_of_greendlinger
    (greendlinger_of_residualsV6 hbudget hvalue hcut hloop hsub hencl hspan htwowalk htwogap
      hcount hni hcellStep hproper hfaces hstep)

/-- **Applying `thm:hull` to `N₀`** in the proof of `lem:saturation`, over the leaf residuals. -/
theorem printedSaturationApplyHull_of_residualsV6 :
    TorsionFreeSectionSentencesFourLeaves.PrintedSaturationApplyHull :=
  TorsionFreeGreendlingerLeaf.printedSaturationApplyHull_of_greendlinger
    (greendlinger_of_residualsV6 hbudget hvalue hcut hloop hsub hencl hspan htwowalk htwogap
      hcount hni hcellStep hproper hfaces hstep)

/-- **Applying `lem:saturation` to `G₀` and `N`**, over the leaf residuals. -/
theorem printedTheoremApplySaturation_of_residualsV6 :
    TorsionFreeSectionSentencesFourLeaves.PrintedTheoremApplySaturation :=
  TorsionFreeGreendlingerLeaf.printedTheoremApplySaturation_of_greendlinger
    (greendlinger_of_residualsV6 hbudget hvalue hcut hloop hsub hencl hspan htwowalk htwogap
      hcount hni hcellStep hproper hfaces hstep)

/-- **The Fournier-Facio paragraph** (tex 1675–1685), over the leaf residuals. -/
theorem fournierFacioParagraph_of_residualsV6 : TorsionFreePrinted.FournierFacioParagraph :=
  TorsionFreeGreendlingerLeaf.fournierFacioParagraph_of_greendlinger
    (greendlinger_of_residualsV6 hbudget hvalue hcut hloop hsub hencl hspan htwowalk htwogap
      hcount hni hcellStep hproper hfaces hstep)

/-- **`G₀` as a Hull Corollary 7.4 common quotient**, over the leaf residuals. -/
theorem hullCommonQuotientPrinted_of_residualsV6 : TorsionFreePrinted.HullCommonQuotientPrinted :=
  TorsionFreeGreendlingerSentences.manuscriptSentence_hullCommonQuotient_of_greendlinger
    (greendlinger_of_residualsV6 hbudget hvalue hcut hloop hsub hencl hspan htwowalk htwogap
      hcount hni hcellStep hproper hfaces hstep)

/-- **Hull's Corollary 7.4 at the printed generality**, over the leaf residuals. -/
theorem printedHullCorollary74_of_residualsV6 : HullCorollary74.PrintedHullCorollary74 :=
  HullCorollary74.printedHullCorollary74_of_greendlinger
    (greendlinger_of_residualsV6 hbudget hvalue hcut hloop hsub hencl hspan htwowalk htwogap
      hcount hni hcellStep hproper hfaces hstep)

end Residuals

end TorsionFreeResidualsV6
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV6.greendlinger_of_residualsV6
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV6.manuscriptTorsionFreeTheorem_of_residualsV6
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV6.manuscriptTorsionFreeFullMFRadical_of_residualsV6
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV6.manuscriptTorsionFreeTheoremOsin_of_residualsV6
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV6.printedTorsionFreeTheoremLimitSet_of_residualsV6
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV6.manuscriptRegularNonMFAlgebra_of_residualsV6
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV6.manuscriptRegularNonMFAlgebraOsin_of_residualsV6
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV6.printedRegularNonMFAlgebraLimitSet_of_residualsV6
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV6.printedHullTheorem_of_residualsV6
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV6.printedHullTheoremOsin_of_residualsV6
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV6.printedHullTheoremLimitSet_of_residualsV6
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV6.hullSmallCancellationTorsionFreePrinted_of_residualsV6
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV6.printedHullProofParagraph_of_residualsV6
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV6.printedSaturation_of_residualsV6
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV6.printedSaturationOsin_of_residualsV6
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV6.printedSaturationLimitSet_of_residualsV6
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV6.printedSaturationPairAndHullAgain_of_residualsV6
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV6.printedSaturationApplyHull_of_residualsV6
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV6.printedTheoremApplySaturation_of_residualsV6
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV6.fournierFacioParagraph_of_residualsV6
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV6.hullCommonQuotientPrinted_of_residualsV6
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV6.printedHullCorollary74_of_residualsV6
