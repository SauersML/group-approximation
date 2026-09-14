import GroupApproximation.GGT.VanKampen.Estimating.OsinGreendlingerWaistV5
import GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV2Copy
import GroupApproximation.Meta.AxiomGuard

/-!
# The top of `sec:torsion-free` over the residuals of the live waist

`non_mf_groups_exist.tex`, `sec:torsion-free`: the endpoints of `TorsionFreeResidualsV2Copy`, restated
additively over the ten named residuals of
`GGT.VanKampen.relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV5`:
`OsinLemma94ClassEndLoopsInput`, `OsinLemma94SameCellPocketInput`, `OsinLemma94CaseOneRCellStatement`,
`OsinLemma94ClassCaseGapSpanStatement`, `OsinTwoGonHoldsSectionStatement`, `CellPocketWalkEulerStatement`,
`CellPocketPinchSectionStatement`, `CellPocketWalkProperArcsSectionStatement`,
`OsinSectionPocketFaceSetTwoArcSectionStatement` and `PocketPinchLabelledSectionTwoArcStatement` (all at
`.{0, 0, 0}`).  None of them is a refuted statement: the positive cell pinch `CellPocketPinchPosStatement`,
which the V2Copy, V4 and V4 Euler forms bind, is refuted by `OsinPocketCellPinchRose.cellPocketPinchRoseRefutation`.
The closed walls are applied as in `TorsionFreeResidualsV2Copy`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreeResidualsV5

open GGT.VanKampen

section Residuals

variable (hloops : OsinLemma94ClassEndLoopsInput.{0, 0, 0})
  (hpocket : OsinLemma94SameCellPocketInput.{0, 0, 0})
  (hrcell : OsinLemma94CaseOneRCellStatement.{0, 0, 0})
  (hspan : OsinLemma94ClassCaseGapSpanStatement.{0, 0, 0})
  (htwogon : OsinTwoGonHoldsSectionStatement.{0, 0, 0})
  (heuler : CellPocketWalkEulerStatement.{0, 0, 0})
  (hcellPinch : CellPocketPinchSectionStatement.{0, 0, 0})
  (hproper : CellPocketWalkProperArcsSectionStatement.{0, 0, 0})
  (hfaces : OsinSectionPocketFaceSetTwoArcSectionStatement.{0, 0, 0})
  (hpinch : PocketPinchLabelledSectionTwoArcStatement.{0, 0, 0})

include hloops hpocket hrcell hspan htwogon heuler hcellPinch hproper hfaces hpinch

/-- Osin's Lemma 4.4 at least-area diagrams, from the ten residuals of the live waist. -/
theorem greendlinger_of_residualsV5 : RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV5 hloops hpocket hrcell hspan
    htwogon heuler hcellPinch hproper hfaces hpinch

/-- **`thm:torsion-free`, exactly as printed** (tex line 284), and the abstract's torsion-free
clause, over the live residuals. -/
theorem manuscriptTorsionFreeTheorem_of_residualsV5 : TorsionFreePrinted.PrintedTorsionFreeTheorem :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptTorsionFreeTheorem_of_hullLeaves
    (greendlinger_of_residualsV5 hloops hpocket hrcell hspan htwogon heuler hcellPinch hproper
      hfaces hpinch)
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed

/-- **`thm:torsion-free` in the radical form**, over the live residuals. -/
theorem manuscriptTorsionFreeFullMFRadical_of_residualsV5 :
    TheoremC.PrintedTorsionFreeFullMFRadical :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptTorsionFreeFullMFRadical_of_hullLeaves
    (greendlinger_of_residualsV5 hloops hpocket hrcell hspan htwogon heuler hcellPinch hproper
      hfaces hpinch)
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed

/-- **`thm:torsion-free` at Osin's notion**, over the live residuals. -/
theorem manuscriptTorsionFreeTheoremOsin_of_residualsV5 :
    TorsionFreeOsinNotion.PrintedTorsionFreeTheoremOsin :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptTorsionFreeTheoremOsin_of_hullLeaves
    (greendlinger_of_residualsV5 hloops hpocket hrcell hspan htwogon heuler hcellPinch hproper
      hfaces hpinch)
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed

/-- **`thm:torsion-free` at the limit-set notion**, over the live residuals. -/
theorem printedTorsionFreeTheoremLimitSet_of_residualsV5 :
    TorsionFreeLimitSetNotion.PrintedTorsionFreeTheoremLimitSet :=
  TorsionFreeGreendlingerLeaf.printedTorsionFreeTheoremLimitSet_of_greendlinger
    (greendlinger_of_residualsV5 hloops hpocket hrcell hspan htwogon heuler hcellPinch hproper
      hfaces hpinch)

/-- **`cor:regular-nonmf-algebra`, along the printed proof**, over the live residuals. -/
theorem manuscriptRegularNonMFAlgebra_of_residualsV5 :
    TorsionFreePrinted.PrintedRegularNonMFAlgebra :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptRegularNonMFAlgebra_of_hullLeaves
    (greendlinger_of_residualsV5 hloops hpocket hrcell hspan htwogon heuler hcellPinch hproper
      hfaces hpinch)
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed
    TorsionFreeSectionAssembly.simpleUniqueTraceAtHypEmbedded_closed
    TorsionFreePrinted.gerasimovaOsinTheorem11Printed

/-- **`cor:regular-nonmf-algebra` at Osin's notion**, over the live residuals. -/
theorem manuscriptRegularNonMFAlgebraOsin_of_residualsV5 :
    TorsionFreeOsinNotion.PrintedRegularNonMFAlgebraOsin :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptRegularNonMFAlgebraOsin_of_hullLeaves
    (greendlinger_of_residualsV5 hloops hpocket hrcell hspan htwogon heuler hcellPinch hproper
      hfaces hpinch)
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed
    TorsionFreeSectionAssembly.simpleUniqueTraceAtHypEmbedded_closed
    TorsionFreePrinted.gerasimovaOsinTheorem11Printed

/-- **`cor:regular-nonmf-algebra` at the limit-set notion**, over the live residuals. -/
theorem printedRegularNonMFAlgebraLimitSet_of_residualsV5 :
    TorsionFreeLimitSetNotion.PrintedRegularNonMFAlgebraLimitSet :=
  TorsionFreeGreendlingerLeaf.printedRegularNonMFAlgebraLimitSet_of_greendlinger
    (greendlinger_of_residualsV5 hloops hpocket hrcell hspan htwogon heuler hcellPinch hproper
      hfaces hpinch)

/-- **`thm:hull`, as printed** (tex line 1636), over the live residuals. -/
theorem printedHullTheorem_of_residualsV5 :
    TorsionFreeSectionSentences.PrintedHullSmallCancellationCurrent.{0} :=
  TorsionFreeGreendlingerLeaf.printedHullTheorem_of_greendlinger
    (greendlinger_of_residualsV5 hloops hpocket hrcell hspan htwogon heuler hcellPinch hproper
      hfaces hpinch)

/-- **`thm:hull` at Osin's notion**, over the live residuals. -/
theorem printedHullTheoremOsin_of_residualsV5 :
    TorsionFreeOsinNotion.PrintedHullSmallCancellationOsin :=
  TorsionFreeGreendlingerLeaf.printedHullTheoremOsin_of_greendlinger
    (greendlinger_of_residualsV5 hloops hpocket hrcell hspan htwogon heuler hcellPinch hproper
      hfaces hpinch)

/-- **`thm:hull` at the limit-set notion**, over the live residuals. -/
theorem printedHullTheoremLimitSet_of_residualsV5 :
    TorsionFreeLimitSetNotion.PrintedHullSmallCancellationLimitSet :=
  TorsionFreeGreendlingerLeaf.printedHullTheoremLimitSet_of_greendlinger
    (greendlinger_of_residualsV5 hloops hpocket hrcell hspan htwogon heuler hcellPinch hproper
      hfaces hpinch)

/-- **`thm:hull` at a torsion-free ambient group**, over the live residuals. -/
theorem hullSmallCancellationTorsionFreePrinted_of_residualsV5 :
    TorsionFreePrinted.HullSmallCancellationTorsionFreePrinted.{0} :=
  TorsionFreeGreendlingerLeaf.hullSmallCancellationTorsionFreePrinted_of_greendlinger
    (greendlinger_of_residualsV5 hloops hpocket hrcell hspan htwogon heuler hcellPinch hproper
      hfaces hpinch)

/-- **The paragraph after `thm:hull`** (tex 1644–1648), over the live residuals. -/
theorem printedHullProofParagraph_of_residualsV5 :
    TorsionFreeSectionSentencesFourLeaves.PrintedHullProofParagraph :=
  TorsionFreeGreendlingerLeaf.printedHullProofParagraph_of_greendlinger
    (greendlinger_of_residualsV5 hloops hpocket hrcell hspan htwogon heuler hcellPinch hproper
      hfaces hpinch)

/-- **`lem:saturation`, as printed**, over the live residuals. -/
theorem printedSaturation_of_residualsV5 : TorsionFreePrinted.PrintedSaturationNoOmega.{0} :=
  TorsionFreeGreendlingerLeaf.printedSaturation_of_greendlinger
    (greendlinger_of_residualsV5 hloops hpocket hrcell hspan htwogon heuler hcellPinch hproper
      hfaces hpinch)

/-- **`lem:saturation` at Osin's notion**, over the live residuals. -/
theorem printedSaturationOsin_of_residualsV5 : TorsionFreeOsinNotion.PrintedSaturationOsin :=
  TorsionFreeGreendlingerLeaf.printedSaturationOsin_of_greendlinger
    (greendlinger_of_residualsV5 hloops hpocket hrcell hspan htwogon heuler hcellPinch hproper
      hfaces hpinch)

/-- **`lem:saturation` at the limit-set notion**, over the live residuals. -/
theorem printedSaturationLimitSet_of_residualsV5 :
    TorsionFreeLimitSetNotion.PrintedSaturationLimitSet :=
  TorsionFreeGreendlingerLeaf.printedSaturationLimitSet_of_greendlinger
    (greendlinger_of_residualsV5 hloops hpocket hrcell hspan htwogon heuler hcellPinch hproper
      hfaces hpinch)

/-- **The Hull 5.7 and 5.8 pair and "Hull's theorem again applies"**, over the live residuals. -/
theorem printedSaturationPairAndHullAgain_of_residualsV5 :
    TorsionFreeSectionSentencesFourLeaves.PrintedSaturationPairAndHullAgain :=
  TorsionFreeGreendlingerLeaf.printedSaturationPairAndHullAgain_of_greendlinger
    (greendlinger_of_residualsV5 hloops hpocket hrcell hspan htwogon heuler hcellPinch hproper
      hfaces hpinch)

/-- **Applying `thm:hull` to `N₀`** in the proof of `lem:saturation`, over the live residuals. -/
theorem printedSaturationApplyHull_of_residualsV5 :
    TorsionFreeSectionSentencesFourLeaves.PrintedSaturationApplyHull :=
  TorsionFreeGreendlingerLeaf.printedSaturationApplyHull_of_greendlinger
    (greendlinger_of_residualsV5 hloops hpocket hrcell hspan htwogon heuler hcellPinch hproper
      hfaces hpinch)

/-- **Applying `lem:saturation` to `G₀` and `N`**, over the live residuals. -/
theorem printedTheoremApplySaturation_of_residualsV5 :
    TorsionFreeSectionSentencesFourLeaves.PrintedTheoremApplySaturation :=
  TorsionFreeGreendlingerLeaf.printedTheoremApplySaturation_of_greendlinger
    (greendlinger_of_residualsV5 hloops hpocket hrcell hspan htwogon heuler hcellPinch hproper
      hfaces hpinch)

/-- **The Fournier-Facio paragraph** (tex 1675–1685), over the live residuals. -/
theorem fournierFacioParagraph_of_residualsV5 : TorsionFreePrinted.FournierFacioParagraph :=
  TorsionFreeGreendlingerLeaf.fournierFacioParagraph_of_greendlinger
    (greendlinger_of_residualsV5 hloops hpocket hrcell hspan htwogon heuler hcellPinch hproper
      hfaces hpinch)

/-- **`G₀` as a Hull Corollary 7.4 common quotient**, over the live residuals. -/
theorem hullCommonQuotientPrinted_of_residualsV5 : TorsionFreePrinted.HullCommonQuotientPrinted :=
  TorsionFreeGreendlingerSentences.manuscriptSentence_hullCommonQuotient_of_greendlinger
    (greendlinger_of_residualsV5 hloops hpocket hrcell hspan htwogon heuler hcellPinch hproper
      hfaces hpinch)

/-- **Hull's Corollary 7.4 at the printed generality**, over the live residuals. -/
theorem printedHullCorollary74_of_residualsV5 : HullCorollary74.PrintedHullCorollary74 :=
  HullCorollary74.printedHullCorollary74_of_greendlinger
    (greendlinger_of_residualsV5 hloops hpocket hrcell hspan htwogon heuler hcellPinch hproper
      hfaces hpinch)

end Residuals

end TorsionFreeResidualsV5
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV5.greendlinger_of_residualsV5
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV5.manuscriptTorsionFreeTheorem_of_residualsV5
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV5.manuscriptTorsionFreeFullMFRadical_of_residualsV5
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV5.manuscriptTorsionFreeTheoremOsin_of_residualsV5
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV5.printedTorsionFreeTheoremLimitSet_of_residualsV5
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV5.manuscriptRegularNonMFAlgebra_of_residualsV5
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV5.manuscriptRegularNonMFAlgebraOsin_of_residualsV5
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV5.printedRegularNonMFAlgebraLimitSet_of_residualsV5
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV5.printedHullTheorem_of_residualsV5
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV5.printedHullTheoremOsin_of_residualsV5
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV5.printedHullTheoremLimitSet_of_residualsV5
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV5.hullSmallCancellationTorsionFreePrinted_of_residualsV5
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV5.printedHullProofParagraph_of_residualsV5
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV5.printedSaturation_of_residualsV5
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV5.printedSaturationOsin_of_residualsV5
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV5.printedSaturationLimitSet_of_residualsV5
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV5.printedSaturationPairAndHullAgain_of_residualsV5
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV5.printedSaturationApplyHull_of_residualsV5
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV5.printedTheoremApplySaturation_of_residualsV5
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV5.fournierFacioParagraph_of_residualsV5
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV5.hullCommonQuotientPrinted_of_residualsV5
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV5.printedHullCorollary74_of_residualsV5
