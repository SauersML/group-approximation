import GroupApproximation.GGT.VanKampen.Estimating.OsinGreendlingerWaistV4TwoThreshold
import GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV2Copy
import GroupApproximation.Meta.AxiomGuard

/-!
# The top of `sec:torsion-free` over the residuals of the two-threshold waist

`non_mf_groups_exist.tex`, `sec:torsion-free`: the endpoints of `TorsionFreeResidualsV2Copy`, restated
additively over the eight named residuals of
`GGT.VanKampen.relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV4TwoThreshold`:
`OsinLemma94ClassEndLoopsInput`, `OsinLemma94SameCellPocketInput`, `OsinLemma94CaseOneRCellStatement`,
`OsinLemma94ClassCaseGapSpanStatement`, `OsinTwoGonHoldsSectionStatement`,
`OsinMultipleEdgePocketRegionCopySectionStatement`, `OsinSectionPocketFaceSetProperSectionStatement` and
`PocketPinchLabelledSectionStatement` (all at `.{0, 0, 0}`).  None of them is the refuted cell pinch
`CellPocketPinchPosStatement`, which the V2Copy, V4 and V4 Euler forms bind.  The closed walls are
applied as in `TorsionFreeResidualsV2Copy`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreeResidualsV4TwoThreshold

open GGT.VanKampen

section Residuals

variable (hloops : OsinLemma94ClassEndLoopsInput.{0, 0, 0})
  (hpocket : OsinLemma94SameCellPocketInput.{0, 0, 0})
  (hrcell : OsinLemma94CaseOneRCellStatement.{0, 0, 0})
  (hspan : OsinLemma94ClassCaseGapSpanStatement.{0, 0, 0})
  (htwogon : OsinTwoGonHoldsSectionStatement.{0, 0, 0})
  (hregion : OsinMultipleEdgePocketRegionCopySectionStatement.{0, 0, 0})
  (hfaces : OsinSectionPocketFaceSetProperSectionStatement.{0, 0, 0})
  (hpinch : PocketPinchLabelledSectionStatement.{0, 0, 0})

include hloops hpocket hrcell hspan htwogon hregion hfaces hpinch

/-- Osin's Lemma 4.4 at least-area diagrams, from the eight residuals of the two-threshold waist. -/
theorem greendlinger_of_residualsV4TwoThreshold : RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV4TwoThreshold hloops hpocket hrcell hspan
    htwogon hregion hfaces hpinch

/-- **`thm:torsion-free`, exactly as printed** (tex line 284), and the abstract's torsion-free
clause, over the two-threshold residuals. -/
theorem manuscriptTorsionFreeTheorem_of_residualsV4TwoThreshold : TorsionFreePrinted.PrintedTorsionFreeTheorem :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptTorsionFreeTheorem_of_hullLeaves
    (greendlinger_of_residualsV4TwoThreshold hloops hpocket hrcell hspan htwogon hregion hfaces hpinch)
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed

/-- **`thm:torsion-free` in the radical form**, over the two-threshold residuals. -/
theorem manuscriptTorsionFreeFullMFRadical_of_residualsV4TwoThreshold :
    TheoremC.PrintedTorsionFreeFullMFRadical :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptTorsionFreeFullMFRadical_of_hullLeaves
    (greendlinger_of_residualsV4TwoThreshold hloops hpocket hrcell hspan htwogon hregion hfaces hpinch)
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed

/-- **`thm:torsion-free` at Osin's notion**, over the two-threshold residuals. -/
theorem manuscriptTorsionFreeTheoremOsin_of_residualsV4TwoThreshold :
    TorsionFreeOsinNotion.PrintedTorsionFreeTheoremOsin :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptTorsionFreeTheoremOsin_of_hullLeaves
    (greendlinger_of_residualsV4TwoThreshold hloops hpocket hrcell hspan htwogon hregion hfaces hpinch)
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed

/-- **`thm:torsion-free` at the limit-set notion**, over the two-threshold residuals. -/
theorem printedTorsionFreeTheoremLimitSet_of_residualsV4TwoThreshold :
    TorsionFreeLimitSetNotion.PrintedTorsionFreeTheoremLimitSet :=
  TorsionFreeGreendlingerLeaf.printedTorsionFreeTheoremLimitSet_of_greendlinger
    (greendlinger_of_residualsV4TwoThreshold hloops hpocket hrcell hspan htwogon hregion hfaces hpinch)

/-- **`cor:regular-nonmf-algebra`, along the printed proof**, over the two-threshold residuals. -/
theorem manuscriptRegularNonMFAlgebra_of_residualsV4TwoThreshold :
    TorsionFreePrinted.PrintedRegularNonMFAlgebra :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptRegularNonMFAlgebra_of_hullLeaves
    (greendlinger_of_residualsV4TwoThreshold hloops hpocket hrcell hspan htwogon hregion hfaces hpinch)
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed
    TorsionFreeSectionAssembly.simpleUniqueTraceAtHypEmbedded_closed
    TorsionFreePrinted.gerasimovaOsinTheorem11Printed

/-- **`cor:regular-nonmf-algebra` at Osin's notion**, over the two-threshold residuals. -/
theorem manuscriptRegularNonMFAlgebraOsin_of_residualsV4TwoThreshold :
    TorsionFreeOsinNotion.PrintedRegularNonMFAlgebraOsin :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptRegularNonMFAlgebraOsin_of_hullLeaves
    (greendlinger_of_residualsV4TwoThreshold hloops hpocket hrcell hspan htwogon hregion hfaces hpinch)
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed
    TorsionFreeSectionAssembly.simpleUniqueTraceAtHypEmbedded_closed
    TorsionFreePrinted.gerasimovaOsinTheorem11Printed

/-- **`cor:regular-nonmf-algebra` at the limit-set notion**, over the two-threshold residuals. -/
theorem printedRegularNonMFAlgebraLimitSet_of_residualsV4TwoThreshold :
    TorsionFreeLimitSetNotion.PrintedRegularNonMFAlgebraLimitSet :=
  TorsionFreeGreendlingerLeaf.printedRegularNonMFAlgebraLimitSet_of_greendlinger
    (greendlinger_of_residualsV4TwoThreshold hloops hpocket hrcell hspan htwogon hregion hfaces hpinch)

/-- **`thm:hull`, as printed** (tex line 1636), over the two-threshold residuals. -/
theorem printedHullTheorem_of_residualsV4TwoThreshold :
    TorsionFreeSectionSentences.PrintedHullSmallCancellationCurrent.{0} :=
  TorsionFreeGreendlingerLeaf.printedHullTheorem_of_greendlinger
    (greendlinger_of_residualsV4TwoThreshold hloops hpocket hrcell hspan htwogon hregion hfaces hpinch)

/-- **`thm:hull` at Osin's notion**, over the two-threshold residuals. -/
theorem printedHullTheoremOsin_of_residualsV4TwoThreshold :
    TorsionFreeOsinNotion.PrintedHullSmallCancellationOsin :=
  TorsionFreeGreendlingerLeaf.printedHullTheoremOsin_of_greendlinger
    (greendlinger_of_residualsV4TwoThreshold hloops hpocket hrcell hspan htwogon hregion hfaces hpinch)

/-- **`thm:hull` at the limit-set notion**, over the two-threshold residuals. -/
theorem printedHullTheoremLimitSet_of_residualsV4TwoThreshold :
    TorsionFreeLimitSetNotion.PrintedHullSmallCancellationLimitSet :=
  TorsionFreeGreendlingerLeaf.printedHullTheoremLimitSet_of_greendlinger
    (greendlinger_of_residualsV4TwoThreshold hloops hpocket hrcell hspan htwogon hregion hfaces hpinch)

/-- **`thm:hull` at a torsion-free ambient group**, over the two-threshold residuals. -/
theorem hullSmallCancellationTorsionFreePrinted_of_residualsV4TwoThreshold :
    TorsionFreePrinted.HullSmallCancellationTorsionFreePrinted.{0} :=
  TorsionFreeGreendlingerLeaf.hullSmallCancellationTorsionFreePrinted_of_greendlinger
    (greendlinger_of_residualsV4TwoThreshold hloops hpocket hrcell hspan htwogon hregion hfaces hpinch)

/-- **The paragraph after `thm:hull`** (tex 1644–1648), over the two-threshold residuals. -/
theorem printedHullProofParagraph_of_residualsV4TwoThreshold :
    TorsionFreeSectionSentencesFourLeaves.PrintedHullProofParagraph :=
  TorsionFreeGreendlingerLeaf.printedHullProofParagraph_of_greendlinger
    (greendlinger_of_residualsV4TwoThreshold hloops hpocket hrcell hspan htwogon hregion hfaces hpinch)

/-- **`lem:saturation`, as printed**, over the two-threshold residuals. -/
theorem printedSaturation_of_residualsV4TwoThreshold : TorsionFreePrinted.PrintedSaturationNoOmega.{0} :=
  TorsionFreeGreendlingerLeaf.printedSaturation_of_greendlinger
    (greendlinger_of_residualsV4TwoThreshold hloops hpocket hrcell hspan htwogon hregion hfaces hpinch)

/-- **`lem:saturation` at Osin's notion**, over the two-threshold residuals. -/
theorem printedSaturationOsin_of_residualsV4TwoThreshold : TorsionFreeOsinNotion.PrintedSaturationOsin :=
  TorsionFreeGreendlingerLeaf.printedSaturationOsin_of_greendlinger
    (greendlinger_of_residualsV4TwoThreshold hloops hpocket hrcell hspan htwogon hregion hfaces hpinch)

/-- **`lem:saturation` at the limit-set notion**, over the two-threshold residuals. -/
theorem printedSaturationLimitSet_of_residualsV4TwoThreshold :
    TorsionFreeLimitSetNotion.PrintedSaturationLimitSet :=
  TorsionFreeGreendlingerLeaf.printedSaturationLimitSet_of_greendlinger
    (greendlinger_of_residualsV4TwoThreshold hloops hpocket hrcell hspan htwogon hregion hfaces hpinch)

/-- **The Hull 5.7 and 5.8 pair and "Hull's theorem again applies"**, over the two-threshold residuals. -/
theorem printedSaturationPairAndHullAgain_of_residualsV4TwoThreshold :
    TorsionFreeSectionSentencesFourLeaves.PrintedSaturationPairAndHullAgain :=
  TorsionFreeGreendlingerLeaf.printedSaturationPairAndHullAgain_of_greendlinger
    (greendlinger_of_residualsV4TwoThreshold hloops hpocket hrcell hspan htwogon hregion hfaces hpinch)

/-- **Applying `thm:hull` to `N₀`** in the proof of `lem:saturation`, over the two-threshold residuals. -/
theorem printedSaturationApplyHull_of_residualsV4TwoThreshold :
    TorsionFreeSectionSentencesFourLeaves.PrintedSaturationApplyHull :=
  TorsionFreeGreendlingerLeaf.printedSaturationApplyHull_of_greendlinger
    (greendlinger_of_residualsV4TwoThreshold hloops hpocket hrcell hspan htwogon hregion hfaces hpinch)

/-- **Applying `lem:saturation` to `G₀` and `N`**, over the two-threshold residuals. -/
theorem printedTheoremApplySaturation_of_residualsV4TwoThreshold :
    TorsionFreeSectionSentencesFourLeaves.PrintedTheoremApplySaturation :=
  TorsionFreeGreendlingerLeaf.printedTheoremApplySaturation_of_greendlinger
    (greendlinger_of_residualsV4TwoThreshold hloops hpocket hrcell hspan htwogon hregion hfaces hpinch)

/-- **The Fournier-Facio paragraph** (tex 1675–1685), over the two-threshold residuals. -/
theorem fournierFacioParagraph_of_residualsV4TwoThreshold : TorsionFreePrinted.FournierFacioParagraph :=
  TorsionFreeGreendlingerLeaf.fournierFacioParagraph_of_greendlinger
    (greendlinger_of_residualsV4TwoThreshold hloops hpocket hrcell hspan htwogon hregion hfaces hpinch)

/-- **`G₀` as a Hull Corollary 7.4 common quotient**, over the two-threshold residuals. -/
theorem hullCommonQuotientPrinted_of_residualsV4TwoThreshold : TorsionFreePrinted.HullCommonQuotientPrinted :=
  TorsionFreeGreendlingerSentences.manuscriptSentence_hullCommonQuotient_of_greendlinger
    (greendlinger_of_residualsV4TwoThreshold hloops hpocket hrcell hspan htwogon hregion hfaces hpinch)

/-- **Hull's Corollary 7.4 at the printed generality**, over the two-threshold residuals. -/
theorem printedHullCorollary74_of_residualsV4TwoThreshold : HullCorollary74.PrintedHullCorollary74 :=
  HullCorollary74.printedHullCorollary74_of_greendlinger
    (greendlinger_of_residualsV4TwoThreshold hloops hpocket hrcell hspan htwogon hregion hfaces hpinch)

end Residuals

end TorsionFreeResidualsV4TwoThreshold
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4TwoThreshold.greendlinger_of_residualsV4TwoThreshold
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4TwoThreshold.manuscriptTorsionFreeTheorem_of_residualsV4TwoThreshold
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4TwoThreshold.manuscriptTorsionFreeFullMFRadical_of_residualsV4TwoThreshold
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4TwoThreshold.manuscriptTorsionFreeTheoremOsin_of_residualsV4TwoThreshold
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4TwoThreshold.printedTorsionFreeTheoremLimitSet_of_residualsV4TwoThreshold
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4TwoThreshold.manuscriptRegularNonMFAlgebra_of_residualsV4TwoThreshold
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4TwoThreshold.manuscriptRegularNonMFAlgebraOsin_of_residualsV4TwoThreshold
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4TwoThreshold.printedRegularNonMFAlgebraLimitSet_of_residualsV4TwoThreshold
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4TwoThreshold.printedHullTheorem_of_residualsV4TwoThreshold
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4TwoThreshold.printedHullTheoremOsin_of_residualsV4TwoThreshold
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4TwoThreshold.printedHullTheoremLimitSet_of_residualsV4TwoThreshold
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4TwoThreshold.hullSmallCancellationTorsionFreePrinted_of_residualsV4TwoThreshold
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4TwoThreshold.printedHullProofParagraph_of_residualsV4TwoThreshold
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4TwoThreshold.printedSaturation_of_residualsV4TwoThreshold
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4TwoThreshold.printedSaturationOsin_of_residualsV4TwoThreshold
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4TwoThreshold.printedSaturationLimitSet_of_residualsV4TwoThreshold
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4TwoThreshold.printedSaturationPairAndHullAgain_of_residualsV4TwoThreshold
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4TwoThreshold.printedSaturationApplyHull_of_residualsV4TwoThreshold
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4TwoThreshold.printedTheoremApplySaturation_of_residualsV4TwoThreshold
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4TwoThreshold.fournierFacioParagraph_of_residualsV4TwoThreshold
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4TwoThreshold.hullCommonQuotientPrinted_of_residualsV4TwoThreshold
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4TwoThreshold.printedHullCorollary74_of_residualsV4TwoThreshold
