import GroupApproximation.GGT.VanKampen.Estimating.OsinGreendlingerResidualsV2Copy
import GroupApproximation.Manuscript.NonMF.TorsionFreeLiteratureInputsLeastArea
import GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf
import GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerSentences
import GroupApproximation.Manuscript.NonMF.HullCorollary74
import GroupApproximation.Manuscript.NonMF.TorsionFreeSectionAssembly
import GroupApproximation.Manuscript.NonMF.GerasimovaOsinTheorem11Closed
import GroupApproximation.Kazhdan.KotowskiOllivierClosed
import GroupApproximation.GGT.HullSCLemma51EmbeddedBridgeHolds
import GroupApproximation.GroupTheory.HydeLodha.FinitelyPresentedInfiniteSimpleClosed
import GroupApproximation.Meta.AxiomGuard

/-!
# The top of `sec:torsion-free` over the residuals of the Greendlinger waist

`non_mf_groups_exist.tex`, `sec:torsion-free`: `thm:torsion-free` (and the abstract's torsion-free
clause), `thm:hull`, `lem:saturation`, `cor:regular-nonmf-algebra`, the paragraph after `thm:hull`,
the Fournier-Facio paragraph and the sentences applying Hull's theorem and the saturation lemma.

Every printed endpoint of the section rests on one binder, Osin's Lemma 4.4 at least-area diagrams,
`GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}`.  The other walls are
closed on main: the embedded bridge (`HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed`),
Kotowski–Ollivier (`KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed`), the Hyde–Lodha group
(`HydeLodha.finitelyPresentedInfiniteSimple_closed`), Dahmani–Guirardel–Osin 2.35
(`TorsionFreeSectionAssembly.simpleUniqueTraceAtHypEmbedded_closed`) and Gerasimova–Osin 1.1
(`TorsionFreePrinted.gerasimovaOsinTheorem11Printed`).

This module states each endpoint `_of_residuals` over exactly the nine named residuals of the waist
`GGT.VanKampen.relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV2Copy`:
`OsinLemma94PolygonCountInput`, `OsinLemma94CaseOneRCellStatement`, `OsinTwoGonHoldsSectionStatement`,
`CellPocketCopyCleanStatement`, `CellPocketWalkOuterOffSideStatement`,
`CellPocketWalkSideRelatorCellStatement`, `CellPocketPinchPosStatement`,
`OsinSectionPocketFaceSetSectionStatement` and `PocketPinchLabelledPosStatement` (all at `.{0, 0, 0}`).
When the waist closes, each endpoint closes by applying the closed producers.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreeResidualsV2Copy

open GGT.VanKampen

section Residuals

variable (hcount : OsinLemma94PolygonCountInput.{0, 0, 0})
  (hrcell : OsinLemma94CaseOneRCellStatement.{0, 0, 0})
  (htwogon : OsinTwoGonHoldsSectionStatement.{0, 0, 0})
  (hcopy : CellPocketCopyCleanStatement.{0, 0, 0})
  (hout : CellPocketWalkOuterOffSideStatement.{0, 0, 0})
  (hkept : CellPocketWalkSideRelatorCellStatement.{0, 0, 0})
  (hcellPinch : CellPocketPinchPosStatement.{0, 0, 0})
  (hfaces : OsinSectionPocketFaceSetSectionStatement.{0, 0, 0})
  (hpinch : PocketPinchLabelledPosStatement.{0, 0, 0})

include hcount hrcell htwogon hcopy hout hkept hcellPinch hfaces hpinch

/-- Osin's Lemma 4.4 at least-area diagrams, from the nine residuals of the copy waist. -/
theorem greendlinger_of_residuals :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV2Copy hcount hrcell htwogon hcopy hout
    hkept hcellPinch hfaces hpinch

/-- **`thm:torsion-free`, exactly as printed** (tex line 284), and the abstract's torsion-free
clause, over the residuals: the top endpoint with the closed bridge, Kotowski–Ollivier and
Hyde–Lodha group. -/
theorem manuscriptTorsionFreeTheorem_of_residuals : TorsionFreePrinted.PrintedTorsionFreeTheorem :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptTorsionFreeTheorem_of_hullLeaves
    (greendlinger_of_residuals hcount hrcell htwogon hcopy hout hkept hcellPinch hfaces hpinch)
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed

/-- **`thm:torsion-free` in the radical form**, over the residuals. -/
theorem manuscriptTorsionFreeFullMFRadical_of_residuals : TheoremC.PrintedTorsionFreeFullMFRadical :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptTorsionFreeFullMFRadical_of_hullLeaves
    (greendlinger_of_residuals hcount hrcell htwogon hcopy hout hkept hcellPinch hfaces hpinch)
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed

/-- **`thm:torsion-free` at Osin's notion**, over the residuals. -/
theorem manuscriptTorsionFreeTheoremOsin_of_residuals :
    TorsionFreeOsinNotion.PrintedTorsionFreeTheoremOsin :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptTorsionFreeTheoremOsin_of_hullLeaves
    (greendlinger_of_residuals hcount hrcell htwogon hcopy hout hkept hcellPinch hfaces hpinch)
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed

/-- **`thm:torsion-free` at the limit-set notion**, over the residuals. -/
theorem printedTorsionFreeTheoremLimitSet_of_residuals :
    TorsionFreeLimitSetNotion.PrintedTorsionFreeTheoremLimitSet :=
  TorsionFreeGreendlingerLeaf.printedTorsionFreeTheoremLimitSet_of_greendlinger
    (greendlinger_of_residuals hcount hrcell htwogon hcopy hout hkept hcellPinch hfaces hpinch)

/-- **`cor:regular-nonmf-algebra`, along the printed proof**, over the residuals: the top endpoint
with the closed walls, DGO 2.35 and Gerasimova–Osin 1.1. -/
theorem manuscriptRegularNonMFAlgebra_of_residuals : TorsionFreePrinted.PrintedRegularNonMFAlgebra :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptRegularNonMFAlgebra_of_hullLeaves
    (greendlinger_of_residuals hcount hrcell htwogon hcopy hout hkept hcellPinch hfaces hpinch)
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed
    TorsionFreeSectionAssembly.simpleUniqueTraceAtHypEmbedded_closed
    TorsionFreePrinted.gerasimovaOsinTheorem11Printed

/-- **`cor:regular-nonmf-algebra` at Osin's notion**, over the residuals. -/
theorem manuscriptRegularNonMFAlgebraOsin_of_residuals :
    TorsionFreeOsinNotion.PrintedRegularNonMFAlgebraOsin :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptRegularNonMFAlgebraOsin_of_hullLeaves
    (greendlinger_of_residuals hcount hrcell htwogon hcopy hout hkept hcellPinch hfaces hpinch)
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed
    TorsionFreeSectionAssembly.simpleUniqueTraceAtHypEmbedded_closed
    TorsionFreePrinted.gerasimovaOsinTheorem11Printed

/-- **`cor:regular-nonmf-algebra` at the limit-set notion**, over the residuals. -/
theorem printedRegularNonMFAlgebraLimitSet_of_residuals :
    TorsionFreeLimitSetNotion.PrintedRegularNonMFAlgebraLimitSet :=
  TorsionFreeGreendlingerLeaf.printedRegularNonMFAlgebraLimitSet_of_greendlinger
    (greendlinger_of_residuals hcount hrcell htwogon hcopy hout hkept hcellPinch hfaces hpinch)

/-- **`thm:hull`, as printed** (tex line 1636), over the residuals. -/
theorem printedHullTheorem_of_residuals :
    TorsionFreeSectionSentences.PrintedHullSmallCancellationCurrent.{0} :=
  TorsionFreeGreendlingerLeaf.printedHullTheorem_of_greendlinger
    (greendlinger_of_residuals hcount hrcell htwogon hcopy hout hkept hcellPinch hfaces hpinch)

/-- **`thm:hull` at Osin's notion**, over the residuals. -/
theorem printedHullTheoremOsin_of_residuals : TorsionFreeOsinNotion.PrintedHullSmallCancellationOsin :=
  TorsionFreeGreendlingerLeaf.printedHullTheoremOsin_of_greendlinger
    (greendlinger_of_residuals hcount hrcell htwogon hcopy hout hkept hcellPinch hfaces hpinch)

/-- **`thm:hull` at the limit-set notion**, over the residuals. -/
theorem printedHullTheoremLimitSet_of_residuals :
    TorsionFreeLimitSetNotion.PrintedHullSmallCancellationLimitSet :=
  TorsionFreeGreendlingerLeaf.printedHullTheoremLimitSet_of_greendlinger
    (greendlinger_of_residuals hcount hrcell htwogon hcopy hout hkept hcellPinch hfaces hpinch)

/-- **`thm:hull` at a torsion-free ambient group**, over the residuals. -/
theorem hullSmallCancellationTorsionFreePrinted_of_residuals :
    TorsionFreePrinted.HullSmallCancellationTorsionFreePrinted.{0} :=
  TorsionFreeGreendlingerLeaf.hullSmallCancellationTorsionFreePrinted_of_greendlinger
    (greendlinger_of_residuals hcount hrcell htwogon hcopy hout hkept hcellPinch hfaces hpinch)

/-- **The paragraph after `thm:hull`** (tex 1644–1648), over the residuals. -/
theorem printedHullProofParagraph_of_residuals :
    TorsionFreeSectionSentencesFourLeaves.PrintedHullProofParagraph :=
  TorsionFreeGreendlingerLeaf.printedHullProofParagraph_of_greendlinger
    (greendlinger_of_residuals hcount hrcell htwogon hcopy hout hkept hcellPinch hfaces hpinch)

/-- **`lem:saturation`, as printed**, over the residuals. -/
theorem printedSaturation_of_residuals : TorsionFreePrinted.PrintedSaturationNoOmega.{0} :=
  TorsionFreeGreendlingerLeaf.printedSaturation_of_greendlinger
    (greendlinger_of_residuals hcount hrcell htwogon hcopy hout hkept hcellPinch hfaces hpinch)

/-- **`lem:saturation` at Osin's notion**, over the residuals. -/
theorem printedSaturationOsin_of_residuals : TorsionFreeOsinNotion.PrintedSaturationOsin :=
  TorsionFreeGreendlingerLeaf.printedSaturationOsin_of_greendlinger
    (greendlinger_of_residuals hcount hrcell htwogon hcopy hout hkept hcellPinch hfaces hpinch)

/-- **`lem:saturation` at the limit-set notion**, over the residuals. -/
theorem printedSaturationLimitSet_of_residuals :
    TorsionFreeLimitSetNotion.PrintedSaturationLimitSet :=
  TorsionFreeGreendlingerLeaf.printedSaturationLimitSet_of_greendlinger
    (greendlinger_of_residuals hcount hrcell htwogon hcopy hout hkept hcellPinch hfaces hpinch)

/-- **The Hull 5.7 and 5.8 pair and "Hull's theorem again applies"**, over the residuals. -/
theorem printedSaturationPairAndHullAgain_of_residuals :
    TorsionFreeSectionSentencesFourLeaves.PrintedSaturationPairAndHullAgain :=
  TorsionFreeGreendlingerLeaf.printedSaturationPairAndHullAgain_of_greendlinger
    (greendlinger_of_residuals hcount hrcell htwogon hcopy hout hkept hcellPinch hfaces hpinch)

/-- **Applying `thm:hull` to `N₀`** in the proof of `lem:saturation`, over the residuals. -/
theorem printedSaturationApplyHull_of_residuals :
    TorsionFreeSectionSentencesFourLeaves.PrintedSaturationApplyHull :=
  TorsionFreeGreendlingerLeaf.printedSaturationApplyHull_of_greendlinger
    (greendlinger_of_residuals hcount hrcell htwogon hcopy hout hkept hcellPinch hfaces hpinch)

/-- **Applying `lem:saturation` to `G₀` and `N`** in the proof of `thm:torsion-free`, over the
residuals. -/
theorem printedTheoremApplySaturation_of_residuals :
    TorsionFreeSectionSentencesFourLeaves.PrintedTheoremApplySaturation :=
  TorsionFreeGreendlingerLeaf.printedTheoremApplySaturation_of_greendlinger
    (greendlinger_of_residuals hcount hrcell htwogon hcopy hout hkept hcellPinch hfaces hpinch)

/-- **The Fournier-Facio paragraph** (tex 1675–1685), over the residuals. -/
theorem fournierFacioParagraph_of_residuals : TorsionFreePrinted.FournierFacioParagraph :=
  TorsionFreeGreendlingerLeaf.fournierFacioParagraph_of_greendlinger
    (greendlinger_of_residuals hcount hrcell htwogon hcopy hout hkept hcellPinch hfaces hpinch)

/-- **`G₀` as a Hull Corollary 7.4 common quotient**, over the residuals. -/
theorem hullCommonQuotientPrinted_of_residuals : TorsionFreePrinted.HullCommonQuotientPrinted :=
  TorsionFreeGreendlingerSentences.manuscriptSentence_hullCommonQuotient_of_greendlinger
    (greendlinger_of_residuals hcount hrcell htwogon hcopy hout hkept hcellPinch hfaces hpinch)

/-- **Hull's Corollary 7.4 at the printed generality**, over the residuals. -/
theorem printedHullCorollary74_of_residuals : HullCorollary74.PrintedHullCorollary74 :=
  HullCorollary74.printedHullCorollary74_of_greendlinger
    (greendlinger_of_residuals hcount hrcell htwogon hcopy hout hkept hcellPinch hfaces hpinch)

end Residuals

end TorsionFreeResidualsV2Copy
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV2Copy.greendlinger_of_residuals
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV2Copy.manuscriptTorsionFreeTheorem_of_residuals
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV2Copy.manuscriptTorsionFreeFullMFRadical_of_residuals
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV2Copy.manuscriptTorsionFreeTheoremOsin_of_residuals
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV2Copy.printedTorsionFreeTheoremLimitSet_of_residuals
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV2Copy.manuscriptRegularNonMFAlgebra_of_residuals
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV2Copy.manuscriptRegularNonMFAlgebraOsin_of_residuals
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV2Copy.printedRegularNonMFAlgebraLimitSet_of_residuals
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV2Copy.printedHullTheorem_of_residuals
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV2Copy.printedHullTheoremOsin_of_residuals
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV2Copy.printedHullTheoremLimitSet_of_residuals
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV2Copy.hullSmallCancellationTorsionFreePrinted_of_residuals
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV2Copy.printedHullProofParagraph_of_residuals
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV2Copy.printedSaturation_of_residuals
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV2Copy.printedSaturationOsin_of_residuals
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV2Copy.printedSaturationLimitSet_of_residuals
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV2Copy.printedSaturationPairAndHullAgain_of_residuals
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV2Copy.printedSaturationApplyHull_of_residuals
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV2Copy.printedTheoremApplySaturation_of_residuals
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV2Copy.fournierFacioParagraph_of_residuals
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV2Copy.hullCommonQuotientPrinted_of_residuals
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV2Copy.printedHullCorollary74_of_residuals
