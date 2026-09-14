import GroupApproximation.GGT.VanKampen.Estimating.OsinGreendlingerWaistV4
import GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV2Copy
import GroupApproximation.Meta.AxiomGuard

/-!
# The top of `sec:torsion-free` over the residuals of the V4 waist

`non_mf_groups_exist.tex`, `sec:torsion-free`: the endpoints of `TorsionFreeResidualsV2Copy`, restated
additively over the ten named residuals of
`GGT.VanKampen.relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV4`:
`OsinLemma94ClassEndLoopsInput`, `OsinLemma94SameCellPocketInput`, `OsinLemma94ClassCasesInput`,
`OsinTwoGonHoldsSectionStatement`, `CellPocketCopyCleanBothOrdersStatement`,
`CellPocketWalkOuterOffSideSomeOrderStatement`, `CellPocketWalkEitherFollowsStatement`,
`CellPocketPinchPosStatement`,
`OsinSectionPocketFaceSetProperSectionStatement` and `PocketPinchLabelledSectionStatement` (all at
`.{0, 0, 0}`).  The closed walls are applied as in `TorsionFreeResidualsV2Copy`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreeResidualsV4

open GGT.VanKampen

section Residuals

variable (hloops : OsinLemma94ClassEndLoopsInput.{0, 0, 0})
  (hpocket : OsinLemma94SameCellPocketInput.{0, 0, 0})
  (hcases : OsinLemma94ClassCasesInput.{0, 0, 0})
  (htwogon : OsinTwoGonHoldsSectionStatement.{0, 0, 0})
  (hcopy : CellPocketCopyCleanBothOrdersStatement.{0, 0, 0})
  (hout : CellPocketWalkOuterOffSideSomeOrderStatement.{0, 0, 0})
  (hfollow : CellPocketWalkEitherFollowsStatement.{0, 0, 0})
  (hcellPinch : CellPocketPinchPosStatement.{0, 0, 0})
  (hfaces : OsinSectionPocketFaceSetProperSectionStatement.{0, 0, 0})
  (hpinch : PocketPinchLabelledSectionStatement.{0, 0, 0})

include hloops hpocket hcases htwogon hcopy hout hfollow hcellPinch hfaces hpinch

/-- Osin's Lemma 4.4 at least-area diagrams, from the ten residuals of the V4 waist. -/
theorem greendlinger_of_residualsV4 : RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV4 hloops hpocket hcases htwogon hcopy
    hout hfollow hcellPinch hfaces hpinch

/-- **`thm:torsion-free`, exactly as printed** (tex line 284), and the abstract's torsion-free
clause, over the V4 residuals. -/
theorem manuscriptTorsionFreeTheorem_of_residualsV4 : TorsionFreePrinted.PrintedTorsionFreeTheorem :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptTorsionFreeTheorem_of_hullLeaves
    (greendlinger_of_residualsV4 hloops hpocket hcases htwogon hcopy hout hfollow hcellPinch hfaces
      hpinch)
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed

/-- **`thm:torsion-free` in the radical form**, over the V4 residuals. -/
theorem manuscriptTorsionFreeFullMFRadical_of_residualsV4 :
    TheoremC.PrintedTorsionFreeFullMFRadical :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptTorsionFreeFullMFRadical_of_hullLeaves
    (greendlinger_of_residualsV4 hloops hpocket hcases htwogon hcopy hout hfollow hcellPinch hfaces
      hpinch)
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed

/-- **`thm:torsion-free` at Osin's notion**, over the V4 residuals. -/
theorem manuscriptTorsionFreeTheoremOsin_of_residualsV4 :
    TorsionFreeOsinNotion.PrintedTorsionFreeTheoremOsin :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptTorsionFreeTheoremOsin_of_hullLeaves
    (greendlinger_of_residualsV4 hloops hpocket hcases htwogon hcopy hout hfollow hcellPinch hfaces
      hpinch)
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed

/-- **`thm:torsion-free` at the limit-set notion**, over the V4 residuals. -/
theorem printedTorsionFreeTheoremLimitSet_of_residualsV4 :
    TorsionFreeLimitSetNotion.PrintedTorsionFreeTheoremLimitSet :=
  TorsionFreeGreendlingerLeaf.printedTorsionFreeTheoremLimitSet_of_greendlinger
    (greendlinger_of_residualsV4 hloops hpocket hcases htwogon hcopy hout hfollow hcellPinch hfaces
      hpinch)

/-- **`cor:regular-nonmf-algebra`, along the printed proof**, over the V4 residuals. -/
theorem manuscriptRegularNonMFAlgebra_of_residualsV4 :
    TorsionFreePrinted.PrintedRegularNonMFAlgebra :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptRegularNonMFAlgebra_of_hullLeaves
    (greendlinger_of_residualsV4 hloops hpocket hcases htwogon hcopy hout hfollow hcellPinch hfaces
      hpinch)
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed
    TorsionFreeSectionAssembly.simpleUniqueTraceAtHypEmbedded_closed
    TorsionFreePrinted.gerasimovaOsinTheorem11Printed

/-- **`cor:regular-nonmf-algebra` at Osin's notion**, over the V4 residuals. -/
theorem manuscriptRegularNonMFAlgebraOsin_of_residualsV4 :
    TorsionFreeOsinNotion.PrintedRegularNonMFAlgebraOsin :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptRegularNonMFAlgebraOsin_of_hullLeaves
    (greendlinger_of_residualsV4 hloops hpocket hcases htwogon hcopy hout hfollow hcellPinch hfaces
      hpinch)
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed
    TorsionFreeSectionAssembly.simpleUniqueTraceAtHypEmbedded_closed
    TorsionFreePrinted.gerasimovaOsinTheorem11Printed

/-- **`cor:regular-nonmf-algebra` at the limit-set notion**, over the V4 residuals. -/
theorem printedRegularNonMFAlgebraLimitSet_of_residualsV4 :
    TorsionFreeLimitSetNotion.PrintedRegularNonMFAlgebraLimitSet :=
  TorsionFreeGreendlingerLeaf.printedRegularNonMFAlgebraLimitSet_of_greendlinger
    (greendlinger_of_residualsV4 hloops hpocket hcases htwogon hcopy hout hfollow hcellPinch hfaces
      hpinch)

/-- **`thm:hull`, as printed** (tex line 1636), over the V4 residuals. -/
theorem printedHullTheorem_of_residualsV4 :
    TorsionFreeSectionSentences.PrintedHullSmallCancellationCurrent.{0} :=
  TorsionFreeGreendlingerLeaf.printedHullTheorem_of_greendlinger
    (greendlinger_of_residualsV4 hloops hpocket hcases htwogon hcopy hout hfollow hcellPinch hfaces
      hpinch)

/-- **`thm:hull` at Osin's notion**, over the V4 residuals. -/
theorem printedHullTheoremOsin_of_residualsV4 :
    TorsionFreeOsinNotion.PrintedHullSmallCancellationOsin :=
  TorsionFreeGreendlingerLeaf.printedHullTheoremOsin_of_greendlinger
    (greendlinger_of_residualsV4 hloops hpocket hcases htwogon hcopy hout hfollow hcellPinch hfaces
      hpinch)

/-- **`thm:hull` at the limit-set notion**, over the V4 residuals. -/
theorem printedHullTheoremLimitSet_of_residualsV4 :
    TorsionFreeLimitSetNotion.PrintedHullSmallCancellationLimitSet :=
  TorsionFreeGreendlingerLeaf.printedHullTheoremLimitSet_of_greendlinger
    (greendlinger_of_residualsV4 hloops hpocket hcases htwogon hcopy hout hfollow hcellPinch hfaces
      hpinch)

/-- **`thm:hull` at a torsion-free ambient group**, over the V4 residuals. -/
theorem hullSmallCancellationTorsionFreePrinted_of_residualsV4 :
    TorsionFreePrinted.HullSmallCancellationTorsionFreePrinted.{0} :=
  TorsionFreeGreendlingerLeaf.hullSmallCancellationTorsionFreePrinted_of_greendlinger
    (greendlinger_of_residualsV4 hloops hpocket hcases htwogon hcopy hout hfollow hcellPinch hfaces
      hpinch)

/-- **The paragraph after `thm:hull`** (tex 1644–1648), over the V4 residuals. -/
theorem printedHullProofParagraph_of_residualsV4 :
    TorsionFreeSectionSentencesFourLeaves.PrintedHullProofParagraph :=
  TorsionFreeGreendlingerLeaf.printedHullProofParagraph_of_greendlinger
    (greendlinger_of_residualsV4 hloops hpocket hcases htwogon hcopy hout hfollow hcellPinch hfaces
      hpinch)

/-- **`lem:saturation`, as printed**, over the V4 residuals. -/
theorem printedSaturation_of_residualsV4 : TorsionFreePrinted.PrintedSaturationNoOmega.{0} :=
  TorsionFreeGreendlingerLeaf.printedSaturation_of_greendlinger
    (greendlinger_of_residualsV4 hloops hpocket hcases htwogon hcopy hout hfollow hcellPinch hfaces
      hpinch)

/-- **`lem:saturation` at Osin's notion**, over the V4 residuals. -/
theorem printedSaturationOsin_of_residualsV4 : TorsionFreeOsinNotion.PrintedSaturationOsin :=
  TorsionFreeGreendlingerLeaf.printedSaturationOsin_of_greendlinger
    (greendlinger_of_residualsV4 hloops hpocket hcases htwogon hcopy hout hfollow hcellPinch hfaces
      hpinch)

/-- **`lem:saturation` at the limit-set notion**, over the V4 residuals. -/
theorem printedSaturationLimitSet_of_residualsV4 :
    TorsionFreeLimitSetNotion.PrintedSaturationLimitSet :=
  TorsionFreeGreendlingerLeaf.printedSaturationLimitSet_of_greendlinger
    (greendlinger_of_residualsV4 hloops hpocket hcases htwogon hcopy hout hfollow hcellPinch hfaces
      hpinch)

/-- **The Hull 5.7 and 5.8 pair and "Hull's theorem again applies"**, over the V4 residuals. -/
theorem printedSaturationPairAndHullAgain_of_residualsV4 :
    TorsionFreeSectionSentencesFourLeaves.PrintedSaturationPairAndHullAgain :=
  TorsionFreeGreendlingerLeaf.printedSaturationPairAndHullAgain_of_greendlinger
    (greendlinger_of_residualsV4 hloops hpocket hcases htwogon hcopy hout hfollow hcellPinch hfaces
      hpinch)

/-- **Applying `thm:hull` to `N₀`** in the proof of `lem:saturation`, over the V4 residuals. -/
theorem printedSaturationApplyHull_of_residualsV4 :
    TorsionFreeSectionSentencesFourLeaves.PrintedSaturationApplyHull :=
  TorsionFreeGreendlingerLeaf.printedSaturationApplyHull_of_greendlinger
    (greendlinger_of_residualsV4 hloops hpocket hcases htwogon hcopy hout hfollow hcellPinch hfaces
      hpinch)

/-- **Applying `lem:saturation` to `G₀` and `N`**, over the V4 residuals. -/
theorem printedTheoremApplySaturation_of_residualsV4 :
    TorsionFreeSectionSentencesFourLeaves.PrintedTheoremApplySaturation :=
  TorsionFreeGreendlingerLeaf.printedTheoremApplySaturation_of_greendlinger
    (greendlinger_of_residualsV4 hloops hpocket hcases htwogon hcopy hout hfollow hcellPinch hfaces
      hpinch)

/-- **The Fournier-Facio paragraph** (tex 1675–1685), over the V4 residuals. -/
theorem fournierFacioParagraph_of_residualsV4 : TorsionFreePrinted.FournierFacioParagraph :=
  TorsionFreeGreendlingerLeaf.fournierFacioParagraph_of_greendlinger
    (greendlinger_of_residualsV4 hloops hpocket hcases htwogon hcopy hout hfollow hcellPinch hfaces
      hpinch)

/-- **`G₀` as a Hull Corollary 7.4 common quotient**, over the V4 residuals. -/
theorem hullCommonQuotientPrinted_of_residualsV4 : TorsionFreePrinted.HullCommonQuotientPrinted :=
  TorsionFreeGreendlingerSentences.manuscriptSentence_hullCommonQuotient_of_greendlinger
    (greendlinger_of_residualsV4 hloops hpocket hcases htwogon hcopy hout hfollow hcellPinch hfaces
      hpinch)

/-- **Hull's Corollary 7.4 at the printed generality**, over the V4 residuals. -/
theorem printedHullCorollary74_of_residualsV4 : HullCorollary74.PrintedHullCorollary74 :=
  HullCorollary74.printedHullCorollary74_of_greendlinger
    (greendlinger_of_residualsV4 hloops hpocket hcases htwogon hcopy hout hfollow hcellPinch hfaces
      hpinch)

end Residuals

end TorsionFreeResidualsV4
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4.greendlinger_of_residualsV4
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4.manuscriptTorsionFreeTheorem_of_residualsV4
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4.manuscriptTorsionFreeFullMFRadical_of_residualsV4
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4.manuscriptTorsionFreeTheoremOsin_of_residualsV4
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4.printedTorsionFreeTheoremLimitSet_of_residualsV4
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4.manuscriptRegularNonMFAlgebra_of_residualsV4
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4.manuscriptRegularNonMFAlgebraOsin_of_residualsV4
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4.printedRegularNonMFAlgebraLimitSet_of_residualsV4
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4.printedHullTheorem_of_residualsV4
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4.printedHullTheoremOsin_of_residualsV4
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4.printedHullTheoremLimitSet_of_residualsV4
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4.hullSmallCancellationTorsionFreePrinted_of_residualsV4
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4.printedHullProofParagraph_of_residualsV4
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4.printedSaturation_of_residualsV4
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4.printedSaturationOsin_of_residualsV4
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4.printedSaturationLimitSet_of_residualsV4
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4.printedSaturationPairAndHullAgain_of_residualsV4
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4.printedSaturationApplyHull_of_residualsV4
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4.printedTheoremApplySaturation_of_residualsV4
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4.fournierFacioParagraph_of_residualsV4
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4.hullCommonQuotientPrinted_of_residualsV4
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4.printedHullCorollary74_of_residualsV4
