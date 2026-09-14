import GroupApproximation.GGT.VanKampen.Estimating.OsinGreendlingerWaistV4Euler
import GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV2Copy
import GroupApproximation.Meta.AxiomGuard

/-!
# The top of `sec:torsion-free` over the residuals of the V4 Euler waist

`non_mf_groups_exist.tex`, `sec:torsion-free`: the endpoints of `TorsionFreeResidualsV4Euler`, restated
additively over the nine named residuals of
`GGT.VanKampen.relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV4Euler`:
`OsinLemma94ClassEndLoopsInput`, `OsinLemma94SameCellPocketInput`, `OsinLemma94ClassCasesInput`,
`OsinTwoGonHoldsSectionStatement`, `CellPocketCopyCleanBothOrdersStatement`,
`CellPocketWalkEulerStatement`, `CellPocketPinchPosStatement`,
`OsinSectionPocketFaceSetProperSectionStatement` and `PocketPinchLabelledSectionStatement` (all at
`.{0, 0, 0}`).  The exterior-off-side residual of V4 is closed by `cellPocketWalkOuterOffSideSomeOrder`,
and `CellPocketWalkEitherFollowsStatement` is replaced by the Euler equalities.  The closed walls are
applied as in `TorsionFreeResidualsV2Copy`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreeResidualsV4Euler

open GGT.VanKampen

section Residuals

variable (hloops : OsinLemma94ClassEndLoopsInput.{0, 0, 0})
  (hpocket : OsinLemma94SameCellPocketInput.{0, 0, 0})
  (hcases : OsinLemma94ClassCasesInput.{0, 0, 0})
  (htwogon : OsinTwoGonHoldsSectionStatement.{0, 0, 0})
  (hcopy : CellPocketCopyCleanBothOrdersStatement.{0, 0, 0})
  (heuler : CellPocketWalkEulerStatement.{0, 0, 0})
  (hcellPinch : CellPocketPinchPosStatement.{0, 0, 0})
  (hfaces : OsinSectionPocketFaceSetProperSectionStatement.{0, 0, 0})
  (hpinch : PocketPinchLabelledSectionStatement.{0, 0, 0})

include hloops hpocket hcases htwogon hcopy heuler hcellPinch hfaces hpinch

/-- Osin's Lemma 4.4 at least-area diagrams, from the nine residuals of the V4 Euler waist. -/
theorem greendlinger_of_residualsV4Euler : RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV4Euler hloops hpocket hcases htwogon hcopy
    heuler hcellPinch hfaces hpinch

/-- **`thm:torsion-free`, exactly as printed** (tex line 284), and the abstract's torsion-free
clause, over the V4 Euler residuals. -/
theorem manuscriptTorsionFreeTheorem_of_residualsV4Euler : TorsionFreePrinted.PrintedTorsionFreeTheorem :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptTorsionFreeTheorem_of_hullLeaves
    (greendlinger_of_residualsV4Euler hloops hpocket hcases htwogon hcopy heuler hcellPinch hfaces
      hpinch)
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed

/-- **`thm:torsion-free` in the radical form**, over the V4 Euler residuals. -/
theorem manuscriptTorsionFreeFullMFRadical_of_residualsV4Euler :
    TheoremC.PrintedTorsionFreeFullMFRadical :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptTorsionFreeFullMFRadical_of_hullLeaves
    (greendlinger_of_residualsV4Euler hloops hpocket hcases htwogon hcopy heuler hcellPinch hfaces
      hpinch)
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed

/-- **`thm:torsion-free` at Osin's notion**, over the V4 Euler residuals. -/
theorem manuscriptTorsionFreeTheoremOsin_of_residualsV4Euler :
    TorsionFreeOsinNotion.PrintedTorsionFreeTheoremOsin :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptTorsionFreeTheoremOsin_of_hullLeaves
    (greendlinger_of_residualsV4Euler hloops hpocket hcases htwogon hcopy heuler hcellPinch hfaces
      hpinch)
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed

/-- **`thm:torsion-free` at the limit-set notion**, over the V4 Euler residuals. -/
theorem printedTorsionFreeTheoremLimitSet_of_residualsV4Euler :
    TorsionFreeLimitSetNotion.PrintedTorsionFreeTheoremLimitSet :=
  TorsionFreeGreendlingerLeaf.printedTorsionFreeTheoremLimitSet_of_greendlinger
    (greendlinger_of_residualsV4Euler hloops hpocket hcases htwogon hcopy heuler hcellPinch hfaces
      hpinch)

/-- **`cor:regular-nonmf-algebra`, along the printed proof**, over the V4 Euler residuals. -/
theorem manuscriptRegularNonMFAlgebra_of_residualsV4Euler :
    TorsionFreePrinted.PrintedRegularNonMFAlgebra :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptRegularNonMFAlgebra_of_hullLeaves
    (greendlinger_of_residualsV4Euler hloops hpocket hcases htwogon hcopy heuler hcellPinch hfaces
      hpinch)
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed
    TorsionFreeSectionAssembly.simpleUniqueTraceAtHypEmbedded_closed
    TorsionFreePrinted.gerasimovaOsinTheorem11Printed

/-- **`cor:regular-nonmf-algebra` at Osin's notion**, over the V4 Euler residuals. -/
theorem manuscriptRegularNonMFAlgebraOsin_of_residualsV4Euler :
    TorsionFreeOsinNotion.PrintedRegularNonMFAlgebraOsin :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptRegularNonMFAlgebraOsin_of_hullLeaves
    (greendlinger_of_residualsV4Euler hloops hpocket hcases htwogon hcopy heuler hcellPinch hfaces
      hpinch)
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed
    TorsionFreeSectionAssembly.simpleUniqueTraceAtHypEmbedded_closed
    TorsionFreePrinted.gerasimovaOsinTheorem11Printed

/-- **`cor:regular-nonmf-algebra` at the limit-set notion**, over the V4 Euler residuals. -/
theorem printedRegularNonMFAlgebraLimitSet_of_residualsV4Euler :
    TorsionFreeLimitSetNotion.PrintedRegularNonMFAlgebraLimitSet :=
  TorsionFreeGreendlingerLeaf.printedRegularNonMFAlgebraLimitSet_of_greendlinger
    (greendlinger_of_residualsV4Euler hloops hpocket hcases htwogon hcopy heuler hcellPinch hfaces
      hpinch)

/-- **`thm:hull`, as printed** (tex line 1636), over the V4 Euler residuals. -/
theorem printedHullTheorem_of_residualsV4Euler :
    TorsionFreeSectionSentences.PrintedHullSmallCancellationCurrent.{0} :=
  TorsionFreeGreendlingerLeaf.printedHullTheorem_of_greendlinger
    (greendlinger_of_residualsV4Euler hloops hpocket hcases htwogon hcopy heuler hcellPinch hfaces
      hpinch)

/-- **`thm:hull` at Osin's notion**, over the V4 Euler residuals. -/
theorem printedHullTheoremOsin_of_residualsV4Euler :
    TorsionFreeOsinNotion.PrintedHullSmallCancellationOsin :=
  TorsionFreeGreendlingerLeaf.printedHullTheoremOsin_of_greendlinger
    (greendlinger_of_residualsV4Euler hloops hpocket hcases htwogon hcopy heuler hcellPinch hfaces
      hpinch)

/-- **`thm:hull` at the limit-set notion**, over the V4 Euler residuals. -/
theorem printedHullTheoremLimitSet_of_residualsV4Euler :
    TorsionFreeLimitSetNotion.PrintedHullSmallCancellationLimitSet :=
  TorsionFreeGreendlingerLeaf.printedHullTheoremLimitSet_of_greendlinger
    (greendlinger_of_residualsV4Euler hloops hpocket hcases htwogon hcopy heuler hcellPinch hfaces
      hpinch)

/-- **`thm:hull` at a torsion-free ambient group**, over the V4 Euler residuals. -/
theorem hullSmallCancellationTorsionFreePrinted_of_residualsV4Euler :
    TorsionFreePrinted.HullSmallCancellationTorsionFreePrinted.{0} :=
  TorsionFreeGreendlingerLeaf.hullSmallCancellationTorsionFreePrinted_of_greendlinger
    (greendlinger_of_residualsV4Euler hloops hpocket hcases htwogon hcopy heuler hcellPinch hfaces
      hpinch)

/-- **The paragraph after `thm:hull`** (tex 1644–1648), over the V4 Euler residuals. -/
theorem printedHullProofParagraph_of_residualsV4Euler :
    TorsionFreeSectionSentencesFourLeaves.PrintedHullProofParagraph :=
  TorsionFreeGreendlingerLeaf.printedHullProofParagraph_of_greendlinger
    (greendlinger_of_residualsV4Euler hloops hpocket hcases htwogon hcopy heuler hcellPinch hfaces
      hpinch)

/-- **`lem:saturation`, as printed**, over the V4 Euler residuals. -/
theorem printedSaturation_of_residualsV4Euler : TorsionFreePrinted.PrintedSaturationNoOmega.{0} :=
  TorsionFreeGreendlingerLeaf.printedSaturation_of_greendlinger
    (greendlinger_of_residualsV4Euler hloops hpocket hcases htwogon hcopy heuler hcellPinch hfaces
      hpinch)

/-- **`lem:saturation` at Osin's notion**, over the V4 Euler residuals. -/
theorem printedSaturationOsin_of_residualsV4Euler : TorsionFreeOsinNotion.PrintedSaturationOsin :=
  TorsionFreeGreendlingerLeaf.printedSaturationOsin_of_greendlinger
    (greendlinger_of_residualsV4Euler hloops hpocket hcases htwogon hcopy heuler hcellPinch hfaces
      hpinch)

/-- **`lem:saturation` at the limit-set notion**, over the V4 Euler residuals. -/
theorem printedSaturationLimitSet_of_residualsV4Euler :
    TorsionFreeLimitSetNotion.PrintedSaturationLimitSet :=
  TorsionFreeGreendlingerLeaf.printedSaturationLimitSet_of_greendlinger
    (greendlinger_of_residualsV4Euler hloops hpocket hcases htwogon hcopy heuler hcellPinch hfaces
      hpinch)

/-- **The Hull 5.7 and 5.8 pair and "Hull's theorem again applies"**, over the V4 Euler residuals. -/
theorem printedSaturationPairAndHullAgain_of_residualsV4Euler :
    TorsionFreeSectionSentencesFourLeaves.PrintedSaturationPairAndHullAgain :=
  TorsionFreeGreendlingerLeaf.printedSaturationPairAndHullAgain_of_greendlinger
    (greendlinger_of_residualsV4Euler hloops hpocket hcases htwogon hcopy heuler hcellPinch hfaces
      hpinch)

/-- **Applying `thm:hull` to `N₀`** in the proof of `lem:saturation`, over the V4 Euler residuals. -/
theorem printedSaturationApplyHull_of_residualsV4Euler :
    TorsionFreeSectionSentencesFourLeaves.PrintedSaturationApplyHull :=
  TorsionFreeGreendlingerLeaf.printedSaturationApplyHull_of_greendlinger
    (greendlinger_of_residualsV4Euler hloops hpocket hcases htwogon hcopy heuler hcellPinch hfaces
      hpinch)

/-- **Applying `lem:saturation` to `G₀` and `N`**, over the V4 Euler residuals. -/
theorem printedTheoremApplySaturation_of_residualsV4Euler :
    TorsionFreeSectionSentencesFourLeaves.PrintedTheoremApplySaturation :=
  TorsionFreeGreendlingerLeaf.printedTheoremApplySaturation_of_greendlinger
    (greendlinger_of_residualsV4Euler hloops hpocket hcases htwogon hcopy heuler hcellPinch hfaces
      hpinch)

/-- **The Fournier-Facio paragraph** (tex 1675–1685), over the V4 Euler residuals. -/
theorem fournierFacioParagraph_of_residualsV4Euler : TorsionFreePrinted.FournierFacioParagraph :=
  TorsionFreeGreendlingerLeaf.fournierFacioParagraph_of_greendlinger
    (greendlinger_of_residualsV4Euler hloops hpocket hcases htwogon hcopy heuler hcellPinch hfaces
      hpinch)

/-- **`G₀` as a Hull Corollary 7.4 common quotient**, over the V4 Euler residuals. -/
theorem hullCommonQuotientPrinted_of_residualsV4Euler : TorsionFreePrinted.HullCommonQuotientPrinted :=
  TorsionFreeGreendlingerSentences.manuscriptSentence_hullCommonQuotient_of_greendlinger
    (greendlinger_of_residualsV4Euler hloops hpocket hcases htwogon hcopy heuler hcellPinch hfaces
      hpinch)

/-- **Hull's Corollary 7.4 at the printed generality**, over the V4 Euler residuals. -/
theorem printedHullCorollary74_of_residualsV4Euler : HullCorollary74.PrintedHullCorollary74 :=
  HullCorollary74.printedHullCorollary74_of_greendlinger
    (greendlinger_of_residualsV4Euler hloops hpocket hcases htwogon hcopy heuler hcellPinch hfaces
      hpinch)

end Residuals

end TorsionFreeResidualsV4Euler
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4Euler.greendlinger_of_residualsV4Euler
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4Euler.manuscriptTorsionFreeTheorem_of_residualsV4Euler
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4Euler.manuscriptTorsionFreeFullMFRadical_of_residualsV4Euler
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4Euler.manuscriptTorsionFreeTheoremOsin_of_residualsV4Euler
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4Euler.printedTorsionFreeTheoremLimitSet_of_residualsV4Euler
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4Euler.manuscriptRegularNonMFAlgebra_of_residualsV4Euler
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4Euler.manuscriptRegularNonMFAlgebraOsin_of_residualsV4Euler
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4Euler.printedRegularNonMFAlgebraLimitSet_of_residualsV4Euler
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4Euler.printedHullTheorem_of_residualsV4Euler
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4Euler.printedHullTheoremOsin_of_residualsV4Euler
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4Euler.printedHullTheoremLimitSet_of_residualsV4Euler
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4Euler.hullSmallCancellationTorsionFreePrinted_of_residualsV4Euler
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4Euler.printedHullProofParagraph_of_residualsV4Euler
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4Euler.printedSaturation_of_residualsV4Euler
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4Euler.printedSaturationOsin_of_residualsV4Euler
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4Euler.printedSaturationLimitSet_of_residualsV4Euler
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4Euler.printedSaturationPairAndHullAgain_of_residualsV4Euler
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4Euler.printedSaturationApplyHull_of_residualsV4Euler
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4Euler.printedTheoremApplySaturation_of_residualsV4Euler
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4Euler.fournierFacioParagraph_of_residualsV4Euler
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4Euler.hullCommonQuotientPrinted_of_residualsV4Euler
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV4Euler.printedHullCorollary74_of_residualsV4Euler
