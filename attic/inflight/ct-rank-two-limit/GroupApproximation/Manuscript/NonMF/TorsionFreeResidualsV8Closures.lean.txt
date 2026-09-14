import GroupApproximation.GGT.VanKampen.Estimating.OsinGreendlingerWaistV8Closures
import GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV2Copy
import GroupApproximation.Meta.AxiomGuard

/-!
# The top of `sec:torsion-free` over the ten leaf residuals of the V8 waist with closures

`non_mf_groups_exist.tex`, `sec:torsion-free`: the endpoints of `TorsionFreeResidualsV8Closures`, restated
additively over the ten named leaf residuals of
`GGT.VanKampen.relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV8Closures`:
`OsinLemma94ClassEndLoopsBudgetInput`, `SameCellPocketLoopCutStatement`,
`EnclosedSubdiagramLoopCutSuccStatement`, `OsinLemma94ClassCaseGapSpanStatement`,
`OsinTwoGonCleanCopySectionStatement`, `CellPocketOuterPinchStepSectionDistinctStatement`,
`CellPocketWalkProperArcsBelowSectionStatement`, `OsinSectionPocketFaceSetProperSectionStatement`,
`OsinSectionPocketFaceSetWholeSectionTwoArcSectionStatement` and `PocketOuterPinchStepSectionStatement`
(at `.{0, 0, 0}`).  Against `TorsionFreeResidualsV8Closures`, the successor-form enclosed subdiagram and the
two-gon decomposition Euler equalities are proved.  The closed walls are applied as in
`TorsionFreeResidualsV2Copy`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreeResidualsV8Closures

open GGT.VanKampen

section Residuals

variable (hbudget : OsinLemma94ClassEndLoopsBudgetInput.{0, 0, 0})
  (hcut : SameCellPocketLoopCutStatement.{0, 0, 0})
  (hloop : EnclosedSubdiagramLoopCutSuccStatement.{0, 0, 0})
  (hspan : OsinLemma94ClassCaseGapSpanStatement.{0, 0, 0})
  (htwocopy : OsinTwoGonCleanCopySectionStatement.{0, 0, 0})
  (hcellStep : CellPocketOuterPinchStepSectionDistinctStatement.{0, 0, 0})
  (hproper : CellPocketWalkProperArcsBelowSectionStatement.{0, 0, 0})
  (hfaces : OsinSectionPocketFaceSetProperSectionStatement.{0, 0, 0})
  (hwhole : OsinSectionPocketFaceSetWholeSectionTwoArcSectionStatement.{0, 0, 0})
  (hstep : PocketOuterPinchStepSectionStatement.{0, 0, 0})

include hbudget hcut hloop hspan htwocopy hcellStep hproper hfaces hwhole hstep

/-- Osin's Lemma 4.4 at least-area diagrams, from the ten leaf residuals of the V8 waist with closures. -/
theorem greendlinger_of_residualsV8Closures : RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV8Closures hbudget hcut hloop hspan
    htwocopy hcellStep hproper hfaces hwhole hstep

/-- **`thm:torsion-free`, exactly as printed** (tex line 284), and the abstract's torsion-free
clause, over the leaf residuals. -/
theorem manuscriptTorsionFreeTheorem_of_residualsV8Closures : TorsionFreePrinted.PrintedTorsionFreeTheorem :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptTorsionFreeTheorem_of_hullLeaves
    (greendlinger_of_residualsV8Closures hbudget hcut hloop hspan htwocopy hcellStep hproper
      hfaces hwhole hstep)
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed

/-- **`thm:torsion-free` in the radical form**, over the leaf residuals. -/
theorem manuscriptTorsionFreeFullMFRadical_of_residualsV8Closures :
    TheoremC.PrintedTorsionFreeFullMFRadical :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptTorsionFreeFullMFRadical_of_hullLeaves
    (greendlinger_of_residualsV8Closures hbudget hcut hloop hspan htwocopy hcellStep hproper
      hfaces hwhole hstep)
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed

/-- **`thm:torsion-free` at Osin's notion**, over the leaf residuals. -/
theorem manuscriptTorsionFreeTheoremOsin_of_residualsV8Closures :
    TorsionFreeOsinNotion.PrintedTorsionFreeTheoremOsin :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptTorsionFreeTheoremOsin_of_hullLeaves
    (greendlinger_of_residualsV8Closures hbudget hcut hloop hspan htwocopy hcellStep hproper
      hfaces hwhole hstep)
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed

/-- **`thm:torsion-free` at the limit-set notion**, over the leaf residuals. -/
theorem printedTorsionFreeTheoremLimitSet_of_residualsV8Closures :
    TorsionFreeLimitSetNotion.PrintedTorsionFreeTheoremLimitSet :=
  TorsionFreeGreendlingerLeaf.printedTorsionFreeTheoremLimitSet_of_greendlinger
    (greendlinger_of_residualsV8Closures hbudget hcut hloop hspan htwocopy hcellStep hproper
      hfaces hwhole hstep)

/-- **`cor:regular-nonmf-algebra`, along the printed proof**, over the leaf residuals. -/
theorem manuscriptRegularNonMFAlgebra_of_residualsV8Closures :
    TorsionFreePrinted.PrintedRegularNonMFAlgebra :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptRegularNonMFAlgebra_of_hullLeaves
    (greendlinger_of_residualsV8Closures hbudget hcut hloop hspan htwocopy hcellStep hproper
      hfaces hwhole hstep)
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed
    TorsionFreeSectionAssembly.simpleUniqueTraceAtHypEmbedded_closed
    TorsionFreePrinted.gerasimovaOsinTheorem11Printed

/-- **`cor:regular-nonmf-algebra` at Osin's notion**, over the leaf residuals. -/
theorem manuscriptRegularNonMFAlgebraOsin_of_residualsV8Closures :
    TorsionFreeOsinNotion.PrintedRegularNonMFAlgebraOsin :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptRegularNonMFAlgebraOsin_of_hullLeaves
    (greendlinger_of_residualsV8Closures hbudget hcut hloop hspan htwocopy hcellStep hproper
      hfaces hwhole hstep)
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed
    TorsionFreeSectionAssembly.simpleUniqueTraceAtHypEmbedded_closed
    TorsionFreePrinted.gerasimovaOsinTheorem11Printed

/-- **`cor:regular-nonmf-algebra` at the limit-set notion**, over the leaf residuals. -/
theorem printedRegularNonMFAlgebraLimitSet_of_residualsV8Closures :
    TorsionFreeLimitSetNotion.PrintedRegularNonMFAlgebraLimitSet :=
  TorsionFreeGreendlingerLeaf.printedRegularNonMFAlgebraLimitSet_of_greendlinger
    (greendlinger_of_residualsV8Closures hbudget hcut hloop hspan htwocopy hcellStep hproper
      hfaces hwhole hstep)

/-- **`thm:hull`, as printed** (tex line 1636), over the leaf residuals. -/
theorem printedHullTheorem_of_residualsV8Closures :
    TorsionFreeSectionSentences.PrintedHullSmallCancellationCurrent.{0} :=
  TorsionFreeGreendlingerLeaf.printedHullTheorem_of_greendlinger
    (greendlinger_of_residualsV8Closures hbudget hcut hloop hspan htwocopy hcellStep hproper
      hfaces hwhole hstep)

/-- **`thm:hull` at Osin's notion**, over the leaf residuals. -/
theorem printedHullTheoremOsin_of_residualsV8Closures :
    TorsionFreeOsinNotion.PrintedHullSmallCancellationOsin :=
  TorsionFreeGreendlingerLeaf.printedHullTheoremOsin_of_greendlinger
    (greendlinger_of_residualsV8Closures hbudget hcut hloop hspan htwocopy hcellStep hproper
      hfaces hwhole hstep)

/-- **`thm:hull` at the limit-set notion**, over the leaf residuals. -/
theorem printedHullTheoremLimitSet_of_residualsV8Closures :
    TorsionFreeLimitSetNotion.PrintedHullSmallCancellationLimitSet :=
  TorsionFreeGreendlingerLeaf.printedHullTheoremLimitSet_of_greendlinger
    (greendlinger_of_residualsV8Closures hbudget hcut hloop hspan htwocopy hcellStep hproper
      hfaces hwhole hstep)

/-- **`thm:hull` at a torsion-free ambient group**, over the leaf residuals. -/
theorem hullSmallCancellationTorsionFreePrinted_of_residualsV8Closures :
    TorsionFreePrinted.HullSmallCancellationTorsionFreePrinted.{0} :=
  TorsionFreeGreendlingerLeaf.hullSmallCancellationTorsionFreePrinted_of_greendlinger
    (greendlinger_of_residualsV8Closures hbudget hcut hloop hspan htwocopy hcellStep hproper
      hfaces hwhole hstep)

/-- **The paragraph after `thm:hull`** (tex 1644–1648), over the leaf residuals. -/
theorem printedHullProofParagraph_of_residualsV8Closures :
    TorsionFreeSectionSentencesFourLeaves.PrintedHullProofParagraph :=
  TorsionFreeGreendlingerLeaf.printedHullProofParagraph_of_greendlinger
    (greendlinger_of_residualsV8Closures hbudget hcut hloop hspan htwocopy hcellStep hproper
      hfaces hwhole hstep)

/-- **`lem:saturation`, as printed**, over the leaf residuals. -/
theorem printedSaturation_of_residualsV8Closures : TorsionFreePrinted.PrintedSaturationNoOmega.{0} :=
  TorsionFreeGreendlingerLeaf.printedSaturation_of_greendlinger
    (greendlinger_of_residualsV8Closures hbudget hcut hloop hspan htwocopy hcellStep hproper
      hfaces hwhole hstep)

/-- **`lem:saturation` at Osin's notion**, over the leaf residuals. -/
theorem printedSaturationOsin_of_residualsV8Closures : TorsionFreeOsinNotion.PrintedSaturationOsin :=
  TorsionFreeGreendlingerLeaf.printedSaturationOsin_of_greendlinger
    (greendlinger_of_residualsV8Closures hbudget hcut hloop hspan htwocopy hcellStep hproper
      hfaces hwhole hstep)

/-- **`lem:saturation` at the limit-set notion**, over the leaf residuals. -/
theorem printedSaturationLimitSet_of_residualsV8Closures :
    TorsionFreeLimitSetNotion.PrintedSaturationLimitSet :=
  TorsionFreeGreendlingerLeaf.printedSaturationLimitSet_of_greendlinger
    (greendlinger_of_residualsV8Closures hbudget hcut hloop hspan htwocopy hcellStep hproper
      hfaces hwhole hstep)

/-- **The Hull 5.7 and 5.8 pair and "Hull's theorem again applies"**, over the leaf residuals. -/
theorem printedSaturationPairAndHullAgain_of_residualsV8Closures :
    TorsionFreeSectionSentencesFourLeaves.PrintedSaturationPairAndHullAgain :=
  TorsionFreeGreendlingerLeaf.printedSaturationPairAndHullAgain_of_greendlinger
    (greendlinger_of_residualsV8Closures hbudget hcut hloop hspan htwocopy hcellStep hproper
      hfaces hwhole hstep)

/-- **Applying `thm:hull` to `N₀`** in the proof of `lem:saturation`, over the leaf residuals. -/
theorem printedSaturationApplyHull_of_residualsV8Closures :
    TorsionFreeSectionSentencesFourLeaves.PrintedSaturationApplyHull :=
  TorsionFreeGreendlingerLeaf.printedSaturationApplyHull_of_greendlinger
    (greendlinger_of_residualsV8Closures hbudget hcut hloop hspan htwocopy hcellStep hproper
      hfaces hwhole hstep)

/-- **Applying `lem:saturation` to `G₀` and `N`**, over the leaf residuals. -/
theorem printedTheoremApplySaturation_of_residualsV8Closures :
    TorsionFreeSectionSentencesFourLeaves.PrintedTheoremApplySaturation :=
  TorsionFreeGreendlingerLeaf.printedTheoremApplySaturation_of_greendlinger
    (greendlinger_of_residualsV8Closures hbudget hcut hloop hspan htwocopy hcellStep hproper
      hfaces hwhole hstep)

/-- **The Fournier-Facio paragraph** (tex 1675–1685), over the leaf residuals. -/
theorem fournierFacioParagraph_of_residualsV8Closures : TorsionFreePrinted.FournierFacioParagraph :=
  TorsionFreeGreendlingerLeaf.fournierFacioParagraph_of_greendlinger
    (greendlinger_of_residualsV8Closures hbudget hcut hloop hspan htwocopy hcellStep hproper
      hfaces hwhole hstep)

/-- **`G₀` as a Hull Corollary 7.4 common quotient**, over the leaf residuals. -/
theorem hullCommonQuotientPrinted_of_residualsV8Closures : TorsionFreePrinted.HullCommonQuotientPrinted :=
  TorsionFreeGreendlingerSentences.manuscriptSentence_hullCommonQuotient_of_greendlinger
    (greendlinger_of_residualsV8Closures hbudget hcut hloop hspan htwocopy hcellStep hproper
      hfaces hwhole hstep)

/-- **Hull's Corollary 7.4 at the printed generality**, over the leaf residuals. -/
theorem printedHullCorollary74_of_residualsV8Closures : HullCorollary74.PrintedHullCorollary74 :=
  HullCorollary74.printedHullCorollary74_of_greendlinger
    (greendlinger_of_residualsV8Closures hbudget hcut hloop hspan htwocopy hcellStep hproper
      hfaces hwhole hstep)

end Residuals

end TorsionFreeResidualsV8Closures
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV8Closures.greendlinger_of_residualsV8Closures
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV8Closures.manuscriptTorsionFreeTheorem_of_residualsV8Closures
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV8Closures.manuscriptTorsionFreeFullMFRadical_of_residualsV8Closures
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV8Closures.manuscriptTorsionFreeTheoremOsin_of_residualsV8Closures
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV8Closures.printedTorsionFreeTheoremLimitSet_of_residualsV8Closures
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV8Closures.manuscriptRegularNonMFAlgebra_of_residualsV8Closures
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV8Closures.manuscriptRegularNonMFAlgebraOsin_of_residualsV8Closures
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV8Closures.printedRegularNonMFAlgebraLimitSet_of_residualsV8Closures
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV8Closures.printedHullTheorem_of_residualsV8Closures
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV8Closures.printedHullTheoremOsin_of_residualsV8Closures
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV8Closures.printedHullTheoremLimitSet_of_residualsV8Closures
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV8Closures.hullSmallCancellationTorsionFreePrinted_of_residualsV8Closures
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV8Closures.printedHullProofParagraph_of_residualsV8Closures
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV8Closures.printedSaturation_of_residualsV8Closures
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV8Closures.printedSaturationOsin_of_residualsV8Closures
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV8Closures.printedSaturationLimitSet_of_residualsV8Closures
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV8Closures.printedSaturationPairAndHullAgain_of_residualsV8Closures
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV8Closures.printedSaturationApplyHull_of_residualsV8Closures
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV8Closures.printedTheoremApplySaturation_of_residualsV8Closures
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV8Closures.fournierFacioParagraph_of_residualsV8Closures
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV8Closures.hullCommonQuotientPrinted_of_residualsV8Closures
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV8Closures.printedHullCorollary74_of_residualsV8Closures
