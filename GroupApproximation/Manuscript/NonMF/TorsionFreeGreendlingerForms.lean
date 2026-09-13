import GroupApproximation.GGT.HullSCLemma51EmbeddedBridgeHolds
import GroupApproximation.GGT.OsinLimitSetSpelling
import GroupApproximation.GGT.RelHypProp23FromLeastAreaLeaves
import GroupApproximation.GroupTheory.HydeLodha.FinitelyPresentedInfiniteSimpleClosed
import GroupApproximation.Kazhdan.KotowskiOllivierClosed
import GroupApproximation.Manuscript.NonMF.TorsionFreeHullPrintedLeastArea
import GroupApproximation.Manuscript.NonMF.TorsionFreeLeastAreaAssembly
import GroupApproximation.Manuscript.NonMF.TorsionFreeLimitSetEndpoints
import GroupApproximation.Manuscript.NonMF.TorsionFreeLimitSetNotion
import GroupApproximation.Manuscript.NonMF.TorsionFreeLiteratureInputsLeastArea
import GroupApproximation.Manuscript.NonMF.TorsionFreeOsinNotion
import GroupApproximation.Manuscript.NonMF.TorsionFreeSectionAssemblyClosedGO
import GroupApproximation.Meta.AxiomGuard

/-!
# `sec:torsion-free` endpoints over the least-area Greendlinger leaf alone

The endpoints of `sec:torsion-free` over the least-area leaves, in
`RelHypProp23FromLeastAreaLeaves`, `TorsionFreeLiteratureInputsLeastArea`,
`TorsionFreeLeastAreaAssembly`, `TorsionFreeOsinNotion`, `TorsionFreeHullPrintedLeastArea`,
`TorsionFreeLimitSetNotion`, `TorsionFreeLimitSetEndpoints` and
`TorsionFreeSectionAssemblyClosedGO`, take the Greendlinger waist `hgreendlinger`, the embedded
bridge `hbridge` and, depending on the form, the inputs `hFFF`, `hKO`, `hW`, `hDGO`, `hGO` and
the hard direction of Osin's Theorem 1.1.  All but the waist are proved:
* `hbridge`: `HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed`;
* `hKO`: `KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed`;
* `hW`: `HydeLodha.finitelyPresentedInfiniteSimple_closed`;
* `hFFF`: `fournierFacioParagraph_of_greendlinger` below;
* `hDGO` and `hGO`: supplied inside `TorsionFreeSectionAssemblyClosedGO`;
* Osin's Theorem 1.1: `GGT.OsinClassification.isAcylindricallyHyperbolicOsin_of_limitSet`.

Each form applies them, so it stands over `hgreendlinger` alone.  One form is given per printed
statement, and the least-area routes that reach the same statement share it.  The sentences over
the same leaf are in `TorsionFreeGreendlingerSentences`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreeGreendlingerForms

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted

/-! ## The Fournier-Facio paragraph -/

/-- **Fournier-Facio's Proposition 2.3, the manuscript quotient field** (tex lines 1675–1680,
`\cite[\S2]{FFF}`, before the proof of `\label{thm:torsion-free}`), over the least-area
Greendlinger leaf alone. -/
theorem fournierFacioQuotientStatement_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TheoremC.FournierFacioQuotientStatement :=
  GGT.RelHyp.fournierFacioQuotientStatement_of_leastAreaLeaves hgreendlinger
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed

/-- **Hull's Corollary 7.4, in the form the Fournier-Facio paragraph uses** (tex lines 1680–1683,
"as a common quotient of two finitely generated acylindrically hyperbolic groups by Hull's
theorem"), over the least-area Greendlinger leaf alone. -/
theorem hullCommonQuotient_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TheoremC.HullCommonQuotientStatement :=
  HullSC.hullCommonQuotient_of_leastAreaLeaves hgreendlinger
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed

/-- **The five literature inputs of the Fournier-Facio paragraph** (tex lines 1675–1683, before
the proof of `\label{thm:torsion-free}`), over the least-area Greendlinger leaf alone. -/
theorem literatureInputs_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TheoremC.LiteratureInputs :=
  TorsionFreeLiteratureInputsLeastArea.literatureInputs_of_leastAreaLeaves hgreendlinger
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed

/-- **The Fournier-Facio paragraph** (tex lines 1675–1685, before the proof of
`\label{thm:torsion-free}`), over the least-area Greendlinger leaf alone. -/
theorem fournierFacioParagraph_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    FournierFacioParagraph :=
  TorsionFreeLiteratureInputsLeastArea.fournierFacioParagraph_of_leastAreaLeaves hgreendlinger
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed

/-! ## `thm:hull` and `lem:saturation` -/

/-- **`thm:hull` as printed, at every acylindrically hyperbolic group** (tex lines 1636–1642,
`\label{thm:hull}`), over the least-area Greendlinger leaf alone. -/
theorem manuscriptSentence_hullTheorem_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreeSectionSentences.PrintedHullSmallCancellationCurrent.{0} :=
  TorsionFreeHullPrintedLeastArea.manuscriptSentence_hullTheorem_of_leastAreaLeaves hgreendlinger
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed

/-- **`thm:hull` as printed, at Osin's notion** (tex lines 1636–1642, `\label{thm:hull}`), over
the least-area Greendlinger leaf alone. -/
theorem manuscriptSentence_hullTheoremOsin_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreeOsinNotion.PrintedHullSmallCancellationOsin :=
  TorsionFreeHullPrintedLeastArea.manuscriptSentence_hullTheoremOsin_of_leastAreaLeaves
    hgreendlinger HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed

/-- **`thm:hull` at the limit-set notion** (tex lines 1636–1642, `\label{thm:hull}`), over the
least-area Greendlinger leaf alone. -/
theorem manuscriptHullTheoremLimitSet_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreeLimitSetNotion.PrintedHullSmallCancellationLimitSet :=
  TorsionFreeLimitSetEndpoints.manuscriptHullTheoremLimitSet_of_leastAreaLeaves hgreendlinger
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed

/-- **`thm:hull` at a torsion-free ambient group** (tex lines 1636–1642, `\label{thm:hull}`),
over the least-area Greendlinger leaf alone. -/
theorem hullSmallCancellationTorsionFreePrinted_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    HullSmallCancellationTorsionFreePrinted.{0} :=
  TorsionFreeLeastAreaAssembly.hullSmallCancellationTorsionFreePrinted_of_leastAreaLeaves
    hgreendlinger HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed

/-- **`lem:saturation` as printed** (tex lines 1650–1656, `\label{lem:saturation}`), over the
least-area Greendlinger leaf alone. -/
theorem printedSaturationNoOmega_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    PrintedSaturationNoOmega.{0} :=
  TorsionFreeLeastAreaAssembly.printedSaturationNoOmega_of_leastAreaLeaves hgreendlinger
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed

/-- **`lem:saturation` at Osin's notion** (tex lines 1650–1656, `\label{lem:saturation}`), over
the least-area Greendlinger leaf alone. -/
theorem manuscriptSaturationOsin_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreeOsinNotion.PrintedSaturationOsin :=
  TorsionFreeOsinNotion.manuscriptSaturationOsin_of_leastAreaLeaves hgreendlinger
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed

/-- **`lem:saturation` at the limit-set notion** (tex lines 1650–1656, `\label{lem:saturation}`),
over the least-area Greendlinger leaf alone.  The hard direction of Osin's Theorem 1.1 is a
theorem. -/
theorem manuscriptSaturationLimitSet_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreeLimitSetNotion.PrintedSaturationLimitSet :=
  TorsionFreeLimitSetEndpoints.manuscriptSaturationLimitSet_of_leastAreaLeaves
    GGT.OsinClassification.isAcylindricallyHyperbolicOsin_of_limitSet hgreendlinger
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed

/-! ## `thm:torsion-free` and `cor:regular-nonmf-algebra` -/

/-- **`thm:torsion-free`, exactly as printed** (tex line 284, `\label{thm:torsion-free}`), over
the least-area Greendlinger leaf alone. -/
theorem manuscriptTorsionFreeTheorem_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    PrintedTorsionFreeTheorem :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptTorsionFreeTheorem_of_hullLeaves hgreendlinger
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed

/-- **`thm:torsion-free` at Osin's notion** (tex line 284, `\label{thm:torsion-free}`), over the
least-area Greendlinger leaf alone. -/
theorem manuscriptTorsionFreeTheoremOsin_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreeOsinNotion.PrintedTorsionFreeTheoremOsin :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptTorsionFreeTheoremOsin_of_hullLeaves
    hgreendlinger HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed

/-- **`thm:torsion-free` at the limit-set notion** (tex line 284, `\label{thm:torsion-free}`),
over the least-area Greendlinger leaf alone. -/
theorem manuscriptTorsionFreeTheoremLimitSet_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreeLimitSetNotion.PrintedTorsionFreeTheoremLimitSet :=
  TorsionFreeLimitSetEndpoints.manuscriptTorsionFreeTheoremLimitSet_of_hullLeaves hgreendlinger
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed

/-- **`cor:regular-nonmf-algebra`, along the printed proof** (tex lines 1718–1722,
`\label{cor:regular-nonmf-algebra}`), over the least-area Greendlinger leaf alone. -/
theorem manuscriptRegularNonMFAlgebra_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    PrintedRegularNonMFAlgebra :=
  TorsionFreeSectionAssembly.manuscriptRegularNonMFAlgebra_of_hullLeaves_closedGO hgreendlinger
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed

/-- **`cor:regular-nonmf-algebra` at Osin's notion** (tex lines 1718–1722,
`\label{cor:regular-nonmf-algebra}`), over the least-area Greendlinger leaf alone. -/
theorem manuscriptRegularNonMFAlgebraOsin_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreeOsinNotion.PrintedRegularNonMFAlgebraOsin :=
  TorsionFreeSectionAssembly.manuscriptRegularNonMFAlgebraOsin_of_hullLeaves_closedGO
    hgreendlinger HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed

/-- **`cor:regular-nonmf-algebra` at the limit-set notion** (tex lines 1718–1722,
`\label{cor:regular-nonmf-algebra}`), over the least-area Greendlinger leaf alone. -/
theorem manuscriptRegularNonMFAlgebraLimitSet_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreeLimitSetNotion.PrintedRegularNonMFAlgebraLimitSet :=
  TorsionFreeSectionAssembly.manuscriptRegularNonMFAlgebraLimitSet_of_hullLeaves_closedGO
    hgreendlinger HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed

end TorsionFreeGreendlingerForms
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.fournierFacioQuotientStatement_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.hullCommonQuotient_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.literatureInputs_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.fournierFacioParagraph_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.manuscriptSentence_hullTheorem_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.manuscriptSentence_hullTheoremOsin_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.manuscriptHullTheoremLimitSet_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.hullSmallCancellationTorsionFreePrinted_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.printedSaturationNoOmega_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.manuscriptSaturationOsin_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.manuscriptSaturationLimitSet_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.manuscriptTorsionFreeTheorem_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.manuscriptTorsionFreeTheoremOsin_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.manuscriptTorsionFreeTheoremLimitSet_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.manuscriptRegularNonMFAlgebra_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.manuscriptRegularNonMFAlgebraOsin_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.manuscriptRegularNonMFAlgebraLimitSet_of_greendlinger
