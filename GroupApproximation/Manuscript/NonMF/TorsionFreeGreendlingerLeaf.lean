import GroupApproximation.Manuscript.NonMF.TorsionFreeFourLeaves
import GroupApproximation.Manuscript.NonMF.TorsionFreeSectionSentencesFourLeaves
import GroupApproximation.GGT.HullSCLemma51EmbeddedBridgeHolds
import GroupApproximation.GroupTheory.HydeLodha.FinitelyPresentedInfiniteSimpleClosed
import GroupApproximation.Kazhdan.KotowskiOllivierClosed
import GroupApproximation.Meta.AxiomGuard

/-!
# `sec:torsion-free` over the least-area Greendlinger waist alone

`TorsionFreeFourLeaves` and `TorsionFreeSectionSentencesFourLeaves` state the printed endpoints
and proof-step sentences of `sec:torsion-free` over four walls.  Three of these walls are now
theorems:

* `HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement`, Osin's Lemma 5.1 in the
  embedded form: `HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed`;
* `TheoremC.KotowskiOllivierStatement`, an infinite, finitely presented, torsion-free hyperbolic
  group with property (T): `KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed`, from
  `GHB(7)`;
* `TorsionFreePrinted.FinitelyPresentedInfiniteSimpleStatement`, a finitely presented,
  torsion-free, infinite simple group: `HydeLodha.finitelyPresentedInfiniteSimple_closed`,
  Hyde–Lodha's `Q₂`.

Each theorem below applies the matching `_of_fourLeaves` theorem to these producers.  So its one
binder is `hgreendlinger : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement`,
Osin's Lemma 4.4 at least-area diagrams, the Greendlinger waist of Hull's Theorem 7.1.

## Manuscript status

Every theorem here still takes `hgreendlinger`, so none of them closes its sentence.  Once
`hgreendlinger` has a closed producer, each endpoint is closed by applying it.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreeGreendlingerLeaf

/-! ## `thm:hull` and `lem:saturation` -/

/-- **`thm:hull` as printed, at every acylindrically hyperbolic group**, at Hull's Cayley-graph
notion (line 1636, `\label{thm:hull}`). -/
theorem printedHullTheorem_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreeSectionSentences.PrintedHullSmallCancellationCurrent.{0} :=
  TorsionFreeFourLeaves.printedHullTheorem_of_fourLeaves hgreendlinger
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed

/-- **`thm:hull` at Osin's notion** (line 1636, `\label{thm:hull}`). -/
theorem printedHullTheoremOsin_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreeOsinNotion.PrintedHullSmallCancellationOsin :=
  TorsionFreeFourLeaves.printedHullTheoremOsin_of_fourLeaves hgreendlinger
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed

/-- **`thm:hull` at the limit-set notion** (line 1636, `\label{thm:hull}`). -/
theorem printedHullTheoremLimitSet_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreeLimitSetNotion.PrintedHullSmallCancellationLimitSet :=
  TorsionFreeFourLeaves.printedHullTheoremLimitSet_of_fourLeaves hgreendlinger
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed

/-- **`thm:hull` at a torsion-free ambient group**, the form the proof of `lem:saturation`
applies (line 1665). -/
theorem hullSmallCancellationTorsionFreePrinted_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreePrinted.HullSmallCancellationTorsionFreePrinted.{0} :=
  TorsionFreeFourLeaves.hullSmallCancellationTorsionFreePrinted_of_fourLeaves hgreendlinger
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed

/-- **`lem:saturation` as printed** (line 1650, `\label{lem:saturation}`). -/
theorem printedSaturation_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreePrinted.PrintedSaturationNoOmega.{0} :=
  TorsionFreeFourLeaves.printedSaturation_of_fourLeaves hgreendlinger
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed

/-- **`lem:saturation` at Osin's notion** (line 1650, `\label{lem:saturation}`). -/
theorem printedSaturationOsin_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreeOsinNotion.PrintedSaturationOsin :=
  TorsionFreeFourLeaves.printedSaturationOsin_of_fourLeaves hgreendlinger
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed

/-- **`lem:saturation` at the limit-set notion** (line 1650, `\label{lem:saturation}`). -/
theorem printedSaturationLimitSet_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreeLimitSetNotion.PrintedSaturationLimitSet :=
  TorsionFreeFourLeaves.printedSaturationLimitSet_of_fourLeaves hgreendlinger
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed

/-! ## The Fournier-Facio paragraph (lines 1675–1685) -/

/-- **Hull's Corollary 7.4, in the form the Fournier-Facio paragraph uses** (line 1680). -/
theorem hullCommonQuotient_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TheoremC.HullCommonQuotientStatement :=
  TorsionFreeFourLeaves.hullCommonQuotient_of_fourLeaves hgreendlinger
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed

/-- **The small cancellation quotient of the Fournier-Facio construction**, the
`smallCancellationQuotient` field of `TheoremC.LiteratureInputs`. -/
theorem fournierFacioQuotient_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TheoremC.FournierFacioQuotientStatement :=
  TorsionFreeFourLeaves.fournierFacioQuotient_of_fourLeaves hgreendlinger
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed

/-- **The literature inputs of the Fournier-Facio paragraph**, `TheoremC.LiteratureInputs`. -/
theorem literatureInputs_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TheoremC.LiteratureInputs :=
  TorsionFreeFourLeaves.literatureInputs_of_fourLeaves hgreendlinger
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed

/-- **The configuration of the Fournier-Facio paragraph**, `TheoremC.Configuration` (line 1680). -/
theorem configuration_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    Nonempty TheoremC.Configuration :=
  TorsionFreeFourLeaves.configuration_of_fourLeaves hgreendlinger
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed

/-- **The Fournier-Facio paragraph, as printed** (line 1675). -/
theorem fournierFacioParagraph_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreePrinted.FournierFacioParagraph :=
  TorsionFreeFourLeaves.fournierFacioParagraph_of_fourLeaves hgreendlinger
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed

/-! ## `thm:torsion-free` (line 284) -/

/-- **`thm:torsion-free`, exactly as printed** (line 284, `\label{thm:torsion-free}`). -/
theorem printedTorsionFreeTheorem_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreePrinted.PrintedTorsionFreeTheorem :=
  TorsionFreeFourLeaves.printedTorsionFreeTheorem_of_fourLeaves hgreendlinger
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed

/-- **`thm:torsion-free` in the radical form** (line 284, `\label{thm:torsion-free}`). -/
theorem printedTorsionFreeFullMFRadical_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TheoremC.PrintedTorsionFreeFullMFRadical :=
  TorsionFreeFourLeaves.printedTorsionFreeFullMFRadical_of_fourLeaves hgreendlinger
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed

/-- **`thm:torsion-free` at Osin's notion** (line 284, `\label{thm:torsion-free}`). -/
theorem printedTorsionFreeTheoremOsin_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreeOsinNotion.PrintedTorsionFreeTheoremOsin :=
  TorsionFreeFourLeaves.printedTorsionFreeTheoremOsin_of_fourLeaves hgreendlinger
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed

/-- **`thm:torsion-free` at the limit-set notion** (line 284, `\label{thm:torsion-free}`). -/
theorem printedTorsionFreeTheoremLimitSet_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreeLimitSetNotion.PrintedTorsionFreeTheoremLimitSet :=
  TorsionFreeFourLeaves.printedTorsionFreeTheoremLimitSet_of_fourLeaves hgreendlinger
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed

/-! ## `cor:regular-nonmf-algebra` (line 1718) -/

/-- **`cor:regular-nonmf-algebra`, along the printed proof** (line 1718,
`\label{cor:regular-nonmf-algebra}`). -/
theorem printedRegularNonMFAlgebra_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreePrinted.PrintedRegularNonMFAlgebra :=
  TorsionFreeFourLeaves.printedRegularNonMFAlgebra_of_fourLeaves hgreendlinger
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed

/-- **`cor:regular-nonmf-algebra` at Osin's notion** (line 1718). -/
theorem printedRegularNonMFAlgebraOsin_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreeOsinNotion.PrintedRegularNonMFAlgebraOsin :=
  TorsionFreeFourLeaves.printedRegularNonMFAlgebraOsin_of_fourLeaves hgreendlinger
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed

/-- **`cor:regular-nonmf-algebra` at the limit-set notion** (line 1718). -/
theorem printedRegularNonMFAlgebraLimitSet_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreeLimitSetNotion.PrintedRegularNonMFAlgebraLimitSet :=
  TorsionFreeFourLeaves.printedRegularNonMFAlgebraLimitSet_of_fourLeaves hgreendlinger
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed
    HydeLodha.finitelyPresentedInfiniteSimple_closed

/-! ## Proof-step sentences (lines 1644–1701) -/

/-- **The paragraph after `thm:hull`, as printed** (lines 1644–1648). -/
theorem printedHullProofParagraph_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreeSectionSentencesFourLeaves.PrintedHullProofParagraph :=
  TorsionFreeSectionSentencesFourLeaves.printedHullProofParagraph_of_fourLeaves hgreendlinger
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed

/-- **The pair `h₁, h₂` and `thm:hull` again** (lines 1662–1665, in the proof of
`lem:saturation`). -/
theorem printedSaturationPairAndHullAgain_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreeSectionSentencesFourLeaves.PrintedSaturationPairAndHullAgain :=
  TorsionFreeSectionSentencesFourLeaves.printedSaturationPairAndHullAgain_of_fourLeaves
    hgreendlinger HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed

/-- **"Apply Theorem `thm:hull` to `N₀`"** (lines 1665–1667, in the proof of
`lem:saturation`). -/
theorem printedSaturationApplyHull_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreeSectionSentencesFourLeaves.PrintedSaturationApplyHull :=
  TorsionFreeSectionSentencesFourLeaves.printedSaturationApplyHull_of_fourLeaves hgreendlinger
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed

/-- **"By Lemma `lem:saturation` applied to `G₀` and `N`"** (lines 1698–1701, in the proof of
`thm:torsion-free`). -/
theorem printedTheoremApplySaturation_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreeSectionSentencesFourLeaves.PrintedTheoremApplySaturation :=
  TorsionFreeSectionSentencesFourLeaves.printedTheoremApplySaturation_of_fourLeaves hgreendlinger
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed

end TorsionFreeGreendlingerLeaf
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedHullTheorem_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedHullTheoremOsin_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedHullTheoremLimitSet_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.hullSmallCancellationTorsionFreePrinted_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedSaturation_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedSaturationOsin_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedSaturationLimitSet_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.hullCommonQuotient_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.fournierFacioQuotient_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.literatureInputs_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.configuration_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.fournierFacioParagraph_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedTorsionFreeTheorem_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedTorsionFreeFullMFRadical_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedTorsionFreeTheoremOsin_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedTorsionFreeTheoremLimitSet_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedRegularNonMFAlgebra_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedRegularNonMFAlgebraOsin_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedRegularNonMFAlgebraLimitSet_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedHullProofParagraph_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedSaturationPairAndHullAgain_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedSaturationApplyHull_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedTheoremApplySaturation_of_greendlinger
