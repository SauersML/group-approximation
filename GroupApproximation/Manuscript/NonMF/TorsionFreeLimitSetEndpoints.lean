import GroupApproximation.Manuscript.NonMF.TorsionFreeLimitSetNotion
import GroupApproximation.Manuscript.NonMF.TorsionFreeLiteratureInputsLeastArea
import GroupApproximation.Manuscript.NonMF.TorsionFreeHullPrintedLeastArea
import GroupApproximation.Meta.AxiomGuard

/-!
# `sec:torsion-free` at the limit-set notion, over the least-area leaves

The endpoints of `TorsionFreeLimitSetNotion`, fed by the section's leaves:

* `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement` and
  `HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement`, the two Hull
  leaves;
* `HullSC.BoundedImageEmbeddingStatement`, `TheoremC.KotowskiOllivierStatement` and
  `TorsionFreePrinted.FinitelyPresentedInfiniteSimpleStatement`, the remaining
  inputs of the Fournier-Facio paragraph (`TorsionFreeLiteratureInputsLeastArea`);
* `TorsionFreePrinted.SimpleUniqueTraceAtHypEmbedded` and
  `TorsionFreePrinted.GerasimovaOsinTheorem11Printed`, the C⋆-algebraic inputs of
  `cor:regular-nonmf-algebra`;
* for `lem:saturation` only, the hard direction of Osin's Theorem 1.1 (`hhard`).
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreeLimitSetEndpoints

open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted
open GroupApproximation.Manuscript.NonMF.TorsionFreeLimitSetNotion

/-- **`thm:torsion-free` at the limit-set notion** (tex line 284), over the least-area
leaves and the inputs of the Fournier-Facio paragraph. -/
theorem manuscriptTorsionFreeTheoremLimitSet_of_hullLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (hemb : HullSC.BoundedImageEmbeddingStatement.{0, 0})
    (hKO : TheoremC.KotowskiOllivierStatement)
    (hW : FinitelyPresentedInfiniteSimpleStatement) : PrintedTorsionFreeTheoremLimitSet :=
  printedTorsionFreeTheoremLimitSet_of_printed
    (TorsionFreeLiteratureInputsLeastArea.manuscriptTorsionFreeTheorem_of_hullLeaves
      hgreendlinger hbridge hemb hKO hW)

/-- **`thm:hull` at the limit-set notion** (tex lines 1624–1628), from the two Hull
leaves. -/
theorem manuscriptHullTheoremLimitSet_of_leastAreaLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}) :
    PrintedHullSmallCancellationLimitSet :=
  printedHullSmallCancellationLimitSet_of_current
    (TorsionFreeHullPrintedLeastArea.manuscriptSentence_hullTheorem_of_leastAreaLeaves
      hgreendlinger hbridge)

/-- **`lem:saturation` at the limit-set notion** (tex line 1650), from the two Hull
leaves and the hard direction of Osin's Theorem 1.1. -/
theorem manuscriptSaturationLimitSet_of_leastAreaLeaves
    (hhard : ∀ (G : Type) [Group G],
      GGT.SequentialBoundary.IsAcylindricallyHyperbolicLimitSet G →
        GGT.IsAcylindricallyHyperbolicOsin G)
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}) :
    PrintedSaturationLimitSet :=
  printedSaturationLimitSet_of_noOmega hhard
    (TorsionFreeLeastAreaAssembly.printedSaturationNoOmega_of_leastAreaLeaves
      hgreendlinger hbridge)

/-- **`cor:regular-nonmf-algebra` at the limit-set notion** (tex line 1718), over
the inputs of `thm:torsion-free` and the two C⋆-algebraic inputs. -/
theorem manuscriptRegularNonMFAlgebraLimitSet_of_hullLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (hemb : HullSC.BoundedImageEmbeddingStatement.{0, 0})
    (hKO : TheoremC.KotowskiOllivierStatement)
    (hW : FinitelyPresentedInfiniteSimpleStatement)
    (hDGO : SimpleUniqueTraceAtHypEmbedded)
    (hGO : GerasimovaOsinTheorem11Printed) : PrintedRegularNonMFAlgebraLimitSet :=
  printedRegularNonMFAlgebraLimitSet_of_printed
    (TorsionFreeLiteratureInputsLeastArea.manuscriptRegularNonMFAlgebra_of_hullLeaves
      hgreendlinger hbridge hemb hKO hW hDGO hGO)

end TorsionFreeLimitSetEndpoints
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeLimitSetEndpoints.manuscriptTorsionFreeTheoremLimitSet_of_hullLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeLimitSetEndpoints.manuscriptHullTheoremLimitSet_of_leastAreaLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeLimitSetEndpoints.manuscriptSaturationLimitSet_of_leastAreaLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeLimitSetEndpoints.manuscriptRegularNonMFAlgebraLimitSet_of_hullLeaves
