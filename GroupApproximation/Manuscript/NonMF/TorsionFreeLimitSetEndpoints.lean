import GroupApproximation.Manuscript.NonMF.TorsionFreeLimitSetNotion
import GroupApproximation.Manuscript.NonMF.TorsionFreeLiteratureInputsLeastArea
import GroupApproximation.Meta.AxiomGuard

/-!
# `sec:torsion-free` at the limit-set notion, over the least-area leaves

The endpoints of `TorsionFreeLimitSetNotion` that need the Fournier-Facio paragraph,
fed by the section's leaves:

* `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement` and
  `HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement`, the two Hull
  leaves;
* `TheoremC.KotowskiOllivierStatement` and
  `TorsionFreePrinted.FinitelyPresentedInfiniteSimpleStatement`, the remaining
  inputs of the Fournier-Facio paragraph (`TorsionFreeLiteratureInputsLeastArea`);
* `TorsionFreePrinted.SimpleUniqueTraceAtHypEmbedded` and
  `TorsionFreePrinted.GerasimovaOsinTheorem11Printed`, the C⋆-algebraic inputs of
  `cor:regular-nonmf-algebra`.

`thm:hull` and `lem:saturation` at the limit-set notion over the two Hull leaves are
in the same namespace, at the end of `TorsionFreeLimitSetNotion`.

## Status: the residual hypotheses and who owns them

The six hypotheses here are those of `TorsionFreeLiteratureInputsLeastArea`, with
their owners listed there.  The hard direction of Osin's Theorem 1.1, used by
`lem:saturation`, is `GGT.OsinClassification.isAcylindricallyHyperbolicOsin_of_limitSet`,
in lane dgo-geometric (`OsinLimitSetSpelling`).
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
    (hKO : TheoremC.KotowskiOllivierStatement)
    (hW : FinitelyPresentedInfiniteSimpleStatement) : PrintedTorsionFreeTheoremLimitSet :=
  printedTorsionFreeTheoremLimitSet_of_printed
    (TorsionFreeLiteratureInputsLeastArea.manuscriptTorsionFreeTheorem_of_hullLeaves
      hgreendlinger hbridge hKO hW)

/-- **`cor:regular-nonmf-algebra` at the limit-set notion** (tex line 1718), over
the inputs of `thm:torsion-free` and the two C⋆-algebraic inputs. -/
theorem manuscriptRegularNonMFAlgebraLimitSet_of_hullLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (hKO : TheoremC.KotowskiOllivierStatement)
    (hW : FinitelyPresentedInfiniteSimpleStatement)
    (hDGO : SimpleUniqueTraceAtHypEmbedded)
    (hGO : GerasimovaOsinTheorem11Printed) : PrintedRegularNonMFAlgebraLimitSet :=
  printedRegularNonMFAlgebraLimitSet_of_printed
    (TorsionFreeLiteratureInputsLeastArea.manuscriptRegularNonMFAlgebra_of_hullLeaves
      hgreendlinger hbridge hKO hW hDGO hGO)

end TorsionFreeLimitSetEndpoints
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeLimitSetEndpoints.manuscriptTorsionFreeTheoremLimitSet_of_hullLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeLimitSetEndpoints.manuscriptRegularNonMFAlgebraLimitSet_of_hullLeaves
