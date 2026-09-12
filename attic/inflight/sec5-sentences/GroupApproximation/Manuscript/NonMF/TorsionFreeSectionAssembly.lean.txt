import GroupApproximation.Manuscript.NonMF.TorsionFreeLiteratureInputsLeastArea
import GroupApproximation.Manuscript.NonMF.TorsionFreeLimitSetEndpoints
import GroupApproximation.Manuscript.NonMF.SimpleUniqueTraceFromNaiveFreeProduct
import GroupApproximation.Manuscript.NonMF.NaiveFreeProductAtAcylindricallyHyperbolicProof
import GroupApproximation.Meta.AxiomGuard

/-!
# `cor:regular-nonmf-algebra` with Dahmani–Guirardel–Osin's Theorem 2.35 discharged

`TorsionFreeLiteratureInputsLeastArea` and `TorsionFreeLimitSetEndpoints` state
`cor:regular-nonmf-algebra` over the section's leaves together with the two
C⋆-algebraic citations of the printed proof (tex lines 1728–1731).  The first of
them, `TorsionFreePrinted.SimpleUniqueTraceAtHypEmbedded` (Dahmani–Guirardel–Osin,
Theorem 2.35, at its source hypothesis), is proved:
`simpleUniqueTraceAtHypEmbedded_of_naiveFreeProduct` on the naive free-product
property of acylindrically hyperbolic groups with trivial finite radical
(`naiveFreeProductAtAcylindricallyHyperbolic`).

This module feeds it into the endpoints, so the corollary rests on the inputs of
`thm:torsion-free` and Gerasimova–Osin's Theorem 1.1 only.  The latter is
discharged in `TorsionFreeSectionAssemblyClosedGO`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreeSectionAssembly

open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted

/-- **Dahmani–Guirardel–Osin, Theorem 2.35, at its source hypothesis**, from the
naive free-product property. -/
theorem simpleUniqueTraceAtHypEmbedded_closed : SimpleUniqueTraceAtHypEmbedded :=
  simpleUniqueTraceAtHypEmbedded_of_naiveFreeProduct naiveFreeProductAtAcylindricallyHyperbolic

/-- **`cor:regular-nonmf-algebra`, along the printed proof** (tex line 1718), from
the inputs of `thm:torsion-free` and Gerasimova–Osin's Theorem 1.1. -/
theorem manuscriptRegularNonMFAlgebra_of_hullLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (hKO : TheoremC.KotowskiOllivierStatement)
    (hW : FinitelyPresentedInfiniteSimpleStatement)
    (hGO : GerasimovaOsinTheorem11Printed) : PrintedRegularNonMFAlgebra :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptRegularNonMFAlgebra_of_hullLeaves
    hgreendlinger hbridge hKO hW simpleUniqueTraceAtHypEmbedded_closed hGO

/-- **`cor:regular-nonmf-algebra` at Osin's notion**, from the inputs of
`thm:torsion-free` and Gerasimova–Osin's Theorem 1.1. -/
theorem manuscriptRegularNonMFAlgebraOsin_of_hullLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (hKO : TheoremC.KotowskiOllivierStatement)
    (hW : FinitelyPresentedInfiniteSimpleStatement)
    (hGO : GerasimovaOsinTheorem11Printed) :
    TorsionFreeOsinNotion.PrintedRegularNonMFAlgebraOsin :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptRegularNonMFAlgebraOsin_of_hullLeaves
    hgreendlinger hbridge hKO hW simpleUniqueTraceAtHypEmbedded_closed hGO

/-- **`cor:regular-nonmf-algebra` at the limit-set notion**, from the inputs of
`thm:torsion-free` and Gerasimova–Osin's Theorem 1.1. -/
theorem manuscriptRegularNonMFAlgebraLimitSet_of_hullLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (hKO : TheoremC.KotowskiOllivierStatement)
    (hW : FinitelyPresentedInfiniteSimpleStatement)
    (hGO : GerasimovaOsinTheorem11Printed) :
    TorsionFreeLimitSetNotion.PrintedRegularNonMFAlgebraLimitSet :=
  TorsionFreeLimitSetEndpoints.manuscriptRegularNonMFAlgebraLimitSet_of_hullLeaves
    hgreendlinger hbridge hKO hW simpleUniqueTraceAtHypEmbedded_closed hGO

end TorsionFreeSectionAssembly
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeSectionAssembly.simpleUniqueTraceAtHypEmbedded_closed
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeSectionAssembly.manuscriptRegularNonMFAlgebra_of_hullLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeSectionAssembly.manuscriptRegularNonMFAlgebraOsin_of_hullLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeSectionAssembly.manuscriptRegularNonMFAlgebraLimitSet_of_hullLeaves
