import GroupApproximation.Manuscript.NonMF.TorsionFreeLiteratureInputsLeastArea
import GroupApproximation.Manuscript.NonMF.TorsionFreeLimitSetEndpoints
import GroupApproximation.Manuscript.NonMF.SimpleUniqueTraceFromNaiveFreeProduct
import GroupApproximation.Manuscript.NonMF.NaiveFreeProductAtAcylindricallyHyperbolicProof
import GroupApproximation.Manuscript.NonMF.GerasimovaOsinTheorem11Closed
import GroupApproximation.Meta.AxiomGuard

/-!
# `cor:regular-nonmf-algebra` with its C⋆-algebraic inputs discharged

`TorsionFreeLiteratureInputsLeastArea` and `TorsionFreeLimitSetEndpoints` state
`cor:regular-nonmf-algebra` over the section's leaves together with the two
C⋆-algebraic citations of the printed proof (tex lines 1728–1731):

* `TorsionFreePrinted.SimpleUniqueTraceAtHypEmbedded`, Dahmani–Guirardel–Osin's
  Theorem 2.35 at its source hypothesis.  It is
  `simpleUniqueTraceAtHypEmbedded_of_naiveFreeProduct` on the proved naive
  free-product property of acylindrically hyperbolic groups with trivial finite
  radical (`naiveFreeProductAtAcylindricallyHyperbolic`).
* `TorsionFreePrinted.GerasimovaOsinTheorem11Printed`, Gerasimova–Osin's
  Theorem 1.1: `gerasimovaOsinTheorem11Printed`.

This module feeds both into the endpoints, so the corollary rests only on the
inputs of `thm:torsion-free`: the two Hull leaves, Kotowski–Ollivier, and a
finitely presented infinite simple torsion-free group.
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
the inputs of `thm:torsion-free` alone. -/
theorem manuscriptRegularNonMFAlgebra_of_hullLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (hKO : TheoremC.KotowskiOllivierStatement)
    (hW : FinitelyPresentedInfiniteSimpleStatement) : PrintedRegularNonMFAlgebra :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptRegularNonMFAlgebra_of_hullLeaves
    hgreendlinger hbridge hKO hW simpleUniqueTraceAtHypEmbedded_closed
    gerasimovaOsinTheorem11Printed

/-- **`cor:regular-nonmf-algebra` at Osin's notion**, from the inputs of
`thm:torsion-free` alone. -/
theorem manuscriptRegularNonMFAlgebraOsin_of_hullLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (hKO : TheoremC.KotowskiOllivierStatement)
    (hW : FinitelyPresentedInfiniteSimpleStatement) :
    TorsionFreeOsinNotion.PrintedRegularNonMFAlgebraOsin :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptRegularNonMFAlgebraOsin_of_hullLeaves
    hgreendlinger hbridge hKO hW simpleUniqueTraceAtHypEmbedded_closed
    gerasimovaOsinTheorem11Printed

/-- **`cor:regular-nonmf-algebra` at the limit-set notion**, from the inputs of
`thm:torsion-free` alone. -/
theorem manuscriptRegularNonMFAlgebraLimitSet_of_hullLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (hKO : TheoremC.KotowskiOllivierStatement)
    (hW : FinitelyPresentedInfiniteSimpleStatement) :
    TorsionFreeLimitSetNotion.PrintedRegularNonMFAlgebraLimitSet :=
  TorsionFreeLimitSetEndpoints.manuscriptRegularNonMFAlgebraLimitSet_of_hullLeaves
    hgreendlinger hbridge hKO hW simpleUniqueTraceAtHypEmbedded_closed
    gerasimovaOsinTheorem11Printed

end TorsionFreeSectionAssembly
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeSectionAssembly.simpleUniqueTraceAtHypEmbedded_closed
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeSectionAssembly.manuscriptRegularNonMFAlgebra_of_hullLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeSectionAssembly.manuscriptRegularNonMFAlgebraOsin_of_hullLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeSectionAssembly.manuscriptRegularNonMFAlgebraLimitSet_of_hullLeaves
