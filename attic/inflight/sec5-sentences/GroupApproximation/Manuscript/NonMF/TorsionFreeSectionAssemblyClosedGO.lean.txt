import GroupApproximation.Manuscript.NonMF.TorsionFreeSectionAssembly
import GroupApproximation.Manuscript.NonMF.DGOTheorem235Proof
import GroupApproximation.Manuscript.NonMF.GerasimovaOsinTheorem11Closed
import GroupApproximation.Meta.AxiomGuard

/-!
# `cor:regular-nonmf-algebra` with both C⋆-algebraic inputs discharged

The printed proof of `cor:regular-nonmf-algebra` (tex lines 1724–1736) cites two
C⋆-algebraic theorems, and both are proved:

* Dahmani–Guirardel–Osin, Theorem 2.35: `TorsionFreePrinted.dgoTheorem235Printed`,
  and at its source hypothesis `TorsionFreeSectionAssembly.simpleUniqueTraceAtHypEmbedded_closed`;
* Gerasimova–Osin, Theorem 1.1: `TorsionFreePrinted.gerasimovaOsinTheorem11Printed`.

This module gives every endpoint of the corollary that took them as hypotheses
again, with both discharged.  It is a twin module, so the landed statements over
the citations stay as they are:

* `TorsionFreePrinted.manuscriptRegularNonMFAlgebra` over `thm:torsion-free`'s
  package inputs;
* `TorsionFreeLeafAssembly.manuscriptRegularNonMFAlgebra_of_saturationNoOmega` and
  `…_of_leaves`, over the historical Hull leaves;
* `TorsionFreeLeastAreaAssembly.manuscriptRegularNonMFAlgebra_of_leastAreaLeaves`
  and `TorsionFreeOsinNotion.manuscriptRegularNonMFAlgebraOsin_of_leastAreaLeaves`,
  over the least-area leaves and the Fournier-Facio paragraph;
* the endpoints of `TorsionFreeSectionAssembly`, with the paragraph produced, at
  Hull's, Osin's and the limit-set notion.  These rest only on the inputs of
  `thm:torsion-free`: the two Hull leaves, Kotowski–Ollivier, and a finitely
  presented infinite simple torsion-free group.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreeSectionAssembly

open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted

/-! ## Over the package inputs and the historical leaves -/

/-- **`cor:regular-nonmf-algebra`, along the printed proof**, from the two inputs of
`thm:torsion-free` alone (`TorsionFreePrinted.manuscriptRegularNonMFAlgebra` with
both C⋆-algebraic citations discharged). -/
theorem manuscriptRegularNonMFAlgebra_closedCitations (hFFF : FournierFacioParagraph)
    (hHull : HullPrintedInputs.{0}) : PrintedRegularNonMFAlgebra :=
  manuscriptRegularNonMFAlgebra hFFF hHull dgoTheorem235Printed
    gerasimovaOsinTheorem11Printed

/-- **`cor:regular-nonmf-algebra` from `lem:saturation` as printed**, with both
C⋆-algebraic citations discharged. -/
theorem manuscriptRegularNonMFAlgebra_of_saturationNoOmega_closedCitations
    (hFFF : FournierFacioParagraph) (hsat : PrintedSaturationNoOmega.{0}) :
    PrintedRegularNonMFAlgebra :=
  TorsionFreeLeafAssembly.manuscriptRegularNonMFAlgebra_of_saturationNoOmega hFFF hsat
    simpleUniqueTraceAtHypEmbedded_closed gerasimovaOsinTheorem11Printed

/-- **`cor:regular-nonmf-algebra` over the historical Hull leaves**, with both
C⋆-algebraic citations discharged. -/
theorem manuscriptRegularNonMFAlgebra_of_leaves_closedCitations
    (hFFF : FournierFacioParagraph)
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicStatement.{0, 0, 0}) :
    PrintedRegularNonMFAlgebra :=
  TorsionFreeLeafAssembly.manuscriptRegularNonMFAlgebra_of_leaves hFFF hgreendlinger
    hbridge simpleUniqueTraceAtHypEmbedded_closed gerasimovaOsinTheorem11Printed

/-! ## Over the least-area leaves and the Fournier-Facio paragraph -/

/-- **`cor:regular-nonmf-algebra` over the Fournier-Facio paragraph and the two
least-area Hull leaves**, with both C⋆-algebraic citations discharged. -/
theorem manuscriptRegularNonMFAlgebra_of_leastAreaLeaves_closedCitations
    (hFFF : FournierFacioParagraph)
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}) :
    PrintedRegularNonMFAlgebra :=
  TorsionFreeLeastAreaAssembly.manuscriptRegularNonMFAlgebra_of_leastAreaLeaves hFFF
    hgreendlinger hbridge simpleUniqueTraceAtHypEmbedded_closed
    gerasimovaOsinTheorem11Printed

/-- **`cor:regular-nonmf-algebra` at Osin's notion, over the Fournier-Facio paragraph
and the two least-area Hull leaves**, with both C⋆-algebraic citations
discharged. -/
theorem manuscriptRegularNonMFAlgebraOsin_of_leastAreaLeaves_closedCitations
    (hFFF : FournierFacioParagraph)
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}) :
    TorsionFreeOsinNotion.PrintedRegularNonMFAlgebraOsin :=
  TorsionFreeOsinNotion.manuscriptRegularNonMFAlgebraOsin_of_leastAreaLeaves hFFF
    hgreendlinger hbridge simpleUniqueTraceAtHypEmbedded_closed
    gerasimovaOsinTheorem11Printed

/-! ## Over the inputs of `thm:torsion-free` alone -/

/-- **`cor:regular-nonmf-algebra`, along the printed proof** (tex line 1718), from
the inputs of `thm:torsion-free` alone. -/
theorem manuscriptRegularNonMFAlgebra_of_hullLeaves_closedGO
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (hKO : TheoremC.KotowskiOllivierStatement)
    (hW : FinitelyPresentedInfiniteSimpleStatement) : PrintedRegularNonMFAlgebra :=
  manuscriptRegularNonMFAlgebra_of_hullLeaves hgreendlinger hbridge hKO hW
    gerasimovaOsinTheorem11Printed

/-- **`cor:regular-nonmf-algebra` at Osin's notion**, from the inputs of
`thm:torsion-free` alone. -/
theorem manuscriptRegularNonMFAlgebraOsin_of_hullLeaves_closedGO
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (hKO : TheoremC.KotowskiOllivierStatement)
    (hW : FinitelyPresentedInfiniteSimpleStatement) :
    TorsionFreeOsinNotion.PrintedRegularNonMFAlgebraOsin :=
  manuscriptRegularNonMFAlgebraOsin_of_hullLeaves hgreendlinger hbridge hKO hW
    gerasimovaOsinTheorem11Printed

/-- **`cor:regular-nonmf-algebra` at the limit-set notion**, from the inputs of
`thm:torsion-free` alone. -/
theorem manuscriptRegularNonMFAlgebraLimitSet_of_hullLeaves_closedGO
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (hKO : TheoremC.KotowskiOllivierStatement)
    (hW : FinitelyPresentedInfiniteSimpleStatement) :
    TorsionFreeLimitSetNotion.PrintedRegularNonMFAlgebraLimitSet :=
  manuscriptRegularNonMFAlgebraLimitSet_of_hullLeaves hgreendlinger hbridge hKO hW
    gerasimovaOsinTheorem11Printed

end TorsionFreeSectionAssembly
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeSectionAssembly.manuscriptRegularNonMFAlgebra_closedCitations
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeSectionAssembly.manuscriptRegularNonMFAlgebra_of_saturationNoOmega_closedCitations
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeSectionAssembly.manuscriptRegularNonMFAlgebra_of_leaves_closedCitations
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeSectionAssembly.manuscriptRegularNonMFAlgebra_of_leastAreaLeaves_closedCitations
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeSectionAssembly.manuscriptRegularNonMFAlgebraOsin_of_leastAreaLeaves_closedCitations
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeSectionAssembly.manuscriptRegularNonMFAlgebra_of_hullLeaves_closedGO
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeSectionAssembly.manuscriptRegularNonMFAlgebraOsin_of_hullLeaves_closedGO
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeSectionAssembly.manuscriptRegularNonMFAlgebraLimitSet_of_hullLeaves_closedGO
