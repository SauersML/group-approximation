import GroupApproximation.Manuscript.NonMF.TorsionFreeSectionAssembly
import GroupApproximation.Manuscript.NonMF.GerasimovaOsinTheorem11Closed
import GroupApproximation.Meta.AxiomGuard

/-!
# `cor:regular-nonmf-algebra` with both C⋆-algebraic inputs discharged

`TorsionFreeSectionAssembly` discharges Dahmani–Guirardel–Osin's Theorem 2.35.  This
module adds Gerasimova–Osin's Theorem 1.1 (`gerasimovaOsinTheorem11Printed`), so
`cor:regular-nonmf-algebra` rests only on the inputs of `thm:torsion-free`: the two
Hull leaves, Kotowski–Ollivier, and a finitely presented infinite simple
torsion-free group.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreeSectionAssembly

open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted

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

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeSectionAssembly.manuscriptRegularNonMFAlgebra_of_hullLeaves_closedGO
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeSectionAssembly.manuscriptRegularNonMFAlgebraOsin_of_hullLeaves_closedGO
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeSectionAssembly.manuscriptRegularNonMFAlgebraLimitSet_of_hullLeaves_closedGO
