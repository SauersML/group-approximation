import GroupApproximation.GGT.HullSCTheorem71GeneralLeastArea
import GroupApproximation.Manuscript.NonMF.TorsionFreeHullPrintedGeneral
import GroupApproximation.Manuscript.NonMF.TorsionFreeOsinNotion
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:hull` as printed, over the least-area leaves

`thm:hull` (tex lines 1624-1628) at every acylindrically hyperbolic group, with no
torsion hypothesis, from the two leaves of the Hull chain: the least-area
Greendlinger waist and the embedded bridge.  It is given both at Hull's
Cayley-graph notion (`PrintedHullSmallCancellationCurrent`) and at Osin's notion,
which the manuscript uses (`TorsionFreeOsinNotion.PrintedHullSmallCancellationOsin`).
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreeHullPrintedLeastArea

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.TorsionFreeSectionSentences
open GroupApproximation.Manuscript.NonMF.TorsionFreeHullPrintedGeneral

/-- **`thm:hull` as printed, at every acylindrically hyperbolic group, from the
least-area leaves.** -/
theorem manuscriptSentence_hullTheorem_of_leastAreaLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}) :
    PrintedHullSmallCancellationCurrent.{0} :=
  printedHullSmallCancellationCurrent_of_ballFormGeneral
    (HullSC.hullBallFormStatementGeneral_of_leastAreaLeaves hgreendlinger hbridge)

/-- **`thm:hull` as printed, at Osin's notion of acylindrical hyperbolicity, from
the least-area leaves.** -/
theorem manuscriptSentence_hullTheoremOsin_of_leastAreaLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}) :
    TorsionFreeOsinNotion.PrintedHullSmallCancellationOsin :=
  TorsionFreeOsinNotion.printedHullSmallCancellationOsin_of_current
    (manuscriptSentence_hullTheorem_of_leastAreaLeaves hgreendlinger hbridge)

end TorsionFreeHullPrintedLeastArea
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeHullPrintedLeastArea.manuscriptSentence_hullTheorem_of_leastAreaLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeHullPrintedLeastArea.manuscriptSentence_hullTheoremOsin_of_leastAreaLeaves
