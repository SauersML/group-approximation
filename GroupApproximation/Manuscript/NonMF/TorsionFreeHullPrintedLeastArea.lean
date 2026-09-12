import GroupApproximation.GGT.HullSCTheorem71GeneralLeastArea
import GroupApproximation.Manuscript.NonMF.TorsionFreeHullPrintedGeneral
import GroupApproximation.Manuscript.NonMF.TorsionFreeHullParagraphGeneral
import GroupApproximation.Manuscript.NonMF.TorsionFreeOsinNotion
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:hull` as printed, over the least-area leaves

`thm:hull` (tex lines 1624-1628) at every acylindrically hyperbolic group, with no
torsion hypothesis, from the two leaves of the Hull chain: the least-area
Greendlinger waist and the embedded bridge.  It is given both at Hull's
Cayley-graph notion (`PrintedHullSmallCancellationCurrent`) and at Osin's notion,
which the manuscript uses (`TorsionFreeOsinNotion.PrintedHullSmallCancellationOsin`).

The paragraph after the theorem (tex lines 1644–1648) over the same leaves
completes `TorsionFreeHullParagraphGeneral`, in that namespace.
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

namespace TorsionFreeHullParagraphGeneral

open GroupApproximation.Manuscript.NonMF.TorsionFree

/-- **The one-relator sentence at every ambient group, from the least-area
leaves.** -/
theorem manuscriptSentence_hullOneTargetOneRelatorGeneral_of_leastAreaLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    {G : Type} [Group G] (A : HullGeneratingSet G)
    {N : Subgroup G} (hN : Suitable A.alphabet N) (t : G) :
    ∃ (s : HullSC.HullTower A N (fun j : Fin 0 => Fin.elim0 j) (fun _ : Fin 1 => t) 0)
      (r : G), s.step.q.ker = Subgroup.normalClosure ({r} : Set G) ∧
        Nonempty (G ⧸ Subgroup.normalClosure ({r} : Set G) ≃* s.step.Q) :=
  manuscriptSentence_hullOneTargetOneRelatorGeneral_of_oneStep
    (HullSC.hullOneStepStatementGeneral_of_leastAreaLeaves hgreendlinger hbridge) A hN t

/-- **The induction sentence at every ambient group, from the least-area
leaves.** -/
theorem manuscriptSentence_hullInductionOnTargetsGeneral_of_leastAreaLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (m : ℕ) {G : Type} [Group G] (A : HullGeneratingSet G)
    {N : Subgroup G} (hN : Suitable A.alphabet N) (t : Fin m → G) (R : ℕ) :
    ∃ s : HullSC.HullTower A N (fun j : Fin 0 => Fin.elim0 j) t R,
      Suitable s.step.hullSet.alphabet (N.map s.step.q) :=
  manuscriptSentence_hullInductionOnTargetsGeneral_of_oneStep
    (HullSC.hullOneStepStatementGeneral_of_leastAreaLeaves hgreendlinger hbridge) m A hN t R

end TorsionFreeHullParagraphGeneral
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeHullPrintedLeastArea.manuscriptSentence_hullTheorem_of_leastAreaLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeHullPrintedLeastArea.manuscriptSentence_hullTheoremOsin_of_leastAreaLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeHullParagraphGeneral.manuscriptSentence_hullOneTargetOneRelatorGeneral_of_leastAreaLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeHullParagraphGeneral.manuscriptSentence_hullInductionOnTargetsGeneral_of_leastAreaLeaves
