import GroupApproximation.GGT.HullSCTheorem71General
import GroupApproximation.Manuscript.NonMF.TorsionFreeSectionSentences
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:hull` as printed, at every acylindrically hyperbolic group

`TorsionFreeSectionSentences.PrintedHullSmallCancellationCurrent` is the statement
of `thm:hull` in `non_mf_groups_exist.tex` (lines 1624-1628): *for an
acylindrically hyperbolic `G`, Hull's alphabet `A`, a suitable `N` and
`g₁, …, g_m ∈ G`, there is a surjection `φ : G ↠ Q` onto an acylindrically
hyperbolic group with `φ(gᵢ) ∈ φ(N)` and every element of finite order of `Q`
the image of an element of the same order.*  There is no torsion hypothesis on
`G`.

This module derives it from Hull's published injectivity-radius form at every
ambient group (`HullSC.HullBallFormStatementGeneral`), and so from Lemma 4.4,
Lemma 4.9 and the simultaneous peripheral selection, through the general chain of
`HullSCTheorem71General`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreeHullPrintedGeneral

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.TorsionFreeSectionSentences

universe u

/-- **`thm:hull` as printed, from the published ball form at every ambient
group**: take radius `0` and forget the injectivity set and the kernel datum. -/
theorem printedHullSmallCancellationCurrent_of_ballFormGeneral
    (h : HullSC.HullBallFormStatementGeneral.{u}) :
    PrintedHullSmallCancellationCurrent.{u} := by
  intro G _ _ A N hN m g
  obtain ⟨H⟩ := h A hN g 0
  exact ⟨H.quotient.mono (Set.empty_subset _)⟩

/-- **`thm:hull` as printed, from Lemma 4.4, Lemma 4.9 and the simultaneous
peripheral selection.** -/
theorem printedHullSmallCancellationCurrent_of_lemma44_of_lemma49
    (hselect : HullSC.SimultaneousAuxiliaryPeripheralSelection.{u})
    (h44 : HullSC.HullLemma44CanonicalQuotientStatement.{u})
    (h49 : HullSC.HullLemma49KernelPowerStatement.{u, 0}) :
    PrintedHullSmallCancellationCurrent.{u} :=
  printedHullSmallCancellationCurrent_of_ballFormGeneral
    (HullSC.hullBallFormStatementGeneral_of_lemma44_of_lemma49 hselect h44 h49)

end TorsionFreeHullPrintedGeneral
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeHullPrintedGeneral.printedHullSmallCancellationCurrent_of_ballFormGeneral
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeHullPrintedGeneral.printedHullSmallCancellationCurrent_of_lemma44_of_lemma49
