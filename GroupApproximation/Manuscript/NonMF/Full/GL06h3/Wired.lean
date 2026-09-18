import GroupApproximation.Manuscript.NonMF.Full.GL06h3.Threshold
import GroupApproximation.Manuscript.NonMF.Full.GL06h2.ShortConjugate
import GroupApproximation.Manuscript.NonMF.Full.GL06e.Refuted
import GroupApproximation.Meta.AxiomGuard

/-!
# GL06h3: the short-conjugate clause wired in

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull`
(non_mf_groups_exist.tex ~2121, Hull's small cancellation theorem, through Osin's Lemma 9.7).

The short-conjugate clause is `GL06h2.shortWordNeConjRelatorStatement_holds`.  What remains is
the geometric nearest-cell cut, `NearestCellCutSectionStatement`.

* `shortBoundaryRefutedBelowSection_of_nearestCellCutSection`: the short-boundary refutation.
* `allCellsShortEnclosedRefutedBelowSection_of_nearestCellCutSection`: GL06e's all-cells clause.
* `refutedBelowSection_of_innerPocketEnclosedCorrected_of_nearestCellCut`: GL06e's cell pocket
  walk refutation.

## Manuscript status

Infrastructure for `thm:hull` (non_mf_groups_exist.tex ~2121); certifies no printed sentence on
its own.
-/

namespace GroupApproximation.Full.GL06h3

universe u w v

/-- **The short-boundary refutation from the nearest-cell cut** (Osin, proof of Lemma 9.7(b);
`thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem shortBoundaryRefutedBelowSection_of_nearestCellCutSection
    (hcut : NearestCellCutSectionStatement.{u, w, v}) :
    ShortBoundaryRefutedBelowSectionStatement.{u, w, v} :=
  shortBoundaryRefutedBelowSection_of_nearestCellCut hcut
    GL06h2.shortWordNeConjRelatorStatement_holds

/-- **GL06e's all-cells clause from the nearest-cell cut** (Osin, proof of Lemma 9.7(b);
`thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem allCellsShortEnclosedRefutedBelowSection_of_nearestCellCutSection
    (hcut : NearestCellCutSectionStatement.{u, w, v}) :
    GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{u, w, v} :=
  allCellsShortEnclosedRefutedBelowSection_of_shortBoundarySection
    (shortBoundaryRefutedBelowSection_of_nearestCellCutSection hcut)

/-- **GL06e's cell pocket walk refutation from the nearest-cell cut** (Osin, proof of
Lemma 9.7(b); `thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem refutedBelowSection_of_innerPocketEnclosedCorrected_of_nearestCellCut
    (hencl : GL03BPinch.InnerPocketEnclosedTwoArcCorrected.{u, w, v})
    (hcut : NearestCellCutSectionStatement.{u, w, v}) :
    GL06e.CellPocketWalkRefutedBelowSectionStatement.{u, w, v} :=
  GL06e.refutedBelowSection_of_innerPocketEnclosedCorrected_of_allCells hencl
    (allCellsShortEnclosedRefutedBelowSection_of_nearestCellCutSection hcut)

end GroupApproximation.Full.GL06h3

#audit_axioms GroupApproximation.Full.GL06h3.shortBoundaryRefutedBelowSection_of_nearestCellCutSection
#audit_axioms GroupApproximation.Full.GL06h3.allCellsShortEnclosedRefutedBelowSection_of_nearestCellCutSection
#audit_axioms GroupApproximation.Full.GL06h3.refutedBelowSection_of_innerPocketEnclosedCorrected_of_nearestCellCut
