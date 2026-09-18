import GroupApproximation.Manuscript.NonMF.Full.NMWire2.Refuted
import GroupApproximation.Manuscript.NonMF.Full.NMWire.CopyPocket
import GroupApproximation.Manuscript.NonMF.Full.GL06.BinderFive
import GroupApproximation.Meta.AxiomGuard

/-!
# Binder 5 with the corrected enclosed pocket discharged

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull`
(non_mf_groups_exist.tex ~2121).

* `nmWire2_copy_of_shortPocket`: `NMWire.nmWire_copy_of_corrected_shortPocket` with `hencl`
  discharged by `GL03BPinch.innerPocketEnclosedTwoArcCorrected`.
* `nmWire2_copy_of_nearestCellPocket`: `NMWire.nmWire_copy_of_corrected_nearestCellPocket`, the
  same.
* `nmWire2_copy_of_allCells`, `nmWire2_copy_of_shortBoundary`, `nmWire2_copy_of_nearestCellCut`,
  `nmWire2_copy_of_descent`: `GL06.osinMultipleEdgePocketRegionCopyBelowSection_of_refuted`
  after the refutations of `NMWire2.Refuted`.

The weakest of these inputs is `GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement`.  Each
of the other five implies it: the short nearest pocket and the nearest cell pocket through
`GL06h4`, the short-boundary refutation through `GL06h3`, and the descent and the nearest-cell
cut through the short-boundary refutation.

This module is routing only.  It certifies no printed sentence on its own.
-/

namespace GroupApproximation.Full.NMWire2

universe u w v

open GroupApproximation.GGT GroupApproximation.GGT.VanKampen

/-- **Binder 5 from the short nearest pocket** (Osin, proof of Lemma 9.7(b); `thm:hull`). -/
theorem nmWire2_copy_of_shortPocket
    (hshort : GroupApproximation.Full.GL06h4.gl06h4Nearest_shortPocketStatement.{u, w, v}) :
    OsinMultipleEdgePocketRegionCopyBelowSectionStatement.{u, w, v} :=
  GroupApproximation.Full.NMWire.nmWire_copy_of_corrected_shortPocket
    GroupApproximation.Full.GL03BPinch.innerPocketEnclosedTwoArcCorrected hshort

#audit_axioms GroupApproximation.Full.NMWire2.nmWire2_copy_of_shortPocket

/-- **Binder 5 from the nearest cell pocket** (Osin, proof of Lemma 9.7(b); `thm:hull`). -/
theorem nmWire2_copy_of_nearestCellPocket
    (hnear : GroupApproximation.Full.GL06h4.NearestCellPocketStatement.{u, w, v}) :
    OsinMultipleEdgePocketRegionCopyBelowSectionStatement.{u, w, v} :=
  GroupApproximation.Full.NMWire.nmWire_copy_of_corrected_nearestCellPocket
    GroupApproximation.Full.GL03BPinch.innerPocketEnclosedTwoArcCorrected hnear

#audit_axioms GroupApproximation.Full.NMWire2.nmWire2_copy_of_nearestCellPocket

/-- **Binder 5 from the all-cells refutation** (Osin, proof of Lemma 9.7(b); `thm:hull`). -/
theorem nmWire2_copy_of_allCells
    (hall :
      GroupApproximation.Full.GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{u, w, v}) :
    OsinMultipleEdgePocketRegionCopyBelowSectionStatement.{u, w, v} :=
  GroupApproximation.Full.GL06.osinMultipleEdgePocketRegionCopyBelowSection_of_refuted
    (nmWire2_refutedBelow_of_allCells hall)

#audit_axioms GroupApproximation.Full.NMWire2.nmWire2_copy_of_allCells

/-- **Binder 5 from the short-boundary refutation** (`thm:hull`). -/
theorem nmWire2_copy_of_shortBoundary
    (h : GroupApproximation.Full.GL06h3.ShortBoundaryRefutedBelowSectionStatement.{u, w, v}) :
    OsinMultipleEdgePocketRegionCopyBelowSectionStatement.{u, w, v} :=
  GroupApproximation.Full.GL06.osinMultipleEdgePocketRegionCopyBelowSection_of_refuted
    (nmWire2_refutedBelow_of_shortBoundary h)

#audit_axioms GroupApproximation.Full.NMWire2.nmWire2_copy_of_shortBoundary

/-- **Binder 5 from the nearest-cell cut** (`thm:hull`). -/
theorem nmWire2_copy_of_nearestCellCut
    (hcut : GroupApproximation.Full.GL06h3.NearestCellCutSectionStatement.{u, w, v}) :
    OsinMultipleEdgePocketRegionCopyBelowSectionStatement.{u, w, v} :=
  GroupApproximation.Full.GL06.osinMultipleEdgePocketRegionCopyBelowSection_of_refuted
    (nmWire2_refutedBelow_of_nearestCellCut hcut)

#audit_axioms GroupApproximation.Full.NMWire2.nmWire2_copy_of_nearestCellCut

/-- **Binder 5 from the descent** (`thm:hull`). -/
theorem nmWire2_copy_of_descent
    (h : GroupApproximation.Full.GL06h5.gl06h5_descentPocketStatement.{u, w, v}) :
    OsinMultipleEdgePocketRegionCopyBelowSectionStatement.{u, w, v} :=
  GroupApproximation.Full.GL06.osinMultipleEdgePocketRegionCopyBelowSection_of_refuted
    (nmWire2_refutedBelow_of_descent h)

#audit_axioms GroupApproximation.Full.NMWire2.nmWire2_copy_of_descent

end GroupApproximation.Full.NMWire2
