import GroupApproximation.Manuscript.NonMF.Full.GL03BPinch.Endpoint
import GroupApproximation.Manuscript.NonMF.Full.GL06e.Refuted
import GroupApproximation.Manuscript.NonMF.Full.GL06h3.Assembly
import GroupApproximation.Manuscript.NonMF.Full.GL06h3.Wired
import GroupApproximation.Manuscript.NonMF.Full.GL06h4.PocketAssembly
import GroupApproximation.Manuscript.NonMF.Full.GL06h4.NearestShortPocket
import GroupApproximation.Manuscript.NonMF.Full.GL06h5.Descent
import GroupApproximation.Meta.AxiomGuard

/-!
# GL06e's refutation below the section count, with the corrected enclosed pocket discharged

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull`
(non_mf_groups_exist.tex ~2121).

Every consumer below took `hencl : GL03BPinch.InnerPocketEnclosedTwoArcCorrected` as a
hypothesis.  Here `hencl` is the proved `GL03BPinch.innerPocketEnclosedTwoArcCorrected`
(`GL03BPinch/Endpoint`).  Every other hypothesis is kept exactly.

* `nmWire2_refutedBelowInput_of_allCells`:
  `GL06e.refutedBelowInput_of_innerPocketEnclosedCorrected`.
* `nmWire2_refutedBelow_of_allCells`:
  `GL06e.refutedBelowSection_of_innerPocketEnclosedCorrected_of_allCells`.
* `nmWire2_refutedBelow_of_nearestCellCut`:
  `GL06h3.refutedBelowSection_of_innerPocketEnclosedCorrected_of_nearestCellCut`.
* `nmWire2_refutedBelow_of_nearestCellPocket`:
  `GL06h4.refutedBelowSection_of_innerPocketEnclosedCorrected_of_nearestCellPocket`.
* `nmWire2_refutedBelow_of_shortPocket`:
  `GL06h4.gl06h4Nearest_refutedBelow_of_corrected_of_shortPocket`.
* `nmWire2_refutedBelow_of_descent`: `GL06h5.gl06h5_refutedBelow_of_corrected_of_descent`.
* `nmWire2_refutedBelow_of_shortBoundary`: the all-cells form after
  `GL06h3.allCellsShortEnclosedRefutedBelowSection_of_shortBoundarySection`.

This module is routing only.  It certifies no printed sentence on its own.
-/

namespace GroupApproximation.Full.NMWire2

universe u w v

open GroupApproximation.GGT GroupApproximation.GGT.VanKampen

section Input

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **The cell pocket walk binder is refuted below the inductive bound, at fixed parameters,
from the all-cells refutation alone** (Osin, proof of Lemma 9.7(b); `thm:hull`).  This is
`GL06e.refutedBelowInput_of_innerPocketEnclosedCorrected` with `hencl` discharged. -/
theorem nmWire2_refutedBelowInput_of_allCells
    {D : RelGenSet G Lambda} {W : Set (List (RelLetter G Lambda))} {eps rho : ℕ}
    {mu lambda c : ℝ}
    (hall : GroupApproximation.Full.GL06e.AllCellsShortEnclosedRefutedBelowInput.{u, w, v}
      D lambda c mu eps W)
    (hcondition : OsinCCondition D W eps mu lambda c rho)
    (hlambda : 0 < lambda) (hlambda1 : lambda ≤ 1) (hc : 0 ≤ c) (hmu : 0 < mu)
    (hmu1 : mu ≤ 1 / 16) (hrho : 2 ≤ rho)
    (hlarge : lambda⁻¹ * (3 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ)) :
    GroupApproximation.Full.GL06e.CellPocketWalkRefutedBelowInput.{u, w, v}
      D lambda c mu eps W :=
  GroupApproximation.Full.GL06e.refutedBelowInput_of_innerPocketEnclosedCorrected
    GroupApproximation.Full.GL03BPinch.innerPocketEnclosedTwoArcCorrected hall hcondition
    hlambda hlambda1 hc hmu hmu1 hrho hlarge

#audit_axioms GroupApproximation.Full.NMWire2.nmWire2_refutedBelowInput_of_allCells

end Input

/-- **GL06e's refutation below the section count from the all-cells refutation** (Osin, proof
of Lemma 9.7(b); `thm:hull`). -/
theorem nmWire2_refutedBelow_of_allCells
    (hall :
      GroupApproximation.Full.GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{u, w, v}) :
    GroupApproximation.Full.GL06e.CellPocketWalkRefutedBelowSectionStatement.{u, w, v} :=
  GroupApproximation.Full.GL06e.refutedBelowSection_of_innerPocketEnclosedCorrected_of_allCells
    GroupApproximation.Full.GL03BPinch.innerPocketEnclosedTwoArcCorrected hall

#audit_axioms GroupApproximation.Full.NMWire2.nmWire2_refutedBelow_of_allCells

/-- **GL06e's refutation below the section count from the nearest-cell cut** (`thm:hull`). -/
theorem nmWire2_refutedBelow_of_nearestCellCut
    (hcut : GroupApproximation.Full.GL06h3.NearestCellCutSectionStatement.{u, w, v}) :
    GroupApproximation.Full.GL06e.CellPocketWalkRefutedBelowSectionStatement.{u, w, v} :=
  GL06h3.refutedBelowSection_of_innerPocketEnclosedCorrected_of_nearestCellCut
    GroupApproximation.Full.GL03BPinch.innerPocketEnclosedTwoArcCorrected hcut

#audit_axioms GroupApproximation.Full.NMWire2.nmWire2_refutedBelow_of_nearestCellCut

/-- **GL06e's refutation below the section count from the slit pocket** (`thm:hull`). -/
theorem nmWire2_refutedBelow_of_nearestCellPocket
    (h : GroupApproximation.Full.GL06h4.NearestCellPocketStatement.{u, w, v}) :
    GroupApproximation.Full.GL06e.CellPocketWalkRefutedBelowSectionStatement.{u, w, v} :=
  GL06h4.refutedBelowSection_of_innerPocketEnclosedCorrected_of_nearestCellPocket
    GroupApproximation.Full.GL03BPinch.innerPocketEnclosedTwoArcCorrected h

#audit_axioms GroupApproximation.Full.NMWire2.nmWire2_refutedBelow_of_nearestCellPocket

/-- **GL06e's refutation below the section count from the short nearest pocket**
(`thm:hull`). -/
theorem nmWire2_refutedBelow_of_shortPocket
    (h : GroupApproximation.Full.GL06h4.gl06h4Nearest_shortPocketStatement.{u, w, v}) :
    GroupApproximation.Full.GL06e.CellPocketWalkRefutedBelowSectionStatement.{u, w, v} :=
  GroupApproximation.Full.GL06h4.gl06h4Nearest_refutedBelow_of_corrected_of_shortPocket
    GroupApproximation.Full.GL03BPinch.innerPocketEnclosedTwoArcCorrected h

#audit_axioms GroupApproximation.Full.NMWire2.nmWire2_refutedBelow_of_shortPocket

/-- **GL06e's refutation below the section count from the descent** (`thm:hull`). -/
theorem nmWire2_refutedBelow_of_descent
    (h : GroupApproximation.Full.GL06h5.gl06h5_descentPocketStatement.{u, w, v}) :
    GroupApproximation.Full.GL06e.CellPocketWalkRefutedBelowSectionStatement.{u, w, v} :=
  GroupApproximation.Full.GL06h5.gl06h5_refutedBelow_of_corrected_of_descent
    GroupApproximation.Full.GL03BPinch.innerPocketEnclosedTwoArcCorrected h

#audit_axioms GroupApproximation.Full.NMWire2.nmWire2_refutedBelow_of_descent

/-- **GL06e's refutation below the section count from the short-boundary refutation**
(`thm:hull`). -/
theorem nmWire2_refutedBelow_of_shortBoundary
    (h : GroupApproximation.Full.GL06h3.ShortBoundaryRefutedBelowSectionStatement.{u, w, v}) :
    GroupApproximation.Full.GL06e.CellPocketWalkRefutedBelowSectionStatement.{u, w, v} :=
  nmWire2_refutedBelow_of_allCells
    (GroupApproximation.Full.GL06h3.allCellsShortEnclosedRefutedBelowSection_of_shortBoundarySection
      h)

#audit_axioms GroupApproximation.Full.NMWire2.nmWire2_refutedBelow_of_shortBoundary

end GroupApproximation.Full.NMWire2
