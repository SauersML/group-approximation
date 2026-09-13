import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerTwoGonPocketFaces
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerTwoGonNoncrossingRoute
import GroupApproximation.GGT.VanKampen.BoundaryCycleFaceClass
import GroupApproximation.Meta.AxiomGuard

/-!
# The walk hypotheses of a two-gon pocket whose inner cycle follows

Osin, arXiv:math/0411039v3, Appendix, proof of Lemma 9.3, the assumption that "inside every 2-gon of
`Φ′_M`, there is a vertex of `Φ_M`".

`TwoGonWalkHyp a b i walk` (`Estimating/OsinAppendixEulerTwoGonPocketFaces`, lane
`debt-conditional`) collects the hypotheses on a closed walk around the pocket of a two-gon.  Its
consumers are `ExtPhiData.cell_face_not_mem_sideFaces_of_twoGon` (`hno`) and
`ExtPhiData.disjoint_sideFaces_of_twoGon` (`havoid`).  This module supplies three of the six
fields for a noncrossing walk whose inner cycle follows its boundary:
* `outer_off`: the exterior face is off the side, from a dart of the target arc
  (`outerFace_not_mem_sideFaces_of_target_mem`);
* `cell_off`: the face of the cell is off the side, from a dart of the source arc read backwards
  (`cellFace_not_mem_sideFaces_of_source_mem`);
* `connected`: the walk lies in one face class of the walk
  (`IsNoncrossingClosedWalk.eqvGen_of_mem_of_innerFollows`).

The three fields `left_side`, `right_side` and `base` read the regions along the walk.  Lane
`w1-binder-1` builds them; `twoGonWalkHyp_of_innerFollows` takes them as hypotheses.

When only the outer cycle follows (Configuration A, the pinched two-gon), `connected` can fail: the
two lobes share no edge.  That case is not covered here.

## Manuscript status

Infrastructure for `thm:hull` (through Osin's Lemma 9.7(a)); certifies no printed sentence on its
own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded SimpleClosedWalkSides

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **The face of a cell is off the side of a noncrossing walk through a backward arc of it.**  A
dart of a nonempty arc of the cell lies on the face of the cell, and its reverse lies on the walk,
so the face across that reverse, the face of the cell, is off the side of the walk. -/
theorem cellFace_not_mem_sideFaces_of_source_mem {W : Set (List (RelLetter G Lambda))}
    {X : DiscDiagram.{u, w, v} W} {walk : List X.toCombMap.Dart}
    (hw : IsNoncrossingClosedWalk X.toCombMap walk) {i : Fin X.rCellCount}
    (source : CyclicArc (cellDarts X i)) (hpos : 0 < source.length)
    (hsub : ∀ d ∈ source.reverseDarts, d ∈ walk) :
    (cell X i).face ∉ sideFaces X.toCombMap walk := by
  obtain ⟨d, hd⟩ := source.exists_mem_darts hpos
  have hface : X.toCombMap.faceOf d = (cell X i).face :=
    ((X.faceBoundary (cell X i).face).mem_iff d).mp (source.mem_cycle_of_mem_darts hd)
  have hrev : X.toCombMap.alpha d ∈ walk := hsub _ (by
    simp only [CyclicArc.reverseDarts, List.mem_map, List.mem_reverse]
    exact ⟨d, hd, rfl⟩)
  have h := And.right ((hw.isBoundaryDart_sideFaces_iff X.planar _).mpr hrev)
  rwa [X.toCombMap.alpha_involutive d, hface] at h

/-- **The walk hypotheses of a two-gon pocket whose inner cycle follows its boundary.**  Let `walk`
be a noncrossing closed walk of the diagram whose inner cycle follows its boundary.  Suppose it holds
a reversed nonempty arc of the cell `i` and a nonempty arc of the oriented outer boundary.  Then the
fields `outer_off`, `cell_off` and `connected` of `TwoGonWalkHyp` hold.  Together with `left_side`,
`right_side` and `base`, supplied as hypotheses, they give `TwoGonWalkHyp a b i walk`. -/
theorem twoGonWalkHyp_of_innerFollows {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {a b : RegionCandidate D eps Delta} {i : Fin Delta.rCellCount}
    {walk : List Delta.toCombMap.Dart} (hw : IsNoncrossingClosedWalk Delta.toCombMap walk)
    (hin : (hw.innerCycle Delta.planar).FollowsBoundary)
    (source : CyclicArc (cellDarts Delta i)) (hposS : 0 < source.length)
    (hsubS : ∀ d ∈ source.reverseDarts, d ∈ walk)
    (target : CyclicArc (targetDarts Delta none)) (hposT : 0 < target.length)
    (hsubT : ∀ d ∈ target.darts, d ∈ walk)
    (hleft : ∀ d ∈ a.2.boundary.cycle, ¬ walkKeep Delta.toCombMap walk d → d ∈ a.2.leftSide)
    (hright : ∀ d ∈ b.2.boundary.cycle, ¬ walkKeep Delta.toCombMap walk d → d ∈ b.2.rightSide)
    (hbase : ∃ d ∈ walk, Delta.toCombMap.faceOf d ∈ a.1) :
    RegionCandidate.TwoGonWalkHyp a b i walk where
  left_side := hleft
  right_side := hright
  outer_off := outerFace_not_mem_sideFaces_of_target_mem hw target hposT hsubT
  cell_off := cellFace_not_mem_sideFaces_of_source_mem hw source hposS hsubS
  connected := fun _ hd _ he => hw.eqvGen_of_mem_of_innerFollows Delta.planar hin hd he
  base := hbase

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.cellFace_not_mem_sideFaces_of_source_mem
#audit_axioms GroupApproximation.GGT.VanKampen.twoGonWalkHyp_of_innerFollows
