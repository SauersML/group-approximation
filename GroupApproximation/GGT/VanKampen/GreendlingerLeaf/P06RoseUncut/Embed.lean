import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06RoseUncut.Move
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06, uncut rose: a closed cut is an in-place sub-walk move

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).

## The mathematics

Let `K` be a cell pocket between `i ≠ j` in walk order with proper arcs, and let
`c = A ++ (B ++ C)` be a closed cut (`Piece06.CellCut K`), with relator cell `k` in the lobe of the
rest `A ++ C`.  Then `p06RoseUncut_Move K` holds with

* face set `lobeFaces c (A ++ C)`, kept cell `k`, the cells `i`, `j` and the arcs of `K`,
* `L = A ++ C`, `L' = B`; `c ~ (A ++ C) ++ B` (`List.perm_append_comm_assoc`),
* `L` lists the boundary darts of its lobe: the rest is closed for the face-class relation
  (`P10Rose.closed_right`), so `P10Rose.isBoundaryDart_lobeFaces_iff` applies,
* the exterior face is off the lobe, since the lobe lies in `K.faces`
  (`P10Rose.mem_faces_of_mem_lobeFaces`),
* `L` is a closed dart walk: `B ++ (C ++ A)` is one, and its two parts start at one vertex
  (`P10Rose.closedDartWalk_split`, `IsClosedDartWalk.append_comm`),
* the shared vertex: the head of `C ++ A` (a dart of `L`) and the head of `B`.

So every configuration handled by `Piece06.exists_step_of_cellCut'` is also handled by
`p06RoseUncut_exists_step_of_move`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides OuterPinchIsolated

section Embed

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **A closed cut is an in-place sub-walk move**: the rest of the cut is the new walk `L`, the cut
sub-walk is `L'`, and the new face set is the lobe of the rest. -/
theorem p06RoseUncut_move_of_cellCut {K : CellPocketFaceSet D eps X i j} (hij : i ≠ j)
    (hK : K.ClosedWalk) (hfirst : K.firstArc.length < (cellDarts X i).length)
    (hsecond : K.secondArc.length < (cellDarts X j).length) (hcut : CellCut K) :
    p06RoseUncut_Move K := by
  obtain ⟨A, B, C, s₁, s₂, hB, hrest, k, hc, hv, hclosed, hdec, hs₁, hs₂, hk⟩ := hcut
  have hperm₀ : List.Perm K.boundary.cycle (B ++ (A ++ C)) := by
    rw [hc]
    exact List.perm_append_comm_assoc _ _ _
  have hperm : List.Perm K.boundary.cycle ((A ++ C) ++ B) :=
    hperm₀.trans List.perm_append_comm
  have hL' : ∀ d ∈ A ++ C, d ∈ K.boundary.cycle := fun d hd =>
    hperm.mem_iff.mpr (List.mem_append_left _ hd)
  have hy : (C ++ A).head hrest ∈ A ++ C :=
    List.perm_append_comm.mem_iff.mp (List.head_mem hrest)
  have hw0 : IsClosedDartWalk X.toCombMap (A ++ (B ++ C)) := by
    rw [← hc]
    exact ⟨K.boundary.cycle_nonempty, hK.1, hK.2⟩
  have hw1 : IsClosedDartWalk X.toCombMap (B ++ (C ++ A)) := by
    have h := hw0.append_comm
    rwa [List.append_assoc] at h
  obtain ⟨-, hwR⟩ := P10Rose.closedDartWalk_split hw1 hB hrest hv
  have hwL' : IsClosedDartWalk X.toCombMap (A ++ C) := hwR.append_comm
  have hclosed' := P10Rose.closed_right hperm₀ K.boundary.cycle_nodup hclosed
  have hmem : ∀ d, d ∈ A ++ C ↔ Surgery.MapCollapse.IsBoundaryDart X.toCombMap
      (P10Rose.lobeFaces X.toCombMap K.boundary.cycle (A ++ C)) d := fun d =>
    (P10Rose.isBoundaryDart_lobeFaces_iff K.boundary.cycle_mem_iff hL' hclosed' d).symm
  exact ⟨P10Rose.lobeFaces X.toCombMap K.boundary.cycle (A ++ C), k, i, j, K.firstArc,
    K.secondArc, s₁, s₂, A ++ C, B, hij,
    fun h => K.outerFace_not_mem
      (P10Rose.mem_faces_of_mem_lobeFaces K.boundary.cycle_mem_iff hL' h),
    hk, hperm, hmem, hdec, K.firstArc_pos, K.secondArc_pos, hfirst, hsecond, hs₁, hs₂, hwL',
    (C ++ A).head hrest, hy, B.head hB, List.head_mem hB, hv.symm⟩

#audit_axioms p06RoseUncut_move_of_cellCut

/-- **No in-place sub-walk move leaves no closed cut**, for a cell pocket in walk order between
distinct cells with proper arcs. -/
theorem p06RoseUncut_not_cellCut_of_not_move {K : CellPocketFaceSet D eps X i j} (hij : i ≠ j)
    (hK : K.ClosedWalk) (hfirst : K.firstArc.length < (cellDarts X i).length)
    (hsecond : K.secondArc.length < (cellDarts X j).length) (hmove : ¬ p06RoseUncut_Move K) :
    ¬ CellCut K := fun hcut =>
  hmove (p06RoseUncut_move_of_cellCut hij hK hfirst hsecond hcut)

#audit_axioms p06RoseUncut_not_cellCut_of_not_move

end Embed

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06
