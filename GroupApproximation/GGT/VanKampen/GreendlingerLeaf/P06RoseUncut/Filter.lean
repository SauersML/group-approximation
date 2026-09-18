import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06RoseUncut.Move
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.LakesBelowFilter
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06, uncut rose: an in-place filter move is an in-place sub-walk move

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).

## The mathematics

Let `K` be a cell pocket between `i ≠ j` with proper arcs, and let `(F', kept, p)` be an in-place
region-union move (`Piece06.CellFilterMove K`: fill some lakes, drop some petals).  Then
`p06RoseUncut_Move K` holds with

* face set `F'`, the kept cell of the move, the cells `i`, `j` and the arcs of `K`,
* `L = c.filter p = s₁.filter p ++ t̄₁ ++ s₂.filter p ++ t̄₂` (`Piece06.filter_cycle_eq_cell`),
  `L' = c.filter (¬ p)`, and `c ~ L ++ L'` (`List.filter_append_perm`),
* the sides of `L` are filters of the sides of `K`, so no longer than `ε` (`List.length_filter_le`),
* `L` lists the boundary darts of `F'` and is a closed dart walk, by the move,
* the kept dart and the removed dart of the move share their vertex.

So every configuration handled by `Piece06.exists_step_of_cellFilterMove'` is also handled by
`p06RoseUncut_exists_step_of_move`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides OuterPinchIsolated

section Filter

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **An in-place filter move is an in-place sub-walk move**: the kept darts are the new walk
`L`, the removed darts are `L'`. -/
theorem p06RoseUncut_move_of_cellFilterMove {K : CellPocketFaceSet D eps X i j} (hij : i ≠ j)
    (hfirst : K.firstArc.length < (cellDarts X i).length)
    (hsecond : K.secondArc.length < (cellDarts X j).length) (hmove : CellFilterMove K) :
    p06RoseUncut_Move K := by
  obtain ⟨faces, kept, p, hout, hkept, hbd, ht₁, ht₂, hwalk, x, hx, y, hy, hpx, hpy, hxy⟩ := hmove
  have hfilt := filter_cycle_eq_cell K p ht₁ ht₂
  have hperm : List.Perm K.boundary.cycle ((K.firstSide.filter p ++
      invDarts X K.firstArc.darts ++ K.secondSide.filter p ++ invDarts X K.secondArc.darts) ++
      K.boundary.cycle.filter (fun d => !p d)) := by
    rw [← hfilt]
    exact (List.filter_append_perm p K.boundary.cycle).symm
  have hmem : ∀ d, d ∈ K.firstSide.filter p ++ invDarts X K.firstArc.darts ++
      K.secondSide.filter p ++ invDarts X K.secondArc.darts ↔
      Surgery.MapCollapse.IsBoundaryDart X.toCombMap faces d := by
    intro d
    rw [← hfilt, List.mem_filter, hbd]
  have hx' : x ∈ K.firstSide.filter p ++ invDarts X K.firstArc.darts ++
      K.secondSide.filter p ++ invDarts X K.secondArc.darts := by
    rw [← hfilt]
    exact List.mem_filter.mpr ⟨hx, hpx⟩
  have hy' : y ∈ K.boundary.cycle.filter (fun d => !p d) :=
    List.mem_filter.mpr ⟨hy, by simp [hpy]⟩
  have hwalk' : IsClosedDartWalk X.toCombMap (K.firstSide.filter p ++
      invDarts X K.firstArc.darts ++ K.secondSide.filter p ++ invDarts X K.secondArc.darts) := by
    rw [← hfilt]
    exact hwalk
  have hs₁ : (K.firstSide.filter p).length ≤ eps :=
    (List.length_filter_le p _).trans K.firstSide_length_le
  have hs₂ : (K.secondSide.filter p).length ≤ eps :=
    (List.length_filter_le p _).trans K.secondSide_length_le
  exact ⟨faces, kept, i, j, K.firstArc, K.secondArc, K.firstSide.filter p,
    K.secondSide.filter p, _, _, hij, hout, hkept, hperm, hmem, rfl, K.firstArc_pos,
    K.secondArc_pos, hfirst, hsecond, hs₁, hs₂, hwalk', x, hx', y, hy', hxy⟩

#audit_axioms p06RoseUncut_move_of_cellFilterMove

/-- **No in-place sub-walk move leaves no in-place filter move**, for a cell pocket between
distinct cells with proper arcs. -/
theorem p06RoseUncut_not_cellFilterMove_of_not_move {K : CellPocketFaceSet D eps X i j}
    (hij : i ≠ j) (hfirst : K.firstArc.length < (cellDarts X i).length)
    (hsecond : K.secondArc.length < (cellDarts X j).length) (hmove : ¬ p06RoseUncut_Move K) :
    ¬ CellFilterMove K := fun hf =>
  hmove (p06RoseUncut_move_of_cellFilterMove hij hfirst hsecond hf)

#audit_axioms p06RoseUncut_not_cellFilterMove_of_not_move

end Filter

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06
