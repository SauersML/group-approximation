import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06RoseRedraw.Split
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06RoseUncut.Move
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.Residual
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.MonogonCorner
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06, rose redraw: stuck pockets, and the step from a competing pocket

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2` between two regions joining two cells.

A cell pocket `K` of `X` between `i ≠ j`, in walk order with both arcs proper, is **stuck**
(`p06RoseRedraw_Stuck K`) when no proved step applies to it:

* every non-first turn is crossed (otherwise `exists_step_of_goodCorners`, or
  `exists_step_of_badCorners` from the proved `MonogonCorner.badCornerRefinement`);
* it has no closed cut (otherwise `exists_step_of_cellCut'`);
* it has no in-place sub-walk move (otherwise `p06RoseUncut_exists_step_of_move`);
* it has no good first-turn split (otherwise `p06RoseRedraw_step_split`).

`p06RoseRedraw_step_notStuck` performs the step for a pocket that is not stuck.

The step is only asked to lower the repeated visits of the *original* pocket `K`.  So any
**competing** pocket `K₂` of the same diagram `X` (any two distinct cells, walk order, proper arcs)
with `K₂.repeatedVisits ≤ K.repeatedVisits` that is not stuck gives the step for `K`:
`p06RoseRedraw_step_notAll`.  `p06RoseRedraw_AllStuck K` says every such competitor is stuck.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides OuterPinchIsolated
open scoped Classical

section Stuck

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **A stuck cell pocket**: every non-first turn is crossed, there is no closed cut, no in-place
sub-walk move and no good first-turn split. -/
def p06RoseRedraw_Stuck (K : CellPocketFaceSet D eps X i j) : Prop :=
  AllNonFirstTurnsCrossed K ∧ ¬ CellCut K ∧ ¬ p06RoseUncut_Move K ∧
    ¬ p06RoseRedraw_TurnSplit K

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.p06RoseRedraw_Stuck

/-- **The cell-pinch step for a pocket that is not stuck.** -/
theorem p06RoseRedraw_step_notStuck
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (K : CellPocketFaceSet D eps X i j) (hK : K.ClosedWalk) (hij : i ≠ j)
    (hfirst : K.firstArc.length < (cellDarts X i).length)
    (hsecond : K.secondArc.length < (cellDarts X j).length) (h : ¬ p06RoseRedraw_Stuck K) :
    ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
      (K' : CellPocketFaceSet D eps X' i' j'),
      Nonempty (OEquivalentDiscDiagram X X') ∧
        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ i' ≠ j' ∧
        K'.ClosedWalk ∧ K'.firstArc.length < (cellDarts X' i').length ∧
        K'.secondArc.length < (cellDarts X' j').length ∧
        K'.repeatedVisits < K.repeatedVisits := by
  by_cases hrose : AllNonFirstTurnsCrossed K
  · by_cases hcut : CellCut K
    · exact exists_step_of_cellCut' hlabel K hK hij hfirst hsecond hcut
    · by_cases hmove : p06RoseUncut_Move K
      · exact p06RoseUncut_exists_step_of_move hlabel K hmove
      · by_cases hsplit : p06RoseRedraw_TurnSplit K
        · exact p06RoseRedraw_step_split hlabel K hij hfirst hsecond hsplit
        · exact (h ⟨hrose, hcut, hmove, hsplit⟩).elim
  · obtain ⟨d₀, hd₀, hnf, hnc⟩ := exists_uncrossed_of_not_allCrossed hrose
    by_cases hgood : GoodTurnCorners X d₀ (K.boundary.cycle.next d₀ hd₀)
    · exact exists_step_of_goodCorners hlabel K hK hij hfirst hsecond hd₀ rfl hnf
        (huncross_of_not_turnCrossed hnc) hgood
    · exact exists_step_of_badCorners MonogonCorner.badCornerRefinement hlabel K hK hij hfirst
        hsecond hd₀ rfl hnf (huncross_of_not_turnCrossed hnc) hgood

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.p06RoseRedraw_step_notStuck

/-- **Every competing pocket is stuck**: every cell pocket `K₂` of the same diagram between two
distinct cells, in walk order, with both arcs proper and at most the repeated visits of `K`, is
stuck.  (`K₂ = K` is one of them.) -/
def p06RoseRedraw_AllStuck (K : CellPocketFaceSet D eps X i j) : Prop :=
  ∀ (i₂ j₂ : Fin X.rCellCount) (K₂ : CellPocketFaceSet D eps X i₂ j₂), i₂ ≠ j₂ →
    K₂.ClosedWalk → K₂.firstArc.length < (cellDarts X i₂).length →
      K₂.secondArc.length < (cellDarts X j₂).length →
        K₂.repeatedVisits ≤ K.repeatedVisits → p06RoseRedraw_Stuck K₂

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.p06RoseRedraw_AllStuck

/-- **The cell-pinch step from a competing pocket that is not stuck**: its step lowers the repeated
visits below those of the competitor, hence below those of `K`. -/
theorem p06RoseRedraw_step_notAll
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (K : CellPocketFaceSet D eps X i j) (h : ¬ p06RoseRedraw_AllStuck K) :
    ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
      (K' : CellPocketFaceSet D eps X' i' j'),
      Nonempty (OEquivalentDiscDiagram X X') ∧
        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ i' ≠ j' ∧
        K'.ClosedWalk ∧ K'.firstArc.length < (cellDarts X' i').length ∧
        K'.secondArc.length < (cellDarts X' j').length ∧
        K'.repeatedVisits < K.repeatedVisits := by
  by_contra hno
  refine h fun i₂ j₂ K₂ hij₂ hK₂ hfirst₂ hsecond₂ hle => ?_
  by_contra hbad
  obtain ⟨X', i', j', K', hO, hl, hne, hK', h₁, h₂, hlt⟩ :=
    p06RoseRedraw_step_notStuck hlabel K₂ hK₂ hij₂ hfirst₂ hsecond₂ hbad
  exact hno ⟨X', i', j', K', hO, hl, hne, hK', h₁, h₂, lt_of_lt_of_le hlt hle⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.p06RoseRedraw_step_notAll

end Stuck

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06
