import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06RoseRedraw.Stuck
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06RoseUncut.Residual
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06, rose redraw: the uncut rose when every competing pocket is stuck

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2` between two regions joining two cells.

Target: `p06RoseUncut_NoMoveStatement` (`P06RoseUncut/Residual`), OPEN.  This module does not
close it.  It isolates the residual `p06RoseRedraw_RoseStatement` and proves the reduction
`p06RoseRedraw_noMove_of_rose`, hence `CellRoseUncutStatement` from the residual
(`p06RoseRedraw_uncut_of_rose`).

## The residual

`p06RoseRedraw_RoseStatement` has the hypotheses of `CellRoseUncutStatement`, except that
`AllNonFirstTurnsCrossed K`, `¬ CellCut K` and `¬ p06RoseUncut_Move K` are replaced by the single
hypothesis `p06RoseRedraw_AllStuck K` (module `P06RoseRedraw/Stuck`).  It says that *every*
competing cell pocket `K₂` of the same diagram `X` (any two distinct cells, walk order, both arcs
proper, `K₂.repeatedVisits ≤ K.repeatedVisits`) is stuck:

* every non-first turn of `K₂` is crossed;
* `K₂` has no closed cut;
* `K₂` has no in-place sub-walk move;
* `K₂` has no good first-turn split (`p06RoseRedraw_TurnSplit`: first-turn order and a turn into
  a vertex visited twice on distinct faces other than relator faces).

The conclusion is the step conclusion, unchanged.

## Proof content discharged by the reduction

`p06RoseRedraw_noMove_of_rose` goes by cases on `p06RoseRedraw_AllStuck K`.  If some competitor
`K₂` is not stuck, `p06RoseRedraw_step_notAll` performs its step (lowering the repeated visits
below those of `K₂`, hence below those of `K`) through:

* `exists_step_of_goodCorners`, or `exists_step_of_badCorners` with the proved
  `MonogonCorner.badCornerRefinement`, at an uncrossed non-first turn of `K₂`;
* `exists_step_of_cellCut'` for a closed cut of `K₂`;
* `p06RoseUncut_exists_step_of_move` for an in-place move of `K₂`;
* `p06RoseRedraw_step_split` (new, module `P06RoseRedraw/Split`) for a good first-turn split of
  `K₂`: the vertex splitting of `Estimating/OsinPocketCellPinchFirstTurn`, kept between the
  transported cells with both arcs proper.

## Why the residual is not stronger, and is strictly smaller in proof content

* It follows from the target: `p06RoseRedraw_rose_of_noMove` (proved) applies
  `p06RoseRedraw_AllStuck K` to `K₂ = K` to recover the three dropped hypotheses.  So it is true
  whenever the target is true.
* The target constrains only `K`.  The residual also constrains every competitor.  So it drops
  every configuration of the target that has a steppable competitor.  Example (checked on paper):
  the three-petal rose (module docstring of `Piece06/RoseCut`, petals `P_1`, `P_k`, `P_2` at the
  pinch vertex `v`, in the crossed order `1, k, 2`).  It is in the target's scope: every
  non-first turn is crossed, and it has no closed cut and no move (`P06RoseUncut/Residual`).
  Reorder the petal loops of the same boundary darts as `1, 2, k`, with the side through `P_k`.
  When that side fits the side bound (`|y₂| + |L_k| + |x₁| ≤ ε` in the notation of the model),
  this is a competing pocket `K₂`.  It has the same face set, the same arcs, and a permutation of
  the same cycle, hence the same repeated visits.  `K₂` is in first-turn order.  The turn from the
  loop of `P_1` into the loop of `P_2` enters `v`, which is visited again, on faces of two
  different petals.  When the two corner faces are not relator faces, this turn is a good
  first-turn split.  So `K₂` is not stuck, and the residual does not contain this rose.  The
  target does.
* `¬ K.FirstTurns`, `LeastArea` and `¬ Unpinched` are kept as in the target.  Nothing is
  re-added, and no binder is renamed into an equivalent.

## Truth check (LOUD)

The residual follows from the target, so it is true if the target is.  **CAUTION: the truth of
the target itself (`p06RoseUncut_NoMoveStatement`, unconditionally) is doubtful and unverified.**
Consider the unbalanced three-petal rose, where no reordering of the petal loops fits the side
bound `ε`.  There, every competitor may be stuck, and the step must come from a genuine redraw of
the diagram to an O-equivalent copy with fewer repeated visits.  No such redraw is known.  If
none exists, the target and this residual are both false for that model.  This has not been
decided either way.

## Remaining gap

The residual keeps exactly the uncut roses in which every competing pocket of the same diagram
is stuck, such as the unbalanced three-petal rose.  The step there needs a planar re-drawing
(surgery) of the rose, and there is no such construction in the library.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides OuterPinchIsolated
open scoped Classical

/-- **The uncut rose step when every competing pocket is stuck** (OPEN residual).  The hypotheses
of `CellRoseUncutStatement`, with `AllNonFirstTurnsCrossed K ∧ ¬ CellCut K` (and the absence of
an in-place move) replaced by `p06RoseRedraw_AllStuck K`. -/
def p06RoseRedraw_RoseStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (i j : Fin X.rCellCount),
    i ≠ j → X.LeastArea → (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : CellPocketFaceSet D eps X i j, K.ClosedWalk → ¬ K.FirstTurns →
      K.firstArc.length < (cellDarts X i).length →
      K.secondArc.length < (cellDarts X j).length →
      ¬Unpinched X.toCombMap K.faces → p06RoseRedraw_AllStuck K →
        ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
          (K' : CellPocketFaceSet D eps X' i' j'),
          Nonempty (OEquivalentDiscDiagram X X') ∧
            (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ i' ≠ j' ∧
            K'.ClosedWalk ∧ K'.firstArc.length < (cellDarts X' i').length ∧
            K'.secondArc.length < (cellDarts X' j').length ∧
            K'.repeatedVisits < K.repeatedVisits

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.p06RoseRedraw_RoseStatement

/-- **The uncut rose step without a move, from the residual**: by cases on whether every
competing pocket is stuck. -/
theorem p06RoseRedraw_noMove_of_rose (h : p06RoseRedraw_RoseStatement.{u, w, v}) :
    p06RoseUncut_NoMoveStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j hij hlea hlabel K hK hnft hfirst hsecond hpinch _ _ _
  by_cases hall : p06RoseRedraw_AllStuck K
  · exact h D eps X i j hij hlea hlabel K hK hnft hfirst hsecond hpinch hall
  · exact p06RoseRedraw_step_notAll hlabel K hall

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.p06RoseRedraw_noMove_of_rose

/-- **The residual follows from the target**: `p06RoseRedraw_AllStuck K` at `K₂ = K` gives the
three hypotheses it replaces.  So the residual is not stronger than the target. -/
theorem p06RoseRedraw_rose_of_noMove (h : p06RoseUncut_NoMoveStatement.{u, w, v}) :
    p06RoseRedraw_RoseStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j hij hlea hlabel K hK hnft hfirst hsecond hpinch hall
  obtain ⟨hrose, hcut, hmove, -⟩ := hall i j K hij hK hfirst hsecond le_rfl
  exact h D eps X i j hij hlea hlabel K hK hnft hfirst hsecond hpinch hrose hcut hmove

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.p06RoseRedraw_rose_of_noMove

/-- **The uncut rose step from the residual**, through `p06RoseUncut_cellRoseUncut_of_noMove`. -/
theorem p06RoseRedraw_uncut_of_rose (h : p06RoseRedraw_RoseStatement.{u, w, v}) :
    CellRoseUncutStatement.{u, w, v} :=
  p06RoseUncut_cellRoseUncut_of_noMove (p06RoseRedraw_noMove_of_rose h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.p06RoseRedraw_uncut_of_rose

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06
