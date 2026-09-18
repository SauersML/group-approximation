import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.Predicate
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellPinchFirstTurn
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06, rose redraw: the split at a good first turn, with proper arcs and distinct cells

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2` between two regions joining two cells.

`CellPocketFaceSet.exists_firstTurnStep_of_turn` (`Estimating/OsinPocketCellPinchFirstTurn`)
splits a cell pocket in first-turn order at a turn `d₀ → e₀` into a vertex visited twice, when the
darts of the turn lie on distinct faces other than relator faces.  Its conclusion forgets the two
cells.  Here the same split `K.pinchSplitInside I hs` is kept in the form of a cell-pinch step
(`p06RoseRedraw_step_split`):

* the cells are `I.cellMap.indexEquiv i ≠ I.cellMap.indexEquiv j`;
* first-turn order survives (`firstTurns_pinchSplitInside`), so walk order does;
* both arcs keep their length (`CyclicArc.mapTo_length`), and so do the cell boundaries
  (`PinchSplit.Input.cellDarts_eq`), so both arcs stay proper;
* the repeated visits drop (`pinchSplitInside_repeatedVisits_lt_of_turn`).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides OuterPinchIsolated
open scoped Classical

section Split

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **A good first-turn split**: `K` is in first-turn order, and it has a turn `d₀ → e₀` into a
vertex visited twice (by a dart `e ≠ e₀` of the cycle) whose darts lie on distinct faces other than
relator faces. -/
def p06RoseRedraw_TurnSplit (K : CellPocketFaceSet D eps X i j) : Prop :=
  K.FirstTurns ∧ ∃ d₀ ∈ K.boundary.cycle, ∃ e₀ ∈ K.boundary.cycle, ∃ e ∈ K.boundary.cycle,
    e ≠ e₀ ∧ X.toCombMap.vertexOf e = X.toCombMap.vertexOf e₀ ∧
      FirstTurn X.toCombMap (K.boundary.cycle.reverse.map X.toCombMap.alpha)
        (X.toCombMap.alpha e₀) (X.toCombMap.alpha d₀) ∧
      X.toCombMap.faceOf d₀ ≠ X.toCombMap.faceOf e₀ ∧
      (∀ C ∈ X.relatorCells, C.face ≠ X.toCombMap.faceOf d₀) ∧
      ∀ C ∈ X.relatorCells, C.face ≠ X.toCombMap.faceOf e₀

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.p06RoseRedraw_TurnSplit

/-- **The cell-pinch step at a good first-turn split**: the split at the end of the turn, in an
O-equivalent copy, between the transported cells, with both arcs proper. -/
theorem p06RoseRedraw_step_split
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (K : CellPocketFaceSet D eps X i j) (hij : i ≠ j)
    (hfirst : K.firstArc.length < (cellDarts X i).length)
    (hsecond : K.secondArc.length < (cellDarts X j).length) (h : p06RoseRedraw_TurnSplit K) :
    ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
      (K' : CellPocketFaceSet D eps X' i' j'),
      Nonempty (OEquivalentDiscDiagram X X') ∧
        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ i' ≠ j' ∧
        K'.ClosedWalk ∧ K'.firstArc.length < (cellDarts X' i').length ∧
        K'.secondArc.length < (cellDarts X' j').length ∧
        K'.repeatedVisits < K.repeatedVisits := by
  obtain ⟨hK, d₀, hd₀, e₀, he₀, e, he, hne, hv, hturn, hface, hcell₀, hcell₁⟩ := h
  obtain ⟨k₀, -, hk₀, hkeep₀⟩ := FirstTurn.reverse_map_alpha_iff.mp hturn
  obtain ⟨I, hx, hy, hs⟩ := K.exists_turnInput hd₀ he₀ hk₀ hface hcell₀ hcell₁
  have h₁ : (K.pinchSplitInside I hs).firstArc.length = K.firstArc.length :=
    K.firstArc.mapTo_length id (I.cellDarts_eq i)
  have h₂ : (K.pinchSplitInside I hs).secondArc.length = K.secondArc.length :=
    K.secondArc.mapTo_length id (I.cellDarts_eq j)
  have c₁ : (cellDarts I.diagram (I.cellMap.indexEquiv i)).length = (cellDarts X i).length :=
    (congrArg List.length (I.cellDarts_eq i)).trans (List.length_map _)
  have c₂ : (cellDarts I.diagram (I.cellMap.indexEquiv j)).length = (cellDarts X j).length :=
    (congrArg List.length (I.cellDarts_eq j)).trans (List.length_map _)
  exact ⟨I.diagram, I.cellMap.indexEquiv i, I.cellMap.indexEquiv j, K.pinchSplitInside I hs,
    ⟨I.oEquivalent⟩, I.label_isLetter (symmetricLabelAlphabet D) hlabel,
    I.cellMap.indexEquiv.injective.ne hij,
    (K.firstTurns_pinchSplitInside I hs hd₀ he₀ hx hy hK).closedWalk,
    lt_of_eq_of_lt h₁ (lt_of_lt_of_eq hfirst c₁.symm),
    lt_of_eq_of_lt h₂ (lt_of_lt_of_eq hsecond c₂.symm),
    K.pinchSplitInside_repeatedVisits_lt_of_turn I hs hd₀ he₀ hx hy hk₀ hkeep₀ he hne hv⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.p06RoseRedraw_step_split

end Split

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06
