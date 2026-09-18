import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06RoseRedraw.Residual
import GroupApproximation.GGT.VanKampen.Estimating.Assembly
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06, rose decision: the unbalanced rose is redrawn by corpus surgeries

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2` between two regions joining two cells.

## Truth check: the unbalanced three-petal rose is NOT a counterexample

The module docstring of `P06RoseRedraw/Residual` leaves open whether the unbalanced three-petal
rose refutes `p06RoseRedraw_RoseStatement`.  It does not.  The conclusion holds there, in an
O-equivalent redraw built only from corpus surgeries.  This was checked on an explicit
combinatorial model, not in Lean.

The model:

* the group `G` is free on the letters, `Lambda` is empty, and `eps = 3`;
* cell `i` is `a b c p q r`, cell `k` is `d e f`, and cell `j` is `h m u v w g`, all on disjoint
  letters, so `X.LeastArea` holds by abelianizing;
* the petals are `P_1` (a G-digon on the arc `t_1 = a` of `i`), `P_k` (the loop `d e f`) and
  `P_2` (a G-digon on the arc `t_2 = g` of `j`), glued at one vertex `v`;
* the exterior order of the lobes is `1, k, 2`, with boundary word `r_j r_k r_i`;
* `K` has faces `{P_1, k, P_2}`, the cycle `y₂ x₁ t₁⁻ k₁ k₂ k₃ t₂⁻`, sides of lengths `2` and `3`,
  `repeatedVisits = 2`, and it is not in first-turn order;
* the first-turn order has a side of length `5 > eps`, so the rose is unbalanced;
* no cell pocket of `X` itself has `repeatedVisits ≤ 1`.

The redraw:

1. Apply `FaceEdgeDoubling` to the last dart `r` of `i` and the first dart `h` of `j`.  The new
   digons are `D_r` and `D_h`, and the new edges `n_r` and `n_h` are now darts of the cells.
2. Take the competitor `K₂` with faces `{k, D_r, D_h}`, arcs `[n_r] ⊂ i` and `[n_h] ⊂ j`, and the
   cycle `k₁ k₂ k₃ n_r⁻ r h n_h⁻` (sides `d e f` and `r h`).
3. `K₂` has `repeatedVisits = 2`, it is in first-turn order, and the turn `r → h` enters `v`,
   which `k₁` visits again, between the two distinct digons.  That is a good first-turn split
   (`p06RoseRedraw_TurnSplit`).
4. `p06RoseRedraw_step_split` splits there and gives `repeatedVisits = 1`.  Doubling `f` inside
   `k` as well, and splitting twice, gives a G-hexagon and `repeatedVisits = 0`.

The Python model and the checks are in the lane scratchpad (`gl-p06-04/turnsplit.py`,
`gl-p06-04/hexa.py`).  The step is found in a *redraw* of `X`, never in `X` itself.  This is why
`p06RoseRedraw_AllStuck`, which only looks at `X`, cannot see it.

## The residual

`p06RoseDecide_RoseStatement` is `p06RoseRedraw_RoseStatement` with one change: the hypothesis
`p06RoseRedraw_AllStuck K` is replaced by `p06RoseDecide_RedrawStuck K`.  That hypothesis says
that every competing pocket of *every O-equivalent copy* of `X` (with letter labels, two distinct
cells, walk order, proper arcs, and `repeatedVisits ≤ K.repeatedVisits`) is stuck.  The reduction
`p06RoseDecide_rose` goes by cases:

* if some competitor of a redraw is not stuck, `p06RoseRedraw_step_notStuck` steps there, and
  `OEquivalentDiscDiagram.trans` composes the two redraws;
* otherwise the residual applies.

## Strength (LOUD)

`p06RoseDecide_of_rose` proves the residual from the target, so the residual is true whenever
the target is.  With the reduction, the two are **provably equivalent**.  This holds for every
residual with a proved `_of_` reduction that the target implies, including
`p06RoseRedraw_RoseStatement` itself relative to `p06RoseUncut_NoMoveStatement`.  So this residual
is strictly smaller in *proof content*, not in logical strength.

The content discharged is the step in every redraw with a steppable competitor.  In particular
it covers the unbalanced three-petal rose, the case the old residual left in doubt: the redraw
in step 1 above falsifies `p06RoseDecide_RedrawStuck K`.  Nothing is re-added, and no binder is
renamed into an equivalent.

## Remaining gap

The residual keeps the uncut roses in which every competitor of every O-equivalent redraw is
stuck.  No such configuration is known.  The rose model suggests the missing general
construction: double the arcs next to the pinch vertex, then split at the first turn between the
new digons.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides OuterPinchIsolated
open scoped Classical

section Decide

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **Stuck in every redraw**: every competing cell pocket of every O-equivalent copy of `X` with
letter labels (two distinct cells, walk order, proper arcs, at most the repeated visits of `K`)
is stuck. -/
def p06RoseDecide_RedrawStuck (K : CellPocketFaceSet D eps X i j) : Prop :=
  ∀ X₂ : DiscDiagram.{u, w, v} W, Nonempty (OEquivalentDiscDiagram X X₂) →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X₂.label d)) →
    ∀ (i₂ j₂ : Fin X₂.rCellCount) (K₂ : CellPocketFaceSet D eps X₂ i₂ j₂), i₂ ≠ j₂ →
      K₂.ClosedWalk → K₂.firstArc.length < (cellDarts X₂ i₂).length →
        K₂.secondArc.length < (cellDarts X₂ j₂).length →
          K₂.repeatedVisits ≤ K.repeatedVisits → p06RoseRedraw_Stuck K₂

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.p06RoseDecide_RedrawStuck

/-- **Stuck in every redraw implies stuck in `X`**: take the redraw `X` itself. -/
theorem p06RoseDecide_allStuck
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (K : CellPocketFaceSet D eps X i j) (h : p06RoseDecide_RedrawStuck K) :
    p06RoseRedraw_AllStuck K :=
  fun i₂ j₂ K₂ hij₂ hK₂ hfirst₂ hsecond₂ hle =>
    h X ⟨OEquivalentDiscDiagram.refl X⟩ hlabel i₂ j₂ K₂ hij₂ hK₂ hfirst₂ hsecond₂ hle

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.p06RoseDecide_allStuck

/-- **The step when some redraw has a competitor that is not stuck**: step there
(`p06RoseRedraw_step_notStuck`) and compose the two O-equivalences. -/
theorem p06RoseDecide_step (K : CellPocketFaceSet D eps X i j)
    (h : ¬ p06RoseDecide_RedrawStuck K) :
    ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
      (K' : CellPocketFaceSet D eps X' i' j'),
      Nonempty (OEquivalentDiscDiagram X X') ∧
        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ i' ≠ j' ∧
        K'.ClosedWalk ∧ K'.firstArc.length < (cellDarts X' i').length ∧
        K'.secondArc.length < (cellDarts X' j').length ∧
        K'.repeatedVisits < K.repeatedVisits := by
  by_contra hno
  refine h fun X₂ hO₂ hl₂ i₂ j₂ K₂ hij₂ hK₂ hfirst₂ hsecond₂ hle => ?_
  by_contra hbad
  obtain ⟨X', i', j', K', ⟨e'⟩, hl, hne, hK', h₁, h₂, hlt⟩ :=
    p06RoseRedraw_step_notStuck hl₂ K₂ hK₂ hij₂ hfirst₂ hsecond₂ hbad
  obtain ⟨e₂⟩ := hO₂
  exact hno ⟨X', i', j', K', ⟨OEquivalentDiscDiagram.trans e₂ e'⟩, hl, hne, hK', h₁, h₂,
    lt_of_lt_of_le hlt hle⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.p06RoseDecide_step

end Decide

/-- **The uncut rose step when every competitor of every redraw is stuck** (OPEN residual).
`p06RoseRedraw_RoseStatement` with `p06RoseRedraw_AllStuck K` replaced by
`p06RoseDecide_RedrawStuck K`. -/
def p06RoseDecide_RoseStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (i j : Fin X.rCellCount),
    i ≠ j → X.LeastArea → (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : CellPocketFaceSet D eps X i j, K.ClosedWalk → ¬ K.FirstTurns →
      K.firstArc.length < (cellDarts X i).length →
      K.secondArc.length < (cellDarts X j).length →
      ¬Unpinched X.toCombMap K.faces → p06RoseDecide_RedrawStuck K →
        ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
          (K' : CellPocketFaceSet D eps X' i' j'),
          Nonempty (OEquivalentDiscDiagram X X') ∧
            (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ i' ≠ j' ∧
            K'.ClosedWalk ∧ K'.firstArc.length < (cellDarts X' i').length ∧
            K'.secondArc.length < (cellDarts X' j').length ∧
            K'.repeatedVisits < K.repeatedVisits

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.p06RoseDecide_RoseStatement

/-- **The old residual from the new one**: by cases on `p06RoseDecide_RedrawStuck K`. -/
theorem p06RoseDecide_rose (h : p06RoseDecide_RoseStatement.{u, w, v}) :
    p06RoseRedraw_RoseStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j hij hlea hlabel K hK hnft hfirst hsecond hpinch _
  by_cases hred : p06RoseDecide_RedrawStuck K
  · exact h D eps X i j hij hlea hlabel K hK hnft hfirst hsecond hpinch hred
  · exact p06RoseDecide_step K hred

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.p06RoseDecide_rose

/-- **The new residual from the old one** (so it is true whenever the old one is): stuck in every
redraw implies stuck in `X` (`p06RoseDecide_allStuck`). -/
theorem p06RoseDecide_of_rose (h : p06RoseRedraw_RoseStatement.{u, w, v}) :
    p06RoseDecide_RoseStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j hij hlea hlabel K hK hnft hfirst hsecond hpinch hred
  exact h D eps X i j hij hlea hlabel K hK hnft hfirst hsecond hpinch
    (p06RoseDecide_allStuck hlabel K hred)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.p06RoseDecide_of_rose

/-- **The target of the rose redraw from the residual**, `p06RoseUncut_NoMoveStatement`. -/
theorem p06RoseDecide_noMove (h : p06RoseDecide_RoseStatement.{u, w, v}) :
    p06RoseUncut_NoMoveStatement.{u, w, v} :=
  p06RoseRedraw_noMove_of_rose (p06RoseDecide_rose h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.p06RoseDecide_noMove

/-- **The uncut rose step from the residual**, `CellRoseUncutStatement`. -/
theorem p06RoseDecide_uncut (h : p06RoseDecide_RoseStatement.{u, w, v}) :
    CellRoseUncutStatement.{u, w, v} :=
  p06RoseRedraw_uncut_of_rose (p06RoseDecide_rose h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.p06RoseDecide_uncut

/-- **The rose step of the cell pinch from the residual**, `CellRoseStepStatement`. -/
theorem p06RoseDecide_cellRoseStep (h : p06RoseDecide_RoseStatement.{u, w, v}) :
    CellRoseStepStatement.{u, w, v} :=
  cellRoseStep_of_uncut (p06RoseDecide_uncut h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.p06RoseDecide_cellRoseStep

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06
