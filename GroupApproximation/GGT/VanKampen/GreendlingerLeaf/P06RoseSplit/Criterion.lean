import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06RoseDecide.Redraw
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06, rose split: refuting "stuck in every redraw" through one competitor

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2` between two regions joining two cells.

`p06RoseDecide_RedrawStuck K` quantifies over every O-equivalent redraw `X₂` of `X` and every
competing cell pocket `K₂` of `X₂` with at most the repeated visits of `K`.  This file proves the
elementary facts about it that any redraw argument uses:

* `p06RoseSplit_ofOEquiv`: the property passes to every pocket `K₂` of every redraw
  with `K₂.repeatedVisits ≤ K.repeatedVisits` (compose the O-equivalences);
* `p06RoseSplit_ofRedraw`: the contrapositive;
* `p06RoseSplit_ofNotStuck`: one competitor that is not stuck refutes it;
* `p06RoseSplit_ofTurnSplit`, `_ofNotCrossed`, `_ofCellCut`, `_ofMove`: the four ways to be
  not stuck;
* `p06RoseSplit_stepSplit`: the step conclusion from a turn-split competitor, through
  `p06RoseDecide_step`.

## Truth check of the proposed general construction (LOUD)

The target `¬ p06RoseDecide_RedrawStuck K` for every uncut rose pocket is **not proved** here.
The proposed uniform construction (double the arc darts of `i` and `j` next to the pinch vertex
`v`, take `K₂` on the two new digons, split at the first turn between them) was checked on
explicit combinatorial models (Python, lane scratchpad `gl-p06-05/`: `eps1.py`, `gen.py`,
`search2.py`, `crossed.py`).  It is **not uniform**:

* Lane-04 model (`eps = 3`, both arcs touch `v`): the two-sided doubling works.
* `eps = 1` model (`P_1` a digon `x₁ t̄₁`, `k` a one-letter relator loop, `P_2` a G-digon on
  `t̄₂` of length 2): the two-sided construction **fails**, the side `r h` of `K₂` has length
  `2 > eps`.  A one-sided redraw works instead (double only the last dart of cell `i`; `K₂` has
  sides `1, 1`, repeated visits `2`, and a turn split).
* Model 2 (`eps = 3`, the arc `t₁` does not touch `v`): the arc darts next to `v` do not exist on
  one side; a doubling *inside* the G-petal `P_2` (first dart of `t̄₂`) gives a turn split.
* **Model 3 (open)**: `eps = 4`, `P_1 = A₁ t̄₁ B₁` with lengths `1, 2, 1`, `P_2 = A₂ t̄₂ B₂` with
  lengths `1, 2, 3`, `k` a one-dart relator loop, exterior order `1, k, 2`.  **Neither arc
  touches the pinch vertex**, so the construction does not apply at all.  `K` is not in
  first-turn order, has repeated visits `2`, every non-first turn is crossed, and `X` has no
  competitor with fewer repeated visits and none with a turn split.  An exhaustive search of
  redraws by one or two doublings (any face, the exterior included) and splits of G-faces
  (1017 diagrams at depth 2) found **no** competitor with a turn split or fewer repeated visits.
  This is not a counterexample to `p06RoseDecide_RoseStatement` (deeper redraws and other
  surgeries are untested), but it is the configuration where the general construction fails.

So no uniform proof of `¬ p06RoseDecide_RedrawStuck K` along the proposed route exists; only the
helper lemmas below and in `P06RoseSplit/Double` are proved.  No residual statement is added.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides OuterPinchIsolated
open scoped Classical

section Criterion

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **Stuck in every redraw passes to a redraw**: to every pocket of an O-equivalent copy with at
most the repeated visits, by composing the O-equivalences. -/
theorem p06RoseSplit_ofOEquiv {K : CellPocketFaceSet D eps X i j}
    (h : p06RoseDecide_RedrawStuck K) {X₂ : DiscDiagram.{u, w, v} W}
    (hO : Nonempty (OEquivalentDiscDiagram X X₂)) {i₂ j₂ : Fin X₂.rCellCount}
    (K₂ : CellPocketFaceSet D eps X₂ i₂ j₂) (hle : K₂.repeatedVisits ≤ K.repeatedVisits) :
    p06RoseDecide_RedrawStuck K₂ :=
  fun X₃ hO₃ hl₃ i₃ j₃ K₃ hij₃ hK₃ hfirst₃ hsecond₃ hle₃ => by
    obtain ⟨e⟩ := hO
    obtain ⟨e₃⟩ := hO₃
    exact h X₃ ⟨OEquivalentDiscDiagram.trans e e₃⟩ hl₃ i₃ j₃ K₃ hij₃ hK₃ hfirst₃ hsecond₃
      (le_trans hle₃ hle)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.p06RoseSplit_ofOEquiv

/-- **Not stuck in some redraw refutes stuck in every redraw.** -/
theorem p06RoseSplit_ofRedraw {K : CellPocketFaceSet D eps X i j}
    {X₂ : DiscDiagram.{u, w, v} W} (hO : Nonempty (OEquivalentDiscDiagram X X₂))
    {i₂ j₂ : Fin X₂.rCellCount} (K₂ : CellPocketFaceSet D eps X₂ i₂ j₂)
    (hle : K₂.repeatedVisits ≤ K.repeatedVisits) (h₂ : ¬ p06RoseDecide_RedrawStuck K₂) :
    ¬ p06RoseDecide_RedrawStuck K :=
  fun h => h₂ (p06RoseSplit_ofOEquiv h hO K₂ hle)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.p06RoseSplit_ofRedraw

/-- **One competitor of one redraw that is not stuck refutes stuck in every redraw.** -/
theorem p06RoseSplit_ofNotStuck (K : CellPocketFaceSet D eps X i j)
    {X₂ : DiscDiagram.{u, w, v} W} (hO : Nonempty (OEquivalentDiscDiagram X X₂))
    (hl : ∀ d, (symmetricLabelAlphabet D).IsLetter (X₂.label d))
    {i₂ j₂ : Fin X₂.rCellCount} (K₂ : CellPocketFaceSet D eps X₂ i₂ j₂) (hij : i₂ ≠ j₂)
    (hK : K₂.ClosedWalk) (hfirst : K₂.firstArc.length < (cellDarts X₂ i₂).length)
    (hsecond : K₂.secondArc.length < (cellDarts X₂ j₂).length)
    (hle : K₂.repeatedVisits ≤ K.repeatedVisits) (hns : ¬ p06RoseRedraw_Stuck K₂) :
    ¬ p06RoseDecide_RedrawStuck K :=
  fun h => hns (h X₂ hO hl i₂ j₂ K₂ hij hK hfirst hsecond hle)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.p06RoseSplit_ofNotStuck

/-- **A competitor with a good first-turn split refutes stuck in every redraw.** -/
theorem p06RoseSplit_ofTurnSplit (K : CellPocketFaceSet D eps X i j)
    {X₂ : DiscDiagram.{u, w, v} W} (hO : Nonempty (OEquivalentDiscDiagram X X₂))
    (hl : ∀ d, (symmetricLabelAlphabet D).IsLetter (X₂.label d))
    {i₂ j₂ : Fin X₂.rCellCount} (K₂ : CellPocketFaceSet D eps X₂ i₂ j₂) (hij : i₂ ≠ j₂)
    (hK : K₂.ClosedWalk) (hfirst : K₂.firstArc.length < (cellDarts X₂ i₂).length)
    (hsecond : K₂.secondArc.length < (cellDarts X₂ j₂).length)
    (hle : K₂.repeatedVisits ≤ K.repeatedVisits) (hsplit : p06RoseRedraw_TurnSplit K₂) :
    ¬ p06RoseDecide_RedrawStuck K :=
  p06RoseSplit_ofNotStuck K hO hl K₂ hij hK hfirst hsecond hle fun hs => by
    obtain ⟨-, -, -, hns⟩ := hs
    exact hns hsplit

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.p06RoseSplit_ofTurnSplit

/-- **A competitor with an uncrossed non-first turn refutes stuck in every redraw.** -/
theorem p06RoseSplit_ofNotCrossed (K : CellPocketFaceSet D eps X i j)
    {X₂ : DiscDiagram.{u, w, v} W} (hO : Nonempty (OEquivalentDiscDiagram X X₂))
    (hl : ∀ d, (symmetricLabelAlphabet D).IsLetter (X₂.label d))
    {i₂ j₂ : Fin X₂.rCellCount} (K₂ : CellPocketFaceSet D eps X₂ i₂ j₂) (hij : i₂ ≠ j₂)
    (hK : K₂.ClosedWalk) (hfirst : K₂.firstArc.length < (cellDarts X₂ i₂).length)
    (hsecond : K₂.secondArc.length < (cellDarts X₂ j₂).length)
    (hle : K₂.repeatedVisits ≤ K.repeatedVisits) (hnc : ¬ AllNonFirstTurnsCrossed K₂) :
    ¬ p06RoseDecide_RedrawStuck K :=
  p06RoseSplit_ofNotStuck K hO hl K₂ hij hK hfirst hsecond hle fun hs => by
    obtain ⟨hcr, -, -, -⟩ := hs
    exact hnc hcr

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.p06RoseSplit_ofNotCrossed

/-- **A competitor with a closed cut refutes stuck in every redraw.** -/
theorem p06RoseSplit_ofCellCut (K : CellPocketFaceSet D eps X i j)
    {X₂ : DiscDiagram.{u, w, v} W} (hO : Nonempty (OEquivalentDiscDiagram X X₂))
    (hl : ∀ d, (symmetricLabelAlphabet D).IsLetter (X₂.label d))
    {i₂ j₂ : Fin X₂.rCellCount} (K₂ : CellPocketFaceSet D eps X₂ i₂ j₂) (hij : i₂ ≠ j₂)
    (hK : K₂.ClosedWalk) (hfirst : K₂.firstArc.length < (cellDarts X₂ i₂).length)
    (hsecond : K₂.secondArc.length < (cellDarts X₂ j₂).length)
    (hle : K₂.repeatedVisits ≤ K.repeatedVisits) (hcut : CellCut K₂) :
    ¬ p06RoseDecide_RedrawStuck K :=
  p06RoseSplit_ofNotStuck K hO hl K₂ hij hK hfirst hsecond hle fun hs => by
    obtain ⟨-, hnc, -, -⟩ := hs
    exact hnc hcut

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.p06RoseSplit_ofCellCut

/-- **A competitor with an uncut-rose move refutes stuck in every redraw.** -/
theorem p06RoseSplit_ofMove (K : CellPocketFaceSet D eps X i j)
    {X₂ : DiscDiagram.{u, w, v} W} (hO : Nonempty (OEquivalentDiscDiagram X X₂))
    (hl : ∀ d, (symmetricLabelAlphabet D).IsLetter (X₂.label d))
    {i₂ j₂ : Fin X₂.rCellCount} (K₂ : CellPocketFaceSet D eps X₂ i₂ j₂) (hij : i₂ ≠ j₂)
    (hK : K₂.ClosedWalk) (hfirst : K₂.firstArc.length < (cellDarts X₂ i₂).length)
    (hsecond : K₂.secondArc.length < (cellDarts X₂ j₂).length)
    (hle : K₂.repeatedVisits ≤ K.repeatedVisits) (hmove : p06RoseUncut_Move K₂) :
    ¬ p06RoseDecide_RedrawStuck K :=
  p06RoseSplit_ofNotStuck K hO hl K₂ hij hK hfirst hsecond hle fun hs => by
    obtain ⟨-, -, hnm, -⟩ := hs
    exact hnm hmove

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.p06RoseSplit_ofMove

/-- **The step from a turn-split competitor of a redraw** (`p06RoseDecide_step`). -/
theorem p06RoseSplit_stepSplit (K : CellPocketFaceSet D eps X i j)
    {X₂ : DiscDiagram.{u, w, v} W} (hO : Nonempty (OEquivalentDiscDiagram X X₂))
    (hl : ∀ d, (symmetricLabelAlphabet D).IsLetter (X₂.label d))
    {i₂ j₂ : Fin X₂.rCellCount} (K₂ : CellPocketFaceSet D eps X₂ i₂ j₂) (hij : i₂ ≠ j₂)
    (hK : K₂.ClosedWalk) (hfirst : K₂.firstArc.length < (cellDarts X₂ i₂).length)
    (hsecond : K₂.secondArc.length < (cellDarts X₂ j₂).length)
    (hle : K₂.repeatedVisits ≤ K.repeatedVisits) (hsplit : p06RoseRedraw_TurnSplit K₂) :
    ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
      (K' : CellPocketFaceSet D eps X' i' j'),
      Nonempty (OEquivalentDiscDiagram X X') ∧
        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ i' ≠ j' ∧
        K'.ClosedWalk ∧ K'.firstArc.length < (cellDarts X' i').length ∧
        K'.secondArc.length < (cellDarts X' j').length ∧
        K'.repeatedVisits < K.repeatedVisits :=
  p06RoseDecide_step K (p06RoseSplit_ofTurnSplit K hO hl K₂ hij hK hfirst hsecond hle hsplit)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.p06RoseSplit_stepSplit

end Criterion

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06
