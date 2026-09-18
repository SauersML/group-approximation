import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.Predicate
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellPinchSectionDistinct
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06: the rose case of the cell outer-pinch step

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Step 6 of the plan in `Piece06/Predicate`:
every non-first turn of the boundary cycle of a cell pocket face set is crossed
(`AllNonFirstTurnsCrossed`).

* `CellRoseStepStatement`: the rose step for cell pockets between distinct cells (OPEN, gap 6).
* `exists_step_of_allCrossed_of_cellRoseStep`: the rose step for a fixed pocket, from it.

## The remaining gap

In the local model at a vertex visited `k` times the rotation reads `o_1 ī_1 … o_k ī_k`, a passage
is `ī_a → o_{π a}`, a first turn is `π a = a`, and passage `a` is crossed iff `π` does not preserve
the open cyclic interval `(a, π a)`.  The intended argument is that of `P10Rose` (see the docstring
of `P10Rose/Proof`): absorb the lakes of the complement of `K.faces`, which keeps the arcs and
lowers the repeated visits once the absorbed walk is known to be closed; without lakes, cut a
contiguous block of passages closed under the face relation `FaceClassStep (walkKeep c)`.

Two differences from the outer pocket make this case harder.

* Cell pocket face sets need positive arcs (`firstArc_pos`, `secondArc_pos`), so the lobe of the cut
  sub-walk `B` cannot be taken with empty arcs.  When the lobe of the rest carries no relator cell,
  the step keeps the rest only after a relator cell of the lobe of `B` is exchanged for it, which is
  not a same-diagram operation.
* The chord split (`exists_step_of_uncrossedTurn`) is not available: at a vertex visited three
  times as `i₁ o₁ i₂ o₂ i₃ o₃` with turns `i₁ → o₂`, `i₂ → o₃`, `i₃ → o₁`, no split into two
  σ-intervals keeps all three turns.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides OuterPinchIsolated

/-- **The rose step of the cell pinch** (OPEN, gap 6 of `Piece06/Predicate`).  A cell pocket face
set between distinct cells of a least-area diagram with letter labels, in walk order, not in
first-turn order, with both arcs proper, pinched complement, and every non-first turn crossed, has an
O-equivalent copy with letter labels and a cell pocket face set between distinct cells, in walk order,
with both arcs proper and strictly fewer repeated visits. -/
def CellRoseStepStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (i j : Fin X.rCellCount),
    i ≠ j → X.LeastArea → (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : CellPocketFaceSet D eps X i j, K.ClosedWalk → ¬ K.FirstTurns →
      K.firstArc.length < (cellDarts X i).length →
      K.secondArc.length < (cellDarts X j).length →
      ¬Unpinched X.toCombMap K.faces → AllNonFirstTurnsCrossed K →
        ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
          (K' : CellPocketFaceSet D eps X' i' j'),
          Nonempty (OEquivalentDiscDiagram X X') ∧
            (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ i' ≠ j' ∧
            K'.ClosedWalk ∧ K'.firstArc.length < (cellDarts X' i').length ∧
            K'.secondArc.length < (cellDarts X' j').length ∧
            K'.repeatedVisits < K.repeatedVisits

/-- **One step of the cell pinch in the rose configuration**, from `CellRoseStepStatement`. -/
theorem exists_step_of_allCrossed_of_cellRoseStep (hgap : CellRoseStepStatement.{u, w, v})
    {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) (hlea : X.LeastArea)
    (K : CellPocketFaceSet D eps X i j) (hK : K.ClosedWalk) (hnft : ¬ K.FirstTurns) (hij : i ≠ j)
    (hfirst : K.firstArc.length < (cellDarts X i).length)
    (hsecond : K.secondArc.length < (cellDarts X j).length)
    (hpinch : ¬Unpinched X.toCombMap K.faces) (hrose : AllNonFirstTurnsCrossed K) :
    ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
      (K' : CellPocketFaceSet D eps X' i' j'),
      Nonempty (OEquivalentDiscDiagram X X') ∧
        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ i' ≠ j' ∧
        K'.ClosedWalk ∧ K'.firstArc.length < (cellDarts X' i').length ∧
        K'.secondArc.length < (cellDarts X' j').length ∧
        K'.repeatedVisits < K.repeatedVisits :=
  hgap D eps X i j hij hlea hlabel K hK hnft hfirst hsecond hpinch hrose

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CellRoseStepStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.exists_step_of_allCrossed_of_cellRoseStep
