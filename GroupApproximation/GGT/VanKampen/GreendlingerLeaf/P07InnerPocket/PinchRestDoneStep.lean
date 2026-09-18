import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.AbsorbFaceSetStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-68: pinch-free walks satisfy the step clauses

`FourPieceWitness.AbsorbFaceSetStepGood G₁ G₂ ow` (`AbsorbFaceSetStatement.lean:85`) packs the
four local step clauses S1a, S1b, S2a, S2b of a walk `ow`.  Each one is a statement about positions
`p` that fail `walkKeep ow (facePerm ow[p]) ∨ PinchFreeAt ow[p]`.  Such a position must have
`ow[p]` pinched.

* **S1a** asks for `walkKeep ∨ PinchFreeAt` at positions with `ow[p] ∈ G₁`.  If every dart
  of `ow` on `G₁` is pinch-free, the right disjunct holds.
* **S1b** (every dart of `ow` on `G₁`) asks that at most one position fails.  If every dart
  of `ow` on `G₁` is pinch-free, no position fails.
* **S2a** and **S2b** are the same argument for `G₂`.

So `pinchRestDone_stepGood` holds.  Its contrapositive is
`pinchRestDone_exists_pinched`: a walk that fails a step clause visits a *pinched* dart of `G₁`
or `G₂`.  Both are proved outright, from definitions only.

## Manuscript status

Infrastructure for `thm:hull` (through Osin's Lemma 4.4); certifies no printed sentence.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **Pinch-free darts on the walk give the step clauses.**  If every dart of `ow` lying on `G₁`
or on `G₂` is `PinchFreeAt`, then S1a, S1b, S2a and S2b hold for `ow`. -/
theorem pinchRestDone_stepGood {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {X : DiscDiagram.{u, w, v} W}
    {i j : Fin X.rCellCount} {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)}
    {ow : List X.toCombMap.Dart}
    (h₁ : ∀ d ∈ ow, d ∈ G₁.darts → PocketRun.PinchFreeAt X.toCombMap d)
    (h₂ : ∀ d ∈ ow, d ∈ G₂.darts → PocketRun.PinchFreeAt X.toCombMap d) :
    FourPieceWitness.AbsorbFaceSetStepGood G₁ G₂ ow := by
  refine ⟨fun _ p hp hm _ => Or.inr (h₁ _ (List.getElem_mem hp) hm), ?_,
    fun _ p hp hm _ => Or.inr (h₂ _ (List.getElem_mem hp) hm), ?_⟩
  · intro hall p _ hp _ hnp _
    exact absurd (Or.inr (h₁ _ (List.getElem_mem hp) (hall _ (List.getElem_mem hp)))) hnp
  · intro hall p _ hp _ hnp _
    exact absurd (Or.inr (h₂ _ (List.getElem_mem hp) (hall _ (List.getElem_mem hp)))) hnp

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchRestDone_stepGood

/-- **A walk failing a step clause visits a pinched dart of `G₁` or `G₂`** (the contrapositive
of `pinchRestDone_stepGood`). -/
theorem pinchRestDone_exists_pinched {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {X : DiscDiagram.{u, w, v} W}
    {i j : Fin X.rCellCount} {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)}
    {ow : List X.toCombMap.Dart} (hS : ¬ FourPieceWitness.AbsorbFaceSetStepGood G₁ G₂ ow) :
    ∃ (p : ℕ) (hp : p < ow.length), (ow[p] ∈ G₁.darts ∨ ow[p] ∈ G₂.darts) ∧
      ¬ PocketRun.PinchFreeAt X.toCombMap ow[p] := by
  refine Classical.byContradiction fun hne => hS (pinchRestDone_stepGood ?_ ?_)
  · intro d hd hG
    obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hd
    exact Classical.byContradiction fun hpf => hne ⟨p, hp, Or.inl hG, hpf⟩
  · intro d hd hG
    obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hd
    exact Classical.byContradiction fun hpf => hne ⟨p, hp, Or.inr hG, hpf⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchRestDone_exists_pinched

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
