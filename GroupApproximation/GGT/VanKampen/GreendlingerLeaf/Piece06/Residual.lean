import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.GoodCorners
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06: the residual cases of the cell outer-pinch step

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Steps 5 and 6 of the plan in
`Piece06/Predicate`.

* `exists_step_of_badCorners` (OPEN, gap 5).  At an uncrossed non-first turn `d₀ → e₀` whose minimal
  corners are bad (`¬ GoodTurnCorners X d₀ e₀`), the intended argument doubles an edge of the
  offending corner face outside `K.faces` (`CellPocketFaceSet.faceEdgeDoubling`), which inserts a
  G-digon, off the exterior and off the relator cells, into the corner, and keeps walk order, repeated
  visits and proper arcs.  In the doubled diagram the corners are good and
  `Piece06.exists_step_of_goodCorners` performs the step; O-equivalences compose.  The missing input
  is the transport of `NonFirstTurn`, `¬ TurnCrossed` and the corner data across the doubling, which
  is not in the library.  The attempt below reads off good corners from `hbad` and is expected to fail
  at that point.
* Gap 6, the rose (every non-first turn is crossed), is isolated as `CellRoseStepStatement` in the
  module `Piece06/Rose`, with the reduction `exists_step_of_allCrossed_of_cellRoseStep`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides OuterPinchIsolated
open scoped Classical

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **One step of the cell pinch at an uncrossed non-first turn with bad corners** (OPEN, gap 5 of
`Piece06/Predicate`: the transport of the turn data across `faceEdgeDoubling` is missing).  Best
attempt; expected not to elaborate. -/
theorem exists_step_of_badCorners
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (K : CellPocketFaceSet D eps X i j) (hK : K.ClosedWalk) (hij : i ≠ j)
    (hfirst : K.firstArc.length < (cellDarts X i).length)
    (hsecond : K.secondArc.length < (cellDarts X j).length)
    {d₀ e₀ : X.toCombMap.Dart} (hd₀ : d₀ ∈ K.boundary.cycle)
    (hnext₀ : K.boundary.cycle.next d₀ hd₀ = e₀)
    (hnot : ¬ FirstTurn X.toCombMap (K.boundary.cycle.reverse.map X.toCombMap.alpha)
      (X.toCombMap.alpha e₀) (X.toCombMap.alpha d₀))
    (huncross : ∀ d (hd : d ∈ K.boundary.cycle), d ≠ d₀ →
      X.toCombMap.sigma.SameCycle (X.toCombMap.alpha d₀) (X.toCombMap.alpha d) →
        (RotationBetween X.toCombMap (X.toCombMap.alpha d₀) e₀ (X.toCombMap.alpha d) ↔
          RotationBetween X.toCombMap (X.toCombMap.alpha d₀) e₀ (K.boundary.cycle.next d hd)))
    (hbad : ¬ GoodTurnCorners X d₀ e₀) :
    ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
      (K' : CellPocketFaceSet D eps X' i' j'),
      Nonempty (OEquivalentDiscDiagram X X') ∧
        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ i' ≠ j' ∧
        K'.ClosedWalk ∧ K'.firstArc.length < (cellDarts X' i').length ∧
        K'.secondArc.length < (cellDarts X' j').length ∧
        K'.repeatedVisits < K.repeatedVisits := by
  -- OPEN (gap 5): in the doubled diagram the corners are good.  Expected elaboration failure: `hbad`
  -- is `¬ GoodTurnCorners X d₀ e₀`, not its double negation.
  have hgood : GoodTurnCorners X d₀ e₀ := not_not.mp hbad
  exact exists_step_of_goodCorners hlabel K hK hij hfirst hsecond hd₀ hnext₀ hnot huncross hgood

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.exists_step_of_badCorners
