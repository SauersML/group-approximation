import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.GoodCorners
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.Doubling
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06: the residual cases of the cell outer-pinch step

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Steps 5 and 6 of the plan in
`Piece06/Predicate`.

* `exists_step_of_badCorners` (proved from `BadCornerRefinementStatement`, gap 5).  At an uncrossed
  non-first turn `d₀ → e₀` whose minimal corners are bad (`¬ GoodTurnCorners X d₀ e₀`), double an
  edge at each corner (`CellPocketFaceSet.faceEdgeDoubling`, `outerSpurThickening`), inserting a
  G-digon into the corner.  Since the turn is not first, `σ e₀ ≠ α d₀`
  (`sigma_ne_alpha_of_not_firstTurn`).  The doubled diagram is a rotation refinement
  (`Piece06/Refinement`) carrying the pocket with boundary `c.map e`, and it has a good refined
  sector.  This existence is the isolated hypothesis `BadCornerRefinementStatement` (`Piece06/Doubling`).
  The transport of the non-first turn, the uncrossedness and the sector across the refinement, and
  the step itself, are `exists_step_of_refinement` (proved).
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

/-- **One step of the cell pinch at an uncrossed non-first turn with bad corners**, from the corner
doubling `BadCornerRefinementStatement` (gap 5 of `Piece06/Predicate`), through
`exists_step_of_refinement`. -/
theorem exists_step_of_badCorners (hgap : BadCornerRefinementStatement.{u, w, v})
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
    (_hbad : ¬ GoodTurnCorners X d₀ e₀) :
    ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
      (K' : CellPocketFaceSet D eps X' i' j'),
      Nonempty (OEquivalentDiscDiagram X X') ∧
        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ i' ≠ j' ∧
        K'.ClosedWalk ∧ K'.firstArc.length < (cellDarts X' i').length ∧
        K'.secondArc.length < (cellDarts X' j').length ∧
        K'.repeatedVisits < K.repeatedVisits := by
  obtain ⟨X', i', j', K', R, hE, hlabel', hij', hK', hfirst', hsecond', hvisits, hcycle, hsector⟩ :=
    hgap K hlabel hK hij hfirst hsecond hd₀ hnext₀ (sigma_ne_alpha_of_not_firstTurn hnot)
  exact exists_step_of_refinement K K' R hE hlabel' hij' hK' hfirst' hsecond' hvisits hcycle hd₀
    hnext₀ hnot huncross hsector

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.exists_step_of_badCorners
