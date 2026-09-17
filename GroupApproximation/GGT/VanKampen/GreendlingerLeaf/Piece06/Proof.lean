import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.Residual
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.Rose
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellPinchSectionDistinct
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf, piece 06: one step of the cell pinch at an outer pinch, for distinct cells

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  `CellPocketOuterPinchStepSectionDistinctStatement`
(`Estimating/OsinPocketCellPinchSectionDistinct`) feeds
`cellPocketPinchSectionDistinctStatement_of_outerPinchStep`.

## Route

The thresholds play no role: `eps0 = 0`, `rho0 = 1`.  For a cell pocket `K` in walk order, not in
first-turn order, with both arcs proper:

* every non-first turn is crossed (the rose): `Piece06.exists_step_of_allCrossed_of_cellRoseStep`,
  from the hypothesis `CellRoseStepStatement` (OPEN, gap 6, module `Piece06/Rose`);
* otherwise some non-first turn `d₀ → next d₀` is uncrossed
  (`Piece06.exists_uncrossed_of_not_allCrossed`), and
  * with good corners the chord split performs the step (`Piece06.exists_step_of_goodCorners`);
  * with bad corners: `Piece06.exists_step_of_badCorners` (OPEN, gap 5).

* `exists_step`: the step for a fixed pocket, from `CellRoseStepStatement`.
* `proof_of_cellRoseStep`: the statement, from `CellRoseStepStatement`.  The unconditional `proof`
  is `proof_of_cellRoseStep` applied to a proof of `CellRoseStepStatement`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides OuterPinchIsolated
open scoped Classical

/-- **One step of the cell pinch at an outer pinch, for a fixed pocket between distinct cells.** -/
theorem exists_step (hgap : CellRoseStepStatement.{u, w, v}) {G : Type u} [Group G]
    {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}
    (hij : i ≠ j) (hlea : X.LeastArea)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (K : CellPocketFaceSet D eps X i j) (hK : K.ClosedWalk) (hnft : ¬ K.FirstTurns)
    (hfirst : K.firstArc.length < (cellDarts X i).length)
    (hsecond : K.secondArc.length < (cellDarts X j).length)
    (hpinch : ¬Unpinched X.toCombMap K.faces) :
    ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
      (K' : CellPocketFaceSet D eps X' i' j'),
      Nonempty (OEquivalentDiscDiagram X X') ∧
        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ i' ≠ j' ∧
        K'.ClosedWalk ∧ K'.firstArc.length < (cellDarts X' i').length ∧
        K'.secondArc.length < (cellDarts X' j').length ∧
        K'.repeatedVisits < K.repeatedVisits := by
  by_cases hrose : AllNonFirstTurnsCrossed K
  · exact exists_step_of_allCrossed_of_cellRoseStep hgap hlabel hlea K hK hnft hij hfirst hsecond
      hpinch hrose
  · obtain ⟨d₀, hd₀, hnf, hnc⟩ := exists_uncrossed_of_not_allCrossed hrose
    by_cases hgood : GoodTurnCorners X d₀ (K.boundary.cycle.next d₀ hd₀)
    · exact exists_step_of_goodCorners hlabel K hK hij hfirst hsecond hd₀ rfl hnf
        (huncross_of_not_turnCrossed hnc) hgood
    · exact exists_step_of_badCorners hlabel K hK hij hfirst hsecond hd₀ rfl hnf
        (huncross_of_not_turnCrossed hnc) hgood

/-- **Piece 06 of the Greendlinger leaf: `CellPocketOuterPinchStepSectionDistinctStatement`**, from
the rose step `CellRoseStepStatement` (OPEN, gap 6). -/
theorem proof_of_cellRoseStep (hgap : CellRoseStepStatement.{u, w, v}) :
    CellPocketOuterPinchStepSectionDistinctStatement.{u, w, v} := by
  intro G _ Lambda D _ _ _ _ _ _ _ _ _
  exact ⟨0, fun _ _ => ⟨1, Nat.one_pos, fun _ _ _ _ _ _ _ hij hlea hlabel K hK hnft hfirst hsecond
    hpinch => exists_step hgap hij hlea hlabel K hK hnft hfirst hsecond hpinch⟩⟩

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.exists_step
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.proof_of_cellRoseStep
