import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepCornerStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepCornerStep
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-50: the block residual from the residual off corner turns

Lane gl-p07-50.  This file proves `FourPieceWitness.WitnessStepBlockResidualStatement`
(`WitnessStepBlockStatement.lean`) from `FourPieceWitness.WitnessStepCornerResidualStatement`
(`WitnessStepCornerStatement.lean`).  Certifies no printed sentence on its own.

Route: the backward disjunct passes through unchanged.  In the forward disjunct, take a
consecutive pair `(x, y)` of a rotation of `l` with no cell, side or block-order turn.  If there
is no corner turn at `y` either, the new residual gives the step.  If there is, use
`witnessStepCorner_step_of_cornerTurn`.  Its face hypotheses come from the premises:
* the faces of `Π_i` and `Π_j` are off `a` and `b`, by `witnessStepCorner_cell_face_not_mem`
  with the joins (`JoinsCells.source_or_target_left/right`) and the positive arc lengths;
* the witness faces are off `a` and `b`, by `not_mem_left_of_mem_witnessFaces` and
  `not_mem_right_of_mem_witnessFaces` (from `C.face ∉ a.1` and `C.face ∉ b.1`).

LOUD: the new residual is logically equivalent to the old one, given this reduction.  It is
strictly smaller only in proof content.  See `WitnessStepCornerStatement.lean`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **Lane gl-p07-50: the block residual from the residual off corner turns.** -/
theorem witnessStepBlockResidual_of_witnessStepCorner
    (h : WitnessStepCornerResidualStatement.{u, w, v}) :
    WitnessStepBlockResidualStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst
    hsecond G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb hlab
  rcases h D eps X a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst hsecond G₁
      hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb
      hlab with hfwd | hbwd
  · refine Or.inl fun n s t x y hr hcell hside hblock => ?_
    by_cases hcorner : WitnessStepCornerTurn a b G₁ G₂ outerWalk y
    · have hFa : ∀ f ∈ witnessFaces a b K C.face, f ∉ a.1 :=
        fun f hf => not_mem_left_of_mem_witnessFaces hCa hf
      have hFb : ∀ f ∈ witnessFaces a b K C.face, f ∉ b.1 :=
        fun f hf => not_mem_right_of_mem_witnessFaces hCb hf
      have hcai : (cell X i).face ∉ a.1 := witnessStepCorner_cell_face_not_mem a
        (RegionCandidate.JoinsCells.source_or_target_left hai) hai₁
      have hcaj : (cell X j).face ∉ a.1 := witnessStepCorner_cell_face_not_mem a
        (RegionCandidate.JoinsCells.source_or_target_right hai) haj₁
      have hcbi : (cell X i).face ∉ b.1 := witnessStepCorner_cell_face_not_mem b
        (RegionCandidate.JoinsCells.source_or_target_left hbi) hbi₁
      have hcbj : (cell X j).face ∉ b.1 := witnessStepCorner_cell_face_not_mem b
        (RegionCandidate.JoinsCells.source_or_target_right hbi) hbj₁
      exact witnessStepCorner_step_of_cornerTurn E hnb hlab hFa hFb hij hab hcai hcaj hcbi hcbj
        hr hcorner
    · exact hfwd n s t x y hr hcell hside hblock hcorner
  · exact Or.inr hbwd

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepBlockResidual_of_witnessStepCorner

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
