import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourBlockWitnessAudit
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitnessNoninterleaveList
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-27: the corrected four-block statements

Lane gl-p07-27.  The context is Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).
`FourPieceWitness.FourBlockStatement` and `PocketFourPieceWitnessNoninterleaveStatement` are
FALSE (model M9, `FourBlockWitnessAudit.lean`).  This file relates them to their corrections,
which assume that the four contact arcs are nonempty.

* `fourBlockNondeg_of_fourBlock`: the original four-block statement implies the corrected one.
* `noninterleaveNondeg_of_noninterleave`: the same for the noninterleave statement.
* `noninterleaveNondeg_of_fourBlockNondeg`: the corrected four-block statement implies the
  corrected noninterleave statement.  The proof is the one of `noninterleave_of_fourBlock`
  (`FourPieceWitnessNoninterleaveEndpoint.lean`), with the four extra hypotheses passed along.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **The original four-block statement implies the corrected one**: ignore the four
nondegeneracy hypotheses. -/
theorem fourBlockNondeg_of_fourBlock (h : FourBlockStatement.{u, w, v}) :
    FourBlockNondegStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab _ _ _ _ hlabel hW hfirst hsecond G₁ hG₁
    G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb
  exact h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner
    houter C hC hCf hCa hCb outerWalk E hnb

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.fourBlockNondeg_of_fourBlock

/-- **The original noninterleave statement implies the corrected one**: ignore the four
nondegeneracy hypotheses. -/
theorem noninterleaveNondeg_of_noninterleave
    (h : PocketFourPieceWitnessNoninterleaveStatement.{u, w, v}) :
    NoninterleaveNondegStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab _ _ _ _ hlabel hW hfirst hsecond G₁ hG₁
    G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb
  exact h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner
    houter C hC hCf hCa hCb outerWalk E hnb

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.noninterleaveNondeg_of_noninterleave

/-- **The corrected noninterleave statement from the corrected four-block statement.** -/
theorem noninterleaveNondeg_of_fourBlockNondeg (h : FourBlockNondegStatement.{u, w, v}) :
    NoninterleaveNondegStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst
    hsecond G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb
  obtain ⟨n, U₁, U₂, U₃, U₄, hrot, hU₁, hU₃, hU₂, hU₄, hor⟩ := h D eps X a b K hij hai hbi hab
    hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa
    hCb outerWalk E hnb
  exact fourNoninterleave_of_blocks (P1 := fun e => e ∈ invDarts X G₁.darts)
    (P2 := fun e => e ∈ invDarts X G₂.darts)
    (Pb := fun e => X.toCombMap.alpha e ∈ b.sideFrom i) hrot hU₁ hU₃ hU₂ hU₄ hor

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.noninterleaveNondeg_of_fourBlockNondeg

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
