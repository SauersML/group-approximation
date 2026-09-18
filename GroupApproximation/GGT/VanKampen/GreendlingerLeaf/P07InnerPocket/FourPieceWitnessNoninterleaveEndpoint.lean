import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitnessNoninterleaveList
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitnessNoninterleaveStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-24: clause 3 for the witness from the four-block reading

Lane gl-p07-24.  The context is Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).

## Statement

`FourPieceWitness.noninterleave_of_fourBlock`: `FourPieceWitness.FourBlockStatement` implies
`PocketFourPieceWitnessNoninterleaveStatement` (clause 3, `FourPieceWitnessRead.lean`).

## Proof

Obtain the four-block reading.  Apply `FourPieceWitness.fourNoninterleave_of_blocks`
(`FourPieceWitnessNoninterleaveList.lean`) with:
* `P1 e := e ∈ invDarts X G₁.darts`;
* `P2 e := e ∈ invDarts X G₂.darts`;
* `Pb e := α e ∈ b.sideFrom i`.

The four classes of the target are these predicates up to beta-reduction.  The truth check and
the models are in `FourPieceWitnessNoninterleaveStatement.lean`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **Clause 3 for the witness from the four-block reading.**  See the module docstring. -/
theorem noninterleave_of_fourBlock (h : FourBlockStatement.{u, w, v}) :
    PocketFourPieceWitnessNoninterleaveStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb
  obtain ⟨n, U₁, U₂, U₃, U₄, hrot, hU₁, hU₃, hU₂, hU₄, hor⟩ := h D eps X a b K hij hai hbi hab
    hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb
  exact fourNoninterleave_of_blocks (P1 := fun e => e ∈ invDarts X G₁.darts)
    (P2 := fun e => e ∈ invDarts X G₂.darts)
    (Pb := fun e => X.toCombMap.alpha e ∈ b.sideFrom i) hrot hU₁ hU₃ hU₂ hU₄ hor

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.noninterleave_of_fourBlock

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
