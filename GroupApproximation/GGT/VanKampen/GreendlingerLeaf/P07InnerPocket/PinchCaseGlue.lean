import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCaseReadStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCaseRestStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-34: glue for the two clauses of `PinchCaseStatement`

* `PinchCase.read_of_pinchCase`, `PinchCase.rest_of_pinchCase`: the two projections.
* `PinchCase.pinchCase_of_read_rest`: the pairing.
* `PinchCase.read_of_noninterleaveNondeg`: clause (read) from the corrected noninterleave
  statement of lane gl-p07-29, by dropping the pinch-free hypotheses.
* `PinchCase.rest_of_arcAuditResidual`: clause (rest) from the arc-audit residual, by dropping
  `¬ case (i)`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **Clause (read) from `PinchCaseStatement`.** -/
theorem read_of_pinchCase (h : SoundRoute.PinchCaseStatement.{u, w, v}) :
    ReadStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb
  exact (h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner
    houter C hC hCf hCa hCb).1

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase.read_of_pinchCase

/-- **Clause (rest) from `PinchCaseStatement`.** -/
theorem rest_of_pinchCase (h : SoundRoute.PinchCaseStatement.{u, w, v}) :
    RestStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb
  exact (h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner
    houter C hC hCf hCa hCb).2

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase.rest_of_pinchCase

/-- **`PinchCaseStatement` from its two clauses.** -/
theorem pinchCase_of_read_rest (hread : ReadStatement.{u, w, v}) (hrest : RestStatement.{u, w, v}) :
    SoundRoute.PinchCaseStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb
  exact ⟨hread D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout
      hinner houter C hC hCf hCa hCb,
    hrest D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner
      houter C hC hCf hCa hCb⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase.pinchCase_of_read_rest

/-- **Clause (read) from the corrected noninterleave statement** (lane gl-p07-29): drop the
pinch-free hypotheses. -/
theorem read_of_noninterleaveNondeg
    (hnon : FourPieceWitness.NoninterleaveNondegStatement.{u, w, v}) : ReadStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb hai₁ haj₁ hbi₁ hbj₁ outerWalk E hnb _ _
  exact hnon D eps X a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst hsecond G₁ hG₁ G₂
    hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase.read_of_noninterleaveNondeg

/-- **Clause (rest) from the arc-audit residual**: drop `¬ case (i)`. -/
theorem rest_of_arcAuditResidual (hres : PocketFourPieceArcAuditResidualStatement.{u, w, v}) :
    RestStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb _
  exact hres D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner
    houter C hC hCf hCa hCb

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase.rest_of_arcAuditResidual

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase
