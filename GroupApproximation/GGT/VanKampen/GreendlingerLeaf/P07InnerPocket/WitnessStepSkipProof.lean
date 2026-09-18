import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepSkipStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepSkipVertex
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-51: the corner residual from the skip residual

Lane gl-p07-51.  Certifies no printed sentence on its own.  NOT COMPILED.

`witnessStepCorner_of_witnessStepSkip` proves `WitnessStepCornerResidualStatement` from
`WitnessStepSkipStatement`.  Run the skip residual on the same data.  A forward pair with no turn
is a skip (`witnessStepSkip_skipAt`), so the skip residual gives its step.  The backward disjunct
passes through unchanged.  See `WitnessStepSkipStatement.lean` for the route, the truth check and
the LOUD notes: the two residuals are logically equivalent, and the skip one is smaller only in
proof content.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **Lane gl-p07-51: the corner residual from the residual at skips.** -/
theorem witnessStepCorner_of_witnessStepSkip (h : WitnessStepSkipStatement.{u, w, v}) :
    WitnessStepCornerResidualStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst
    hsecond G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb hlab
  rcases h D eps X a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst hsecond G₁
      hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb
      hlab with hfwd | hbwd
  · exact Or.inl fun n s t x y hr hcell hside hblock hcorner =>
      hfwd n s t x y hr hcell hside hblock hcorner (witnessStepSkip_skipAt E hr hcell hcorner)
  · exact Or.inr hbwd

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCorner_of_witnessStepSkip

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
