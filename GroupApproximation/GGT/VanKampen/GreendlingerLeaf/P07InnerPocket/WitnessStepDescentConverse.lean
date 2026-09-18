import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepDescentProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepDescentUnique
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessCurveSublistProof
import GroupApproximation.GGT.VanKampen.FaceSetBoundaryWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-58: winding one is equivalent to the step residual

Lane gl-p07-58.  Certifies no printed sentence on its own.  NOT COMPILED.

* `witnessStepDescent_descent_of_curveStep`: `WitnessStepDescentStatement` from
  `WitnessCurveSublistStepStatement`.  When every rotation step of `l` is a `StepNext` step of
  `w`, every descent ends at the `w`-first entry of `l`.  So there is at most one descent, and
  the gap sum is at most `|w|` (`witnessStepDescent_bound_of_steps`).
* `witnessStepDescent_iff_curveStep`: the two statements are equivalent.  LOUD: so the residual
  `WitnessStepDescentStatement` is **equivalent** to the step residual, not strictly weaker.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **Lane gl-p07-58: the winding-one residual from the local step residual.** -/
theorem witnessStepDescent_descent_of_curveStep
    (h : WitnessCurveSublistStepStatement.{u, w, v}) :
    WitnessStepDescentStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst
    hsecond G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb hlab
  rcases h D eps X a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst hsecond G₁
      hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb
      hlab with hfwd | hbwd
  · exact Or.inl (witnessStepDescent_bound_of_steps (witnessSublist_curve_nodup a b G₁ G₂)
      (Embedded.invDarts_nodup E.nodup) hfwd)
  · exact Or.inr hbwd

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_descent_of_curveStep

/-- **Lane gl-p07-58: the winding-one residual is equivalent to the local step residual.** -/
theorem witnessStepDescent_iff_curveStep :
    WitnessStepDescentStatement.{u, w, v} ↔ WitnessCurveSublistStepStatement.{u, w, v} :=
  ⟨witnessStepDescent_curveStep_of_descent, witnessStepDescent_descent_of_curveStep⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_iff_curveStep

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
