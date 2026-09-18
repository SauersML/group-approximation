import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepWindingStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepDescentProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepDescentUnique
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepPinchArcClassify
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessCurveSublistProof
import GroupApproximation.GGT.VanKampen.FaceSetBoundaryWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-59: the winding-one residual from its pinched case

Lane gl-p07-59.  Certifies no printed sentence on its own.  NOT COMPILED.

* `witnessStepWinding_descent_of_pinched`: `WitnessStepDescentStatement` from
  `WitnessStepWindingPinchedStatement`.  Split on whether some rotation step `(x, y)` of `l` fails
  `StepNext w l x y`.
  * No step fails.  Then `witnessStepDescent_bound_of_steps` gives the bound.  It needs `w` and `l`
    to have no duplicates: `witnessSublist_curve_nodup` and `Embedded.invDarts_nodup E.nodup`.
  * Some step fails.  Then `witnessStepPinchArc_classify` makes it an off-lobe pinch with no cell,
    side, block or corner turn.  That witnesses the pinch hypothesis of the residual.
* `witnessStepWinding_skip_of_pinched`: the wire to `WitnessStepSkipStatement` through
  `witnessStepDescent_skip_of_descent`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **Lane gl-p07-59: the winding-one residual from its pinched case.**  An unpinched
configuration has every step a forward `StepNext`, which gives the bound. -/
theorem witnessStepWinding_descent_of_pinched
    (h : WitnessStepWindingPinchedStatement.{u, w, v}) :
    WitnessStepDescentStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst
    hsecond G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb hlab
  by_cases hex : ∃ (n : ℕ) (s t : List X.toCombMap.Dart) (x y : X.toCombMap.Dart),
      (invDarts X outerWalk).rotate n = s ++ x :: y :: t ∧
      ¬ WitnessCurveSublistList.StepNext (witnessSublistCurve a b G₁ G₂)
        (invDarts X outerWalk) x y
  · obtain ⟨n, s, t, x, y, hr, hns⟩ := hex
    rcases witnessStepPinchArc_classify hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hG₁ hG₂ hw hCa
        hCb E hnb hlab hr with hstep | ⟨hc, hs, hb, hco, hp⟩
    · exact absurd hstep hns
    · exact h D eps X a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst hsecond G₁
        hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb hlab
        ⟨n, s, t, x, y, hr, hc, hs, hb, hco, hp⟩
  · refine Or.inl (witnessStepDescent_bound_of_steps (witnessSublist_curve_nodup a b G₁ G₂)
      (Embedded.invDarts_nodup E.nodup) fun n s t x y hr => ?_)
    by_contra hns
    exact hex ⟨n, s, t, x, y, hr, hns⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepWinding_descent_of_pinched

/-- **Lane gl-p07-59: the skip residual from the pinched winding-one residual.** -/
theorem witnessStepWinding_skip_of_pinched
    (h : WitnessStepWindingPinchedStatement.{u, w, v}) :
    WitnessStepSkipStatement.{u, w, v} :=
  witnessStepDescent_skip_of_descent (witnessStepWinding_descent_of_pinched h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepWinding_skip_of_pinched

/-- **LOUD: the pinched residual follows from the winding-one residual** (it only adds a
hypothesis).  With `witnessStepWinding_descent_of_pinched` the two are equivalent. -/
theorem witnessStepWinding_pinched_of_descent (h : WitnessStepDescentStatement.{u, w, v}) :
    WitnessStepWindingPinchedStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst
    hsecond G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb hlab _
  exact h D eps X a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst hsecond G₁
    hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb hlab

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepWinding_pinched_of_descent

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
