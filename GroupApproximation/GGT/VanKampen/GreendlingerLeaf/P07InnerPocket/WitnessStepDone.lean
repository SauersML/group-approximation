import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepCurveProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepLobeStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepCornerProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepBlockProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepSideProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepWindingProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepGenusProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepDescentProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepPinchParityProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepPinchLobeProof
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-67: the witness-step chain, unconditionally

Lane gl-p07-66 proved `FourPieceWitness.witnessStepCurve_sublist :
witnessStepLobe_SublistStatement` with no hypotheses (`WitnessStepCurveProof.lean:92`).  This
module is only wiring.  It applies the `_of_` reductions already in the repo to that term and
states, with no binders, every witness-step Statement they reach:

* from `witnessStepLobe_*_of_sublist` (`WitnessStepLobeStatement.lean`): the order, cycle,
  reclosed, genus-bridge, skip and corner Statements;
* corner ⟶ block ⟶ side ⟶ `WitnessStepResidualStatement` (`WitnessStepCornerProof`,
  `WitnessStepBlockProof`, `WitnessStepSideProof`);
* bridge ⟶ winding-pinched ⟶ descent ⟶ pinch arc / pinch parity ⟶ pinch lobe ⟶ pinch cut,
  and parity ⟶ pinch-off, pinch (`WitnessStepGenusProof`, `WitnessStepWindingProof`,
  `WitnessStepDescentProof`, `WitnessStepPinchParityProof`, `WitnessStepPinchLobeProof`).

The chain continues to clause (read) in `WitnessStepDoneRead`.  No new mathematics and no
residual Statement.  Declarations live in `P07InnerPocket` rather than `FourPieceWitness`, so
each `#audit_axioms` full name fits in 100 columns.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 4.4 at
least-area diagrams); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

/-- **The reclose order Statement, unconditionally.** -/
theorem witnessStepDone_order : FourPieceWitness.witnessStepReclose_OrderStatement.{u, w, v} :=
  FourPieceWitness.witnessStepLobe_order_of_sublist FourPieceWitness.witnessStepCurve_sublist

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepDone_order

/-- **The order cycle Statement, unconditionally.** -/
theorem witnessStepDone_cycle : FourPieceWitness.witnessStepOrder_CycleStatement.{u, w, v} :=
  FourPieceWitness.witnessStepLobe_cycle_of_sublist FourPieceWitness.witnessStepCurve_sublist

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepDone_cycle

/-- **The bridge reclosed Statement, unconditionally.** -/
theorem witnessStepDone_reclosed :
    FourPieceWitness.witnessStepBridge_ReclosedStatement.{u, w, v} :=
  FourPieceWitness.witnessStepLobe_reclosed_of_sublist FourPieceWitness.witnessStepCurve_sublist

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepDone_reclosed

/-- **The genus bridge Statement, unconditionally.** -/
theorem witnessStepDone_bridge : FourPieceWitness.WitnessStepGenusBridgeStatement.{u, w, v} :=
  FourPieceWitness.witnessStepLobe_bridge_of_sublist FourPieceWitness.witnessStepCurve_sublist

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepDone_bridge

/-- **The skip Statement, unconditionally.** -/
theorem witnessStepDone_skip : FourPieceWitness.WitnessStepSkipStatement.{u, w, v} :=
  FourPieceWitness.witnessStepLobe_skip_of_sublist FourPieceWitness.witnessStepCurve_sublist

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepDone_skip

/-- **The corner residual, unconditionally.** -/
theorem witnessStepDone_corner : FourPieceWitness.WitnessStepCornerResidualStatement.{u, w, v} :=
  FourPieceWitness.witnessStepLobe_corner_of_sublist FourPieceWitness.witnessStepCurve_sublist

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepDone_corner

/-- **The block residual, unconditionally.** -/
theorem witnessStepDone_blockResidual :
    FourPieceWitness.WitnessStepBlockResidualStatement.{u, w, v} :=
  FourPieceWitness.witnessStepBlockResidual_of_witnessStepCorner witnessStepDone_corner

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepDone_blockResidual

/-- **The side residual, unconditionally.** -/
theorem witnessStepDone_sideResidual :
    FourPieceWitness.WitnessStepSideResidualStatement.{u, w, v} :=
  FourPieceWitness.witnessStepSideResidual_of_witnessStepBlock witnessStepDone_blockResidual

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepDone_sideResidual

/-- **Lane gl-p07-40's `WitnessStepResidualStatement`, unconditionally.** -/
theorem witnessStepDone_stepResidual : FourPieceWitness.WitnessStepResidualStatement.{u, w, v} :=
  FourPieceWitness.witnessStepResidual_of_witnessStepSide witnessStepDone_sideResidual

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepDone_stepResidual

/-- **The winding pinched Statement, unconditionally.** -/
theorem witnessStepDone_windingPinched :
    FourPieceWitness.WitnessStepWindingPinchedStatement.{u, w, v} :=
  FourPieceWitness.witnessStepGenus_pinched_of_bridge witnessStepDone_bridge

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepDone_windingPinched

/-- **The descent Statement, unconditionally.** -/
theorem witnessStepDone_descent : FourPieceWitness.WitnessStepDescentStatement.{u, w, v} :=
  FourPieceWitness.witnessStepWinding_descent_of_pinched witnessStepDone_windingPinched

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepDone_descent

/-- **The pinch arc Statement, unconditionally.** -/
theorem witnessStepDone_pinchArc : FourPieceWitness.WitnessStepPinchArcStatement.{u, w, v} :=
  FourPieceWitness.witnessStepDescent_arc_of_descent witnessStepDone_descent

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepDone_pinchArc

/-- **The pinch parity Statement, unconditionally.** -/
theorem witnessStepDone_pinchParity :
    FourPieceWitness.WitnessStepPinchParityStatement.{u, w, v} :=
  FourPieceWitness.witnessStepDescent_parity_of_descent witnessStepDone_descent

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepDone_pinchParity

/-- **The pinch lobe Statement, unconditionally.** -/
theorem witnessStepDone_pinchLobe : FourPieceWitness.WitnessStepPinchLobeStatement.{u, w, v} :=
  FourPieceWitness.witnessStepPinchParity_pinchLobe_of_parity witnessStepDone_pinchParity

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepDone_pinchLobe

/-- **The pinch cut Statement, unconditionally.** -/
theorem witnessStepDone_pinchCut : FourPieceWitness.WitnessStepPinchCutStatement.{u, w, v} :=
  FourPieceWitness.witnessStepPinchLobe_pinchCut_of_pinchLobe witnessStepDone_pinchLobe

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepDone_pinchCut

/-- **The pinch-off Statement, unconditionally.** -/
theorem witnessStepDone_pinchOff : FourPieceWitness.WitnessStepPinchOffStatement.{u, w, v} :=
  FourPieceWitness.witnessStepPinchParity_pinchOff_of_parity witnessStepDone_pinchParity

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepDone_pinchOff

/-- **The pinch Statement, unconditionally.** -/
theorem witnessStepDone_pinch : FourPieceWitness.WitnessStepPinchStatement.{u, w, v} :=
  FourPieceWitness.witnessStepPinchParity_pinch_of_parity witnessStepDone_pinchParity

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepDone_pinch

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
