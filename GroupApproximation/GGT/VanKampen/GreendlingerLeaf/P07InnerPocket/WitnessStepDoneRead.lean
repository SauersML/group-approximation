import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepDone
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessCurveSublistProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourBlockNondegStepProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCaseGlue
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-67: clause (read), unconditionally

This continues `WitnessStepDone`.  It is wiring only:

* descent ⟶ `WitnessCurveSublistStepStatement` (`witnessStepDescent_curveStep_of_descent`);
* ⟶ `WitnessCurveSublistNondegStatement` (`witnessCurveSublistNondeg_of_step`);
* ⟶ the corrected four-block Statements `FourBlockNondegLabel`, `FourBlockNondeg` and
  `NoninterleaveNondeg` (`FourBlockNondegStepProof`).  These are the corrected, nondegenerate
  forms, not the FALSE `WitnessNoninterleave`/`FourBlock` Statements;
* ⟶ clause (read) of the pinch case, `PinchCase.ReadStatement`
  (`PinchCase.read_of_noninterleaveNondeg`, `PinchCaseGlue.lean:56`).

So of the two clauses of `SoundRoute.PinchCaseStatement` only (rest) stays open; see
`WitnessStepDoneOff`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 4.4 at
least-area diagrams); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

/-- **Lane gl-p07-32's curve sublist step Statement, unconditionally.** -/
theorem witnessStepDone_curveStep :
    FourPieceWitness.WitnessCurveSublistStepStatement.{u, w, v} :=
  FourPieceWitness.witnessStepDescent_curveStep_of_descent witnessStepDone_descent

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepDone_curveStep

/-- **The nondegenerate curve sublist Statement, unconditionally.** -/
theorem witnessStepDone_curveNondeg :
    FourPieceWitness.WitnessCurveSublistNondegStatement.{u, w, v} :=
  FourPieceWitness.witnessCurveSublistNondeg_of_step witnessStepDone_curveStep

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepDone_curveNondeg

/-- **The labelled nondegenerate four-block Statement, unconditionally.** -/
theorem witnessStepDone_fourBlockLabel :
    FourPieceWitness.FourBlockNondegLabelStatement.{u, w, v} :=
  FourPieceWitness.fourBlockNondegLabel_of_curveSublist witnessStepDone_curveNondeg

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepDone_fourBlockLabel

/-- **The nondegenerate four-block Statement, unconditionally.** -/
theorem witnessStepDone_fourBlockNondeg : FourPieceWitness.FourBlockNondegStatement.{u, w, v} :=
  FourPieceWitness.fourBlockNondeg_of_curveSublist witnessStepDone_curveNondeg

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepDone_fourBlockNondeg

/-- **The nondegenerate noninterleave Statement, unconditionally.** -/
theorem witnessStepDone_noninterleave :
    FourPieceWitness.NoninterleaveNondegStatement.{u, w, v} :=
  FourPieceWitness.noninterleaveNondeg_of_curveSublist witnessStepDone_curveNondeg

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepDone_noninterleave

/-- **Clause (read) of the pinch case, unconditionally.** -/
theorem witnessStepDone_read : PinchCase.ReadStatement.{u, w, v} :=
  PinchCase.read_of_noninterleaveNondeg witnessStepDone_noninterleave

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepDone_read

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
