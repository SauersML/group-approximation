import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitnessPlanarCorrected
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCaseProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessCurveSublistProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.AbsorbFaceSetProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WalkDegenStepProof
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-43: the corrected planar part on the sound route

`PocketFourPieceWitnessPlanarStatement` is FALSE (M8, M7; lane gl-p07-23, re-checked in
`WitnessPlanarCloseConnected.lean`).  Its consumers
* `inputProofResidual_of_witness_noninterleave_arcs` (target FALSE by M2),
* `FourPieceWitness.arcAuditResidual_of_planar_noninterleave_arcsAudit` (two more FALSE inputs),
* `FourPieceWitness.noPlanarDegenerate_of_planar` (records weakness only)
are all superseded.  The only true replacement is the corrected planar part
`PocketFourPieceWitnessPlanarCorrectedStatement` (`FourPieceWitnessPlanarAudit.lean`), which had a
supplier only from the arc-audit residual.  This module reroutes it to the live gaps of the sound
route, so that no FALSE statement is needed for it.

## Route

`pocketFourPieceWitnessPlanarCorrected_of_arcAuditResidual` (lane 23) after
`SoundRoute.arcAuditResidual_of_pinchCase` (lane 31) gives the corrected part from
`SoundRoute.PinchCaseStatement`.  That statement is assembled exactly as in
`PinchCase.pocketFourPieceOff_of_curveSublist_noPlanarDegenStep_walkDegen` (lane 34):
* (read) from `FourPieceWitness.WitnessCurveSublistNondegStatement` (lane 32), through
  `noninterleaveNondeg_of_curveSublist` and `PinchCase.read_of_noninterleaveNondeg`;
* (rest) from `FourPieceWitness.NoPlanarDegenStepStatement` (lane 33) and
  `PinchCase.WalkDegenStatement` (lane 34), through `noPlanarDegenerate_of_step`,
  `residual_of_noPlanarDegenerate_walkDegen` and `rest_of_residual`.

The deepest form takes the step statements of lanes 36c, 38 and 37c:
`FourPieceWitness.WitnessCurveSublistStepStatement`, `FourPieceWitness.AbsorbFaceSetStatement`
and `PinchCase.WalkDegenStepStatement`.  These are owned by the sibling lanes gl-p07-40
(WitnessCurveStep), gl-p07-41 (AbsorbLobe) and gl-p07-39b (WalkDegenCase).  No residual is left
that belongs to this lane.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

/-- **The corrected planar part from the sound-route residual of lane gl-p07-31.** -/
theorem witnessPlanarCloseCorrected_of_pinchCase (h : SoundRoute.PinchCaseStatement.{u, w, v}) :
    PocketFourPieceWitnessPlanarCorrectedStatement.{u, w, v} :=
  pocketFourPieceWitnessPlanarCorrected_of_arcAuditResidual
    (SoundRoute.arcAuditResidual_of_pinchCase h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessPlanarCloseCorrected_of_pinchCase

/-- **The sound-route residual from the gaps of lanes gl-p07-32, 33 and 34.** -/
theorem witnessPlanarClosePinchCase_of_curveSublist_noPlanarDegenStep_walkDegen
    (hcurve : FourPieceWitness.WitnessCurveSublistNondegStatement.{u, w, v})
    (hstep : FourPieceWitness.NoPlanarDegenStepStatement.{u, w, v})
    (hwalk : PinchCase.WalkDegenStatement.{u, w, v}) :
    SoundRoute.PinchCaseStatement.{u, w, v} :=
  PinchCase.pinchCase_of_read_rest
    (PinchCase.read_of_noninterleaveNondeg
      (FourPieceWitness.noninterleaveNondeg_of_curveSublist hcurve))
    (PinchCase.rest_of_residual
      (PinchCase.residual_of_noPlanarDegenerate_walkDegen
        (FourPieceWitness.noPlanarDegenerate_of_step hstep) hwalk))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessPlanarClosePinchCase_of_curveSublist_noPlanarDegenStep_walkDegen

/-- **The corrected planar part from the gaps of lanes gl-p07-32, 33 and 34.** -/
theorem witnessPlanarCloseCorrected_of_curveSublist_noPlanarDegenStep_walkDegen
    (hcurve : FourPieceWitness.WitnessCurveSublistNondegStatement.{u, w, v})
    (hstep : FourPieceWitness.NoPlanarDegenStepStatement.{u, w, v})
    (hwalk : PinchCase.WalkDegenStatement.{u, w, v}) :
    PocketFourPieceWitnessPlanarCorrectedStatement.{u, w, v} :=
  witnessPlanarCloseCorrected_of_pinchCase
    (witnessPlanarClosePinchCase_of_curveSublist_noPlanarDegenStep_walkDegen hcurve hstep hwalk)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessPlanarCloseCorrected_of_curveSublist_noPlanarDegenStep_walkDegen

/-- **The corrected planar part from the step statements** owned by the sibling lanes gl-p07-40
(`WitnessCurveSublistStepStatement`), gl-p07-41 (`AbsorbFaceSetStatement`) and gl-p07-39b
(`WalkDegenStepStatement`). -/
theorem witnessPlanarCloseCorrected_of_steps
    (hcurve : FourPieceWitness.WitnessCurveSublistStepStatement.{u, w, v})
    (habsorb : FourPieceWitness.AbsorbFaceSetStatement.{u, w, v})
    (hwalk : PinchCase.WalkDegenStepStatement.{u, w, v}) :
    PocketFourPieceWitnessPlanarCorrectedStatement.{u, w, v} :=
  witnessPlanarCloseCorrected_of_curveSublist_noPlanarDegenStep_walkDegen
    (FourPieceWitness.witnessCurveSublistNondeg_of_step hcurve)
    (FourPieceWitness.noPlanarDegenStep_of_absorbFaceSet habsorb)
    (PinchCase.walkDegen_of_step hwalk)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessPlanarCloseCorrected_of_steps

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
