import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.LakeReadFixOff
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WalkDegenStepProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessCurveSublistProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.AbsorbFaceSetProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessCurveStepProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.AbsorbLobeProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WalkDegenCaseProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AssemblyResidual
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-42b: the 07 row without any lake statement

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Certifies no printed sentence on its own.

The false `PocketFourPieceLakeReadStatement` is used only to reach `PocketFourPieceOffStatement`
(see `LakeReadFixStatement.lean`).  This module reaches that consumer, and the leaf, from the
three step statements of the sibling lane gl-p07-43 (`WitnessPlanarCloseRoute.lean`):
* `FourPieceWitness.WitnessCurveSublistStepStatement` (lane 36c; residual of gl-p07-40);
* `FourPieceWitness.AbsorbFaceSetStatement` (lane 38; residual of gl-p07-41);
* `PinchCase.WalkDegenStepStatement` (lane 37c; residual of gl-p07-39b).

* `lakeReadFix_pocketFourPieceOff_of_steps`: the 07 row from the steps.
* `lakeReadFix_innerPocketEnclosed_of_steps`: the enclosed inner pocket from the steps.
* `lakeReadFix_of_core_steps`: the corrected lake reading from the core reading and the steps.
* `lakeReadFix_pocketFourPieceOff_of_residuals`: the 07 row from the deeper sibling residuals
  (`WitnessStepResidualStatement`, `AbsorbLobeStatement`, `WalkDegenCaseStatement`).
* `lakeReadFix_relativeGreendlinger_of_steps`, `lakeReadFix_relativeGreendlinger_of_fix`: the leaf
  with the 07 row supplied by the steps, respectively by `LakeReadFixStatement`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

/-- **The four-piece off statement from the sibling step statements**, without any lake
statement. -/
theorem lakeReadFix_pocketFourPieceOff_of_steps
    (hcurve : FourPieceWitness.WitnessCurveSublistStepStatement.{u, w, v})
    (habsorb : FourPieceWitness.AbsorbFaceSetStatement.{u, w, v})
    (hwalk : PinchCase.WalkDegenStepStatement.{u, w, v}) :
    PocketFourPieceOffStatement.{u, w, v} :=
  PinchCase.walkDegen_pocketFourPieceOff_of_step
    (FourPieceWitness.witnessCurveSublistNondeg_of_step hcurve)
    (FourPieceWitness.noPlanarDegenStep_of_absorbFaceSet habsorb) hwalk

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.lakeReadFix_pocketFourPieceOff_of_steps

/-- **The enclosed inner pocket from the sibling step statements.**  It replaces
`innerPocketEnclosed_of_lakeRead`. -/
theorem lakeReadFix_innerPocketEnclosed_of_steps
    (hcurve : FourPieceWitness.WitnessCurveSublistStepStatement.{u, w, v})
    (habsorb : FourPieceWitness.AbsorbFaceSetStatement.{u, w, v})
    (hwalk : PinchCase.WalkDegenStepStatement.{u, w, v}) :
    P07LakeExclusion.InnerPocketEnclosedTwoArcStatement.{u, w, v} :=
  innerPocketEnclosed_of_fourPieceOff (lakeReadFix_pocketFourPieceOff_of_steps hcurve habsorb hwalk)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.lakeReadFix_innerPocketEnclosed_of_steps

/-- **The corrected lake reading from gl-p07-18's core reading and the sibling steps.** -/
theorem lakeReadFix_of_core_steps (hcore : PocketFourPieceLakeReadCoreStatement.{u, w, v})
    (hcurve : FourPieceWitness.WitnessCurveSublistStepStatement.{u, w, v})
    (habsorb : FourPieceWitness.AbsorbFaceSetStatement.{u, w, v})
    (hwalk : PinchCase.WalkDegenStepStatement.{u, w, v}) :
    LakeReadFixStatement.{u, w, v} :=
  lakeReadFix_of_core_off hcore (lakeReadFix_pocketFourPieceOff_of_steps hcurve habsorb hwalk)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.lakeReadFix_of_core_steps

/-- **The four-piece off statement from the deeper sibling residuals**: gl-p07-40's
`WitnessStepResidualStatement`, gl-p07-41's `AbsorbLobeStatement` and gl-p07-39b's
`WalkDegenCaseStatement`. -/
theorem lakeReadFix_pocketFourPieceOff_of_residuals
    (hstep : FourPieceWitness.WitnessStepResidualStatement.{u, w, v})
    (hlobe : FourPieceWitness.AbsorbLobeStatement.{u, w, v})
    (hcase : PinchCase.WalkDegenCaseStatement.{u, w, v}) :
    PocketFourPieceOffStatement.{u, w, v} :=
  lakeReadFix_pocketFourPieceOff_of_steps
    (FourPieceWitness.witnessCurveSublistStep_of_witnessStepResidual hstep)
    (FourPieceWitness.absorbLobe_absorbFaceSet hlobe) (PinchCase.walkDegenCase_step hcase)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.lakeReadFix_pocketFourPieceOff_of_residuals

/-- **The leaf with the 07 row from the sibling step statements.** -/
theorem lakeReadFix_relativeGreendlinger_of_steps
    (hcurve : FourPieceWitness.WitnessCurveSublistStepStatement.{u, w, v})
    (habsorb : FourPieceWitness.AbsorbFaceSetStatement.{u, w, v})
    (hwalk : PinchCase.WalkDegenStepStatement.{u, w, v})
    (hjunction : P10RoseExtremalTrim.RoseExtremalJunctionStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  AssemblyResidual.relativeGreendlinger_of_residuals
    (lakeReadFix_pocketFourPieceOff_of_steps hcurve habsorb hwalk) hjunction

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.lakeReadFix_relativeGreendlinger_of_steps

/-- **The leaf with the 07 row from the corrected lake reading.**  It replaces any use of the
false `PocketFourPieceLakeReadStatement` on the way to the leaf. -/
theorem lakeReadFix_relativeGreendlinger_of_fix (hfix : LakeReadFixStatement.{u, w, v})
    (hjunction : P10RoseExtremalTrim.RoseExtremalJunctionStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  AssemblyResidual.relativeGreendlinger_of_residuals (lakeReadFix_pocketFourPieceOff hfix)
    hjunction

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.lakeReadFix_relativeGreendlinger_of_fix

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
