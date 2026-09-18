import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepDoneRead
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCaseProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.SoundRouteProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.NoPlanarDegenStepProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.AbsorbFaceSetProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.AbsorbLobeProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WalkDegenStepProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WalkDegenCaseProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.Assembly
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-67: `PocketFourPieceOffStatement` over (rest) only

With clause (read) now closed (`witnessStepDone_read`, `WitnessStepDoneRead`), every existing
route to `PocketFourPieceOffStatement` loses its (read)-side hypothesis.  Every binder below is
an open residual already in the repo.  None is FALSE and none is a new Statement:

* `PinchCase.RestStatement` (`PinchCaseRestStatement.lean:24`; OPEN, PLAUSIBLE), and its LOUD
  equivalent `PinchCase.ResidualStatement` (`PinchCaseResidualStatement.lean:77`;
  `rest_of_residual`/`residual_of_rest`).  This is the weakest remaining hypothesis: each pair
  below implies it.
* `FourPieceWitness.NoPlanarDegenerateStatement` (`FourPieceNoPlanarStatement.lean:112`) with
  `PinchCase.WalkDegenStatement` (`PinchCaseWalkStatement.lean:38`); `WalkDegen` is no stronger
  than (rest) (`walkDegen_of_rest`).
* The equivalent absorb family `NoPlanarDegenStep ≡ AbsorbFaceSet ≡ AbsorbLobe`
  (`NoPlanarDegenStepStatement.lean:72`, `AbsorbFaceSetStatement.lean:152`,
  `AbsorbLobeStatement.lean:79`) paired with the walk family `WalkDegen`, `WalkDegenStep` or
  `WalkDegenCase` (`WalkDegenStepStatement.lean:67`, `WalkDegenCaseStatement.lean:87`).
* `PocketFourPieceArcAuditResidualStatement` (`FourPieceArcAuditStatement.lean:72`; the
  corrected, strictly weaker arc audit).

Avoided: the FALSE `PocketFourPieceInputProofResidualStatement`,
`PocketFourPieceWitnessPlanarStatement` and `PocketFourPieceLakeReadStatement`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 4.4 at
least-area diagrams); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

/-- **The pinch case from clause (rest) alone.** -/
theorem witnessStepDone_pinchCase (hrest : PinchCase.RestStatement.{u, w, v}) :
    SoundRoute.PinchCaseStatement.{u, w, v} :=
  PinchCase.pinchCase_of_read_rest witnessStepDone_read hrest

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepDone_pinchCase

/-- **P07's top target from clause (rest) alone.** -/
theorem witnessStepDone_off_rest (hrest : PinchCase.RestStatement.{u, w, v}) :
    PocketFourPieceOffStatement.{u, w, v} :=
  SoundRoute.pocketFourPieceOff_of_pinchCase (witnessStepDone_pinchCase hrest)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepDone_off_rest

/-- **P07's top target from the (LOUD: equivalent) pinch-case residual alone.** -/
theorem witnessStepDone_off_residual (hres : PinchCase.ResidualStatement.{u, w, v}) :
    PocketFourPieceOffStatement.{u, w, v} :=
  PinchCase.pocketFourPieceOff_of_read_residual witnessStepDone_read hres

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepDone_off_residual

/-- **P07's top target from the no-walk residual and the walk-degenerate residual.** -/
theorem witnessStepDone_off_noPlanarWalk
    (hdeg : FourPieceWitness.NoPlanarDegenerateStatement.{u, w, v})
    (hwalk : PinchCase.WalkDegenStatement.{u, w, v}) : PocketFourPieceOffStatement.{u, w, v} :=
  PinchCase.pocketFourPieceOff_of_read_noPlanarDegenerate_walkDegen witnessStepDone_read hdeg hwalk

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepDone_off_noPlanarWalk

/-- **P07's top target from the no-planar step and the walk-degenerate residual.** -/
theorem witnessStepDone_off_stepWalk
    (hstep : FourPieceWitness.NoPlanarDegenStepStatement.{u, w, v})
    (hwalk : PinchCase.WalkDegenStatement.{u, w, v}) : PocketFourPieceOffStatement.{u, w, v} :=
  PinchCase.pocketFourPieceOff_of_curveSublist_noPlanarDegenStep_walkDegen
    witnessStepDone_curveNondeg hstep hwalk

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepDone_off_stepWalk

/-- **P07's top target from the no-planar step and the walk-degenerate step.** -/
theorem witnessStepDone_off_stepStep
    (hstep : FourPieceWitness.NoPlanarDegenStepStatement.{u, w, v})
    (hwalk : PinchCase.WalkDegenStepStatement.{u, w, v}) :
    PocketFourPieceOffStatement.{u, w, v} :=
  PinchCase.walkDegen_pocketFourPieceOff_of_step witnessStepDone_curveNondeg hstep hwalk

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepDone_off_stepStep

/-- **P07's top target from the absorbed face set and the walk-degenerate step.** -/
theorem witnessStepDone_off_absorbStep
    (habs : FourPieceWitness.AbsorbFaceSetStatement.{u, w, v})
    (hwalk : PinchCase.WalkDegenStepStatement.{u, w, v}) :
    PocketFourPieceOffStatement.{u, w, v} :=
  PinchCase.walkDegen_pocketFourPieceOff_of_step witnessStepDone_curveNondeg
    (FourPieceWitness.noPlanarDegenStep_of_absorbFaceSet habs) hwalk

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepDone_off_absorbStep

/-- **P07's top target from the absorbed face set and the walk-degenerate case.** -/
theorem witnessStepDone_off_absorbCase
    (habs : FourPieceWitness.AbsorbFaceSetStatement.{u, w, v})
    (hcase : PinchCase.WalkDegenCaseStatement.{u, w, v}) :
    PocketFourPieceOffStatement.{u, w, v} :=
  PinchCase.walkDegenCase_pocketFourPieceOff witnessStepDone_curveNondeg habs hcase

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepDone_off_absorbCase

/-- **P07's top target from the absorbed lobe and the walk-degenerate case.** -/
theorem witnessStepDone_off_lobeCase
    (hlobe : FourPieceWitness.AbsorbLobeStatement.{u, w, v})
    (hcase : PinchCase.WalkDegenCaseStatement.{u, w, v}) :
    PocketFourPieceOffStatement.{u, w, v} :=
  PinchCase.walkDegenCase_pocketFourPieceOff witnessStepDone_curveNondeg
    (FourPieceWitness.absorbLobe_absorbFaceSet hlobe) hcase

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepDone_off_lobeCase

/-- **P07's top target from the corrected arc-audit residual alone.** -/
theorem witnessStepDone_off_arcAudit (hres : PocketFourPieceArcAuditResidualStatement.{u, w, v}) :
    PocketFourPieceOffStatement.{u, w, v} :=
  SoundRoute.pocketFourPieceOff_of_pinchCase
    (SoundRoute.pinchCase_of_arcAuditResidual_noninterleaveNondeg hres
      witnessStepDone_noninterleave)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepDone_off_arcAudit

/-- **The enclosed inner pocket (the piece 07 row of the assembly) from clause (rest) alone.** -/
theorem witnessStepDone_enclosed_rest (hrest : PinchCase.RestStatement.{u, w, v}) :
    P07LakeExclusion.InnerPocketEnclosedTwoArcStatement.{u, w, v} :=
  innerPocketEnclosed_of_fourPieceOff (witnessStepDone_off_rest hrest)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepDone_enclosed_rest

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
