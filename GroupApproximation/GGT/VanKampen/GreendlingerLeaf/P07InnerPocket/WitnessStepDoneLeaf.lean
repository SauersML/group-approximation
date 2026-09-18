import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepDoneOff
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.JunctionCore
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-67: the leaf over (rest) and the lobe removal

Osin, arXiv:math/0411039v3, §9 and Appendix, Lemmas 9.4, 9.7 and 4.4, at least-area diagrams:
the leaf `RelativeGreendlingerQuasiGeodesicLeastAreaStatement` (`Estimating/OsinAppendixSections`).

This is wiring only.  It feeds `witnessStepDone_off_rest` (and its variants,
`WitnessStepDoneOff`) into
`P10RoseExtremalTrim.roseJunctionCore_relativeGreendlinger_of_lobeRemoval`
(`P10RoseExtremalTrim/JunctionCore.lean:272`).  The leaf then rests on exactly two open
Statements already in the repo:

* piece 07: `PinchCase.RestStatement` (`P07InnerPocket/PinchCaseRestStatement.lean:24`;
  OPEN, PLAUSIBLE; no model refutes it).  The pairs of `WitnessStepDoneOff` may replace it.
* piece 10: `P10RoseExtremalTrim.roseJunctionCore_LobeRemovalStatement`
  (`P10RoseExtremalTrim/JunctionCore.lean:185`; OPEN, PLAUSIBLE, backed by the exhaustive search
  recorded in that module's docstring).

Avoided: `GreendlingerLeaf.relativeGreendlingerQuasiGeodesicLeastArea_of_residuals` and
`AssemblyResidual.relativeGreendlinger_of_residuals`.  Their binder
`RoseExtremalJunctionStatement` is LOUD FALSE (lane gl-p10-48).  The `P10RoseLobe`
residuals (`roseLobe_FilterListing`, `roseLobeFL_Block`, `roseLobeBlk_Block`, `roseLobePlace`)
are logically stronger than, or equivalent to, the lobe removal, so it is the weakest piece-10
input on disk.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemmas 9.4, 9.7
and 4.4); certifies no printed sentence on its own.  The leaf stays open until both Statements
above are proved.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

/-- **The Greendlinger leaf from clause (rest) and the lobe removal.** -/
theorem witnessStepDone_leaf_rest (hrest : PinchCase.RestStatement.{u, w, v})
    (hlobe : P10RoseExtremalTrim.roseJunctionCore_LobeRemovalStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  P10RoseExtremalTrim.roseJunctionCore_relativeGreendlinger_of_lobeRemoval
    (witnessStepDone_off_rest hrest) hlobe

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepDone_leaf_rest

/-- **The Greendlinger leaf from the no-walk residual, the walk-degenerate residual and the lobe
removal.** -/
theorem witnessStepDone_leaf_noPlanar
    (hdeg : FourPieceWitness.NoPlanarDegenerateStatement.{u, w, v})
    (hwalk : PinchCase.WalkDegenStatement.{u, w, v})
    (hlobe : P10RoseExtremalTrim.roseJunctionCore_LobeRemovalStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  P10RoseExtremalTrim.roseJunctionCore_relativeGreendlinger_of_lobeRemoval
    (witnessStepDone_off_noPlanarWalk hdeg hwalk) hlobe

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepDone_leaf_noPlanar

/-- **The Greendlinger leaf from the corrected arc-audit residual and the lobe removal.** -/
theorem witnessStepDone_leaf_arcAudit
    (hres : PocketFourPieceArcAuditResidualStatement.{u, w, v})
    (hlobe : P10RoseExtremalTrim.roseJunctionCore_LobeRemovalStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  P10RoseExtremalTrim.roseJunctionCore_relativeGreendlinger_of_lobeRemoval
    (witnessStepDone_off_arcAudit hres) hlobe

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessStepDone_leaf_arcAudit

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
