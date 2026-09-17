import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerTwoGonCleanCopy
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05Spur.Proof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterCell.Proof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterSide.Proof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellSide.Proof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.Proof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.Proof
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf, piece 05: the clean copy of a two-gon section

Osin, arXiv:math/0411039v3, Appendix (the two-gon decomposition of the Euler count).
`OsinTwoGonCleanCopySectionStatement` (`Estimating/OsinAppendixEulerTwoGonCopyRoute`) is the `htwocopy`
residual of `relativeGreendlingerQuasiGeodesicLeastArea_of_eightResiduals`
(`GreendlingerLeaf/Common/EightResidualWaist`).

## Route

`osinTwoGonCleanCopySection_of_steps` (`Estimating/OsinAppendixEulerTwoGonCleanCopy`) over the six
surgery steps of the clean copy (`Estimating/OsinAppendixEulerTwoGonDoublingTransport`).

## Assumed sub-leaf endpoints

Each sub-leaf lives in the module `GreendlingerLeaf/<Dir>/Proof` and exposes, in the namespace
`GroupApproximation.GGT.VanKampen.GreendlingerLeaf.<Dir>`, a theorem `proof`:

* `P05Spur.proof : TwoGonSpurStepStatement.{u, w, v}`;
* `P05OuterCell.proof : TwoGonOuterCellStepStatement.{u, w, v}`;
* `P05OuterSide.proof : TwoGonOuterSideStepStatement.{u, w, v}`;
* `P05CellSide.proof : TwoGonCellSideStepStatement.{u, w, v}`;
* `P05CellHair.proof : TwoGonCellHairStepStatement.{u, w, v}`;
* `P05RegionPair.proof : TwoGonRegionPairStepStatement.{u, w, v}`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 4.4 and the
Appendix); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece05

universe u w v

/-- **Piece 05 of the Greendlinger leaf: `OsinTwoGonCleanCopySectionStatement` holds**, with no
hypotheses: the six clean-copy steps assembled by `osinTwoGonCleanCopySection_of_steps`. -/
theorem proof : OsinTwoGonCleanCopySectionStatement.{u, w, v} :=
  osinTwoGonCleanCopySection_of_steps
    GreendlingerLeaf.P05Spur.proof
    GreendlingerLeaf.P05OuterCell.proof
    GreendlingerLeaf.P05OuterSide.proof
    GreendlingerLeaf.P05CellSide.proof
    GreendlingerLeaf.P05CellHair.proof
    GreendlingerLeaf.P05RegionPair.proof

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece05

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece05.proof
