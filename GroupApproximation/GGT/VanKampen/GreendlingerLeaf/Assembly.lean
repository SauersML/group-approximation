import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Common.EightResidualWaist
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece01.Proof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.Proof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece05.Proof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.Proof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece07.Proof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P08ProperArc.Proof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.Proof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10.Proof
import GroupApproximation.Meta.AxiomGuard

/-!
# The Greendlinger leaf, assembled

Osin, arXiv:math/0411039v3, §9 and Appendix, Lemmas 9.4, 9.7 and 4.4, at least-area diagrams: the
leaf `RelativeGreendlingerQuasiGeodesicLeastAreaStatement` (`Estimating/OsinAppendixSections`) of
Hull's small cancellation theorem (`thm:hull`).

Route.  `relativeGreendlingerQuasiGeodesicLeastArea_of_eightResiduals`
(`GreendlingerLeaf/Common/EightResidualWaist`) is the V8 waist with every closed leaf supplied.  It is
applied to the piece proofs `GreendlingerLeaf.Piece<NN>.proof`, each in the module
`GreendlingerLeaf/Piece<NN>/Proof`:

* 01 `OsinLemma94ClassEndLoopsBudgetInput`;
* 04 `OsinLemma94ClassCaseGapSpanStatement`;
* 05 `OsinTwoGonCleanCopySectionStatement`;
* 06 `CellPocketOuterPinchStepSectionDistinctStatement`;
* 07 `CellPocketWalkProperArcsBelowSectionStatement`;
* 08 `OsinSectionPocketFaceSetProperSectionStatement`;
* 09 `OsinSectionPocketFaceSetWholeSectionTwoArcSectionStatement`;
* 10 `PocketOuterPinchStepSectionStatement`.

The waist already supplies piece 02, `SameCellPocketLoopCutStatement`, as `sameCellPocketLoopCut`
(also exposed as `GreendlingerLeaf.Piece02.proof`).  The waist does not consume piece 03,
`EnclosedSubdiagramLoopCutSuccStatement`: its only use in V8 is the Case 1 same-cell branch, which is
proved as `osinLemma94CaseOneSameCell`.  Neither piece is imported here.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemmas 9.4, 9.7 and
4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf

universe u w v

/-- **Osin's Lemma 4.4 at least-area diagrams**, with no hypotheses: the eight-residual waist applied
to the proofs of the open pieces. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_eightResiduals
    GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece01.proof
    GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.proof
    GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece05.proof
    GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.proof
    GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece07.proof
    GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P08ProperArc.proof
    GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.proof
    GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10.proof

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf

#audit_closed_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.relativeGreendlingerQuasiGeodesicLeastArea
