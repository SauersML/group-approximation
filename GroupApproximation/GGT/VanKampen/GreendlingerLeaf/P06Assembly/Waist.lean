import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Assembly.Proof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Common.EightResidualWaistBelow
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmTrio.ClosedTrio
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmFrontier.Gaps
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmFrontier.OuterPinch
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece01.Proof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.Proof
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06 assembly: the Greendlinger leaf with residual 06 retired

Osin, arXiv:math/0411039v3, §9 (Lemmas 9.4, 9.7 and 4.4).  Lane gl-p06-04, item (v).

## The waist over binder 5

`relativeGreendlingerQuasiGeodesicLeastArea_of_copyBelow` is the term of
`relativeGreendlingerQuasiGeodesicLeastArea_of_eightResidualsBelow`
(`Common/EightResidualWaistBelow.lean:33`) with one change.  Binder 5 below the bound
(`OsinMultipleEdgePocketRegionCopyBelowSectionStatement`) is taken as a hypothesis in place of
`osinMultipleEdgePocketRegionCopyBelowSection_of_pinchBelowSectionOrderEuler …`.  So neither
`hcellStep` nor `hproper` occurs.  Residuals 05, 08 and 09 are the closed trio
`AsmTrio.twoCopy`, `AsmTrio.faces`, `AsmTrio.whole`.

## The frontier through the bypass

`greendlinger_of_frontier` feeds the waist as follows:
* `Piece01.proof` for the budget;
* `AsmFrontier.gapSpan_of_rotationTurns` for the gap span;
* `proof_of_innerPocketEnclosed_of_bypass` for binder 5;
* `AsmFrontier.outerPinchStep_of_nonRose_subArc P10ChordLift.proof` for the outer pinch step.

What remains open:
* the two bypass reductions of `P06Assembly/Bypass` (lanes gl-p06-01, gl-p06-02, in flight);
* `Piece04.ClassPocketRotationTurnStatement`;
* `P07LakeExclusion.InnerPocketEnclosedTwoArcStatement` (lane gl-p07-15);
* `P10Rose.RoseRegionMoveSubArcStatement`.

Once lane gl-p06-03 lands, item (v) of the lane is the re-export
```
theorem greendlinger_of_frontier
    (hrot : Piece04.ClassPocketRotationTurnStatement.{u, w, v})
    (hencl : P07LakeExclusion.InnerPocketEnclosedTwoArcStatement.{u, w, v})
    (hsub : P10Rose.RoseRegionMoveSubArcStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  P06Bypass.relativeGreendlingerQuasiGeodesicLeastArea_of_bypassFrontier hrot hencl hsub
```

Not imported: `GreendlingerLeaf/Assembly`, `Piece04/Proof`, `Piece06/Proof`, `Piece07/Proof`,
`Piece10/Proof` and `P10Rose/Live`.

## Manuscript status

Infrastructure for `thm:hull` (Osin's Lemma 4.4 at least-area diagrams); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Assembly

universe u w v

/-- **Osin's Lemma 4.4 at least-area diagrams over binder 5 below the bound**: the Below waist
with binder 5 as a hypothesis, so residuals 06 and 07 do not occur.  Residuals 05, 08 and 09 are the
closed trio. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_copyBelow
    (hbudget : OsinLemma94ClassEndLoopsBudgetInput.{u, w, v})
    (hspan : OsinLemma94ClassCaseGapSpanStatement.{u, w, v})
    (hcopy : OsinMultipleEdgePocketRegionCopyBelowSectionStatement.{u, w, v})
    (hstep : PocketOuterPinchStepSectionStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_pocketPartsBelow
    (osinLemma94Section_of_classCountTwoThreshold
      (osinLemma94ClassCountInput_of_endLoops (osinLemma94ClassEndLoopsInput_of_budget hbudget)
        (osinLemma94SameCellFactorInput_of_scan
          (osinLemma94SameCellScanInput_of_pocket
            (osinLemma94SameCellPocketInput_of_loopCut sameCellPocketCellFreeValue
              sameCellPocketLoopCut))))
      (osinLemma94ClassCasesTwoThreshold_of_residuals
        (osinLemma94CaseOneInput_of_walk osinLemma94CaseOneWalk osinLemma94CaseOneSameCell)
        osinLemma94CaseTwoInput hspan))
    (osinMultipleEdgeCutBelowSection_of_copyPieces hcopy
      GeodesicCollar.StripStep.geodesicCollarStatement_holds pocketCellTransport)
    osinLoopCutSection
    (osinPhiPrimeCountSection_of_pieces osinCornerTwoGonSection
      (osinTwoGonHoldsSection_of_cleanCopyEuler AsmTrio.twoCopy.{u, w, v}
        osinTwoGonDecompositionEulerSection))
    (osinSectionPocketCutSection_of_residualsTwoArc
      (osinSectionPocketFaceSetTwoArcSection_of_proper_of_wholeSection AsmTrio.faces.{u, w, v}
        AsmTrio.whole.{u, w, v})
      (pocketPinchLabelledSectionTwoArcStatement_of_outerPinchStep hstep)
      GeodesicCollar.StripStep.geodesicCollarStatement_holds)

/-- **Osin's Lemma 4.4 at least-area diagrams from the bypass frontier**: the two bypass reductions,
the rotation turns of a class pocket, the enclosed inner pocket and the sub-arc region move of the
rose case.  Residual 06 is retired: binder 5 comes from the enclosed inner pocket through the
bypass. -/
theorem greendlinger_of_frontier
    (hrefuted : RefutedOfInnerPocketEnclosedStatement.{u, w, v})
    (hcopy : CopyBelowOfRefutedStatement.{u, w, v})
    (hrot : Piece04.ClassPocketRotationTurnStatement.{u, w, v})
    (hencl : P07LakeExclusion.InnerPocketEnclosedTwoArcStatement.{u, w, v})
    (hsub : P10Rose.RoseRegionMoveSubArcStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_copyBelow Piece01.proof.{u, w, v}
    (AsmFrontier.gapSpan_of_rotationTurns hrot)
    (proof_of_innerPocketEnclosed_of_bypass hrefuted hcopy hencl)
    (AsmFrontier.outerPinchStep_of_nonRose_subArc P10ChordLift.proof.{u, w, v} hsub)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Assembly

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Assembly.relativeGreendlingerQuasiGeodesicLeastArea_of_copyBelow
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Assembly.greendlinger_of_frontier
