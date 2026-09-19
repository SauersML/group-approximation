import GroupApproximation.Manuscript.NonMF.Full.GL06.Assembly
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10FilterMoveExists.Endpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# The Greendlinger waist with residual 10 read as the quadrant move

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull` in
`non_mf_groups_exist.tex` (around line 2121); certifies no printed sentence on its own.

`Full.GL06.relativeGreendlinger_of_allCells_of_core` consumes residual 10,
`GL03DKept.gl03dKept_KeptSubwalkCoreStatement`, only through
`GL03D.gl03dKept_roseRegionMoveSubArc_of_core`, i.e. only as
`GL06f.RoseRegionMoveSubArcStatement`.  Lane gl-p10-91 proved
`P10FilterMoveExists.p10FM_regionMoveSubArc`: the sub-arc region move of `P10Rose` from
`p10FM_QuadrantMoveStatement`, a statement about a planar map, a face set and its boundary cycle
only, with no pocket, diagram, labels or least area.

* `gl06fRoseRegionMoveSubArc_of_p10Rose`: the `P10Rose` copy of the region move gives the `GL06f`
  one.  The two definitions have the same body.  They differ only in the names of their
  `AllNonFirstTurnsCrossed` and `movePred`, and `GL06f` and `GL05b` restate those with the same
  bodies.  So the proof is the hypothesis itself, up to unfolding.
* `relativeGreendlinger_of_allCells_of_quadrantMove`: Osin's Lemma 4.4 at least-area diagrams from
  the all-cells residual and the quadrant move.

**CONDITIONAL, stated loudly.**  Both hypotheses are unproved in the repository: `hall`
(binder 5) and `hqm`, the quadrant move.  The quadrant move is **not** weaker than residual 10.
It is at least as strong in generality (see `P10FilterMoveExists/Residual`, LOUD section), so
this theorem does not replace `relativeGreendlinger_of_allCells_of_core`.  It is an alternative
route whose open input is pure planar combinatorics, truth-checked by lane gl-p10-91 on about
1.4 million random configurations with 0 failures.
-/

namespace GroupApproximation.Full.GL03DQuadrant

universe u w v

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen

/-- **The `GL06f` sub-arc region move from its `P10Rose` copy** (Osin 9.7(b), `thm:hull`
infrastructure).  The two statements have the same body up to restated definitions. -/
theorem gl06fRoseRegionMoveSubArc_of_p10Rose
    (h : GreendlingerLeaf.P10Rose.RoseRegionMoveSubArcStatement.{u, w, v}) :
    GL06f.RoseRegionMoveSubArcStatement.{u, w, v} := h

/-- **Osin's Lemma 4.4 at least-area diagrams, CONDITIONAL on binder 5 and the quadrant move**
(relative Greendlinger lemma; `thm:hull` infrastructure, non_mf_groups_exist.tex ~2121).  The
route of `Full.GL06.relativeGreendlinger_of_allCells_of_core`, with the rose step taken from the
quadrant move through `P10FilterMoveExists.p10FM_regionMoveSubArc`. -/
theorem relativeGreendlinger_of_allCells_of_quadrantMove
    (hall : GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{u, w, v})
    (hqm : GreendlingerLeaf.P10FilterMoveExists.p10FM_QuadrantMoveStatement.{v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  GL06.relativeGreendlingerQuasiGeodesicLeastArea_of_residuals
    GroupApproximation.Full.GL06a.budget.{u, w, v}
    GroupApproximation.Full.GL06b.twoGonCleanCopy.{u, w, v}
    GroupApproximation.Full.GL06c.wholeSectionTwoArc.{u, w, v}
    (GL06.osinMultipleEdgePocketRegionCopyBelowSection_of_refuted
      (GL06e.refutedBelowSection_of_innerPocketEnclosedCorrected_of_allCells
        GroupApproximation.Full.GL03BPinch.innerPocketEnclosedTwoArcCorrected.{u, w, v} hall))
    (GL06.outerPinchStep_of_cases GroupApproximation.Full.GL06d.nonRoseStep.{u, w, v}
      (GroupApproximation.Full.GL06f.rose_of_regionMoveSubArc
        (gl06fRoseRegionMoveSubArc_of_p10Rose
          (GreendlingerLeaf.P10FilterMoveExists.p10FM_regionMoveSubArc hqm))))

/-- The universe-`0` instance, **CONDITIONAL on the same two unproved hypotheses**. -/
theorem relativeGreendlinger_zero_of_allCells_of_quadrantMove
    (hall : GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{0, 0, 0})
    (hqm : GreendlingerLeaf.P10FilterMoveExists.p10FM_QuadrantMoveStatement.{0}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0} :=
  relativeGreendlinger_of_allCells_of_quadrantMove.{0, 0, 0} hall hqm

end GroupApproximation.Full.GL03DQuadrant

#audit_axioms GroupApproximation.Full.GL03DQuadrant.gl06fRoseRegionMoveSubArc_of_p10Rose
#audit_axioms
  GroupApproximation.Full.GL03DQuadrant.relativeGreendlinger_of_allCells_of_quadrantMove
#audit_axioms
  GroupApproximation.Full.GL03DQuadrant.relativeGreendlinger_zero_of_allCells_of_quadrantMove
