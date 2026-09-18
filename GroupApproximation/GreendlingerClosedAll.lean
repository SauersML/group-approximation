import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmTrio.ClosedTrio
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmWaist.Statement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmWaist.Trio
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmWaist.Endpoint
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmFrontier.Gaps
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmFrontier.OuterPinch
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmFrontier.Frontier
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmFrontier.Tight
import GroupApproximation.GreendlingerClosedAll.Pending
import GroupApproximation.Meta.AxiomGuard

/-!
# Root-import aggregator of the closed Greendlinger leaf and its carriers

Lane gl-assembly-12.  Pure wiring: this module declares nothing and only re-audits the endpoints of
the gl-assembly lanes.  The lead adds the single line `import GroupApproximation.GreendlingerClosedAll`
to `GroupApproximation.lean`.

Osin, arXiv:math/0411039v3, Lemma 4.4 at least-area diagrams
(`GroupApproximation.GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement`,
`Estimating/OsinAppendixSections`), the Greendlinger waist of Hull's Theorem 7.1.

## The eight residuals of the Below waist

`GreendlingerLeaf.relativeGreendlingerQuasiGeodesicLeastArea_of_eightResidualsBelow`
(`GreendlingerLeaf/Common/EightResidualWaistBelow`):

| # | binder | residual | producer on disk |
|---|---|---|---|
| 01 | `hbudget` | `OsinLemma94ClassEndLoopsBudgetInput` | `Piece01.proof` |
| 04 | `hspan` | `OsinLemma94ClassCaseGapSpanStatement` | open: `Piece04.ClassPocketRotationTurnStatement` |
| 05 | `htwocopy` | `OsinTwoGonCleanCopySectionStatement` | `Piece05.proof` (`AsmTrio.twoCopy`) |
| 06 | `hcellStep` | `CellPocketOuterPinchStepSectionDistinctBelowStatement` | open: `Piece06.CellRoseUncutLakesBelowStatement` (monogon corner closed) |
| 07 | `hproper` | `CellPocketWalkProperArcsBelowSectionStatement` | open: `P07LakeExclusion.CellPocketInnerTwoArcLongStatement` |
| 08 | `hfaces` | `OsinSectionPocketFaceSetProperSectionStatement` | `P08ProperArc.proof` (`AsmTrio.faces`) |
| 09 | `hwhole` | `OsinSectionPocketFaceSetWholeSectionTwoArcSectionStatement` | `Piece09.proof` (`AsmTrio.whole`) |
| 10 | `hstep` | `PocketOuterPinchStepSectionStatement` | open: `P10Rose.RoseRegionMoveSubArcStatement` (non-rose step closed) |

The four open Statements are bundled in `ClosedAll.OpenFrontierStatement`
(`GreendlingerClosedAll/Pending`), with the reduction
`ClosedAll.relativeGreendlingerQuasiGeodesicLeastArea_of_openFrontier`.

## Imported lanes

* gl-assembly-01 `AsmTrio/ClosedTrio`; gl-assembly-02 `AsmWaist/Statement`, `AsmWaist/Trio`,
  `AsmWaist/Endpoint`; gl-assembly-03 `AsmFrontier/Gaps`, `AsmFrontier/OuterPinch`,
  `AsmFrontier/Frontier`, `AsmFrontier/Tight`.
* Not imported: `GreendlingerLeaf/Assembly`, `Piece04/Proof`, `Piece04/Residual`, `Piece06/Proof`,
  `Piece07/Proof`, `Piece10/Proof`.  `Piece01/Proof` enters only through `AsmFrontier/Tight`, now
  that `P01EmptyTwoGon/Endpoint` provides `P01EmptyTwoGon.proof`.

## Pending lanes (not on disk at authoring time)

When they land, add these imports and closed audits here:

* gl-assembly-04 `GreendlingerLeaf/AsmClose/*`: `AsmClose.relativeGreendlingerQuasiGeodesicLeastAreaClosed`
  (and the five region endpoint modules it imports);
* gl-assembly-05 `Manuscript/NonMF/GreendlingerClosedHull/*`;
* gl-assembly-06 `Manuscript/NonMF/GreendlingerClosedSaturation/*`;
* gl-assembly-07 `Manuscript/NonMF/GreendlingerClosedTorsionFree/*`;
* gl-assembly-08 `Manuscript/NonMF/GreendlingerClosedSteps/*`;
* gl-assembly-09 `Manuscript/NonMF/GreendlingerClosedForms/*`;
* gl-assembly-10 `Manuscript/MFRecognition/SeedClosed/*`;
* gl-assembly-11 `Manuscript/SimpleKazhdanSofic/HyperbolicKazhdanHostClosed/*`.

## Census rows that flip once gl-assembly-04 lands

NM: a16637da7249 (66), abb56744db26 (292), 0f22bdbc4184 (297), dce7a9ff4e83 (303),
8aead549f1fe (2122), bcc99703f838 (2129), 2f55113239ce (2136), 2f997e5af4e6 (2144),
8097c371f35d (2160), 721da4c14d11 (2182), 7b1fa3182135 and 8b1ec28a0e73 (2204); to check:
4895f03fdf5f (2122), 2d1cd22e5f49 (2144), dab2f2bfe084 (2160).  MFR: c6172bdc109a (655).
SK: fc84c012b409 (477).  None flips from this module alone: the leaf still rests on
`ClosedAll.OpenFrontierStatement`.
-/

-- gl-assembly-01: the closed trio.
#audit_closed_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmTrio.closedTrio
#audit_closed_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmTrio.twoCopy
#audit_closed_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmTrio.faces
#audit_closed_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmTrio.whole
#audit_closed_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmWaist.closedTrio

-- Hypothesis-free region producers consumed by the leaf.
#audit_closed_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece01.proof
#audit_closed_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece05.proof
#audit_closed_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P08ProperArc.proof
#audit_closed_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.proof
#audit_closed_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.MonogonCorner.monogonCorner
#audit_closed_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.proof

-- gl-assembly-02 and gl-assembly-03: Statement-hypothesis reductions (interfaces).
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmWaist.relativeGreendlingerQuasiGeodesicLeastArea_of_fiveResidualsBelow
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmWaist.relativeGreendlingerQuasiGeodesicLeastArea_of_openResidualsBelow
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmFrontier.relativeGreendlingerQuasiGeodesicLeastArea_of_frontier
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmFrontier.relativeGreendlingerQuasiGeodesicLeastArea_of_tightFrontier

-- gl-assembly-12 pending interface.
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.ClosedAll.openResidualsBelow_of_openFrontier
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.ClosedAll.relativeGreendlingerQuasiGeodesicLeastArea_of_openFrontier
