# Lane ct-rank-two-limit: the rank-two limitation remark (tex 1794–1807)

Target: `non_mf_groups_exist.tex`, sec:chain-core, the remark after `cor:dynamic-rank-budget`
("There is also a limitation of the compression method at rank two ..."), every sentence, closed.

## GHW Theorem 4 check

`GHW.printedGHWTheoremFour : PrintedGHWTheoremFour` (Kazhdan/GHWTheoremFourClosed, closed at 66417a372)
covers every field `K` and every countable subgroup of `GL_2(K)`.  `GL_2(k[z,z^{-1}])` embeds in
`GL_2(Frac k[z,z^{-1}])`, so the printed consumption has no gap.

## Already on main (consumed, not rebuilt)

- `JacobsonRankTwo.finite_image_and_finite_of_kazhdan` (Manuscript/OneSidedMFRadical/JacobsonRankTwoInert):
  a hom with locally finite kernel into a group whose countable subgroups are Haagerup kills
  nothing infinite: every Kazhdan subgroup is finite.  This is the printed deduction
  "Haagerup + (T) ⇒ finite image; finite-index f.g. locally finite kernel ⇒ finite".
- `printedDefect_eq_bot_of_finite` (DefectSaturation): finite subgroups have trivial printed defect.
- `ClopenCrossedProduct.restrict`, `restrictHomeo` (Dynamics/ClopenCrossedProductComap): core restriction.

## Modules (this lane)

| module | content | status |
|---|---|---|
| `Kazhdan/HaagerupFiniteProduct` | `hasHaagerupProperty_of_injective_pi`, `hasHaagerupProperty_of_injective_pi_glTwo` (GHW at finitely many `GL_2` over fields) | LANDED 8509c9a55 |
| `Algebra/LocallyFiniteCongruenceKernel` | `HasLocallyFiniteKernel ρ`; `hasLocallyFiniteKernel_of_isLocallyMatricialIn`; `glMap n ρ` (noncommutative rings); `isLocallyFiniteGroup_ker_glMap`, `isLocallyFiniteGroup_ker_unitsMap` | LANDED 70317e581 |
| `Dynamics/RankTwoKazhdanLimitStatements` | step Props and printed endpoints (below) | LANDED 70317e581 |
| `Dynamics/RankTwoKazhdanLimitAssembly` | `printedFixedCoreGLTwoKazhdanFinite_of_steps`, `printedPeriodTwoCoreUnitsKazhdanFinite_of_steps`, `printedRankTwoCompressionDefectsTrivial_of_steps` | LANDED 70317e581 |
| `Dynamics/ClopenCrossedProductLaurentEval` | `evalLaurent` (fixed points into `k[z,z^{-1}]`), `evalPair` (period ≤ 2 into `M_2(k[z,z^{-1}])`), `coeff_evalLaurent`, `coeff_evalPair_row` | LANDED 86e64d0a3 |
| `Dynamics/RankTwoCoreImageHaagerup` | `fiberSubring`; `fixedCoreImageHaagerup`, `periodTwoCoreUnitImageHaagerup` (closed); endpoints `printedFixedCoreGLTwoKazhdanFinite_of_kernel`, `printedPeriodTwoCoreUnitsKazhdanFinite_of_kernel`, `printedRankTwoCompressionDefectsTrivial_of_kernel` | LANDED a34f74c76 |

| `Dynamics/RankTwoRestrictionImageFinite` | `finite_map_of_kazhdan_of_haagerup`; closed endpoints `printedFixedCoreRestrictionImageFinite`, `printedPeriodTwoCoreUnitRestrictionImageFinite` (restriction images finite, no kernel hypothesis) | LANDED 11c23415f |

| `Dynamics/RankTwoKazhdanLimitClosed` | closed `coreRestrictionLocallyFiniteKernel` (over ct-involution's `transientIdealLocallyMatricialStatement_holds` and ms-compress-3's glue), `printedFixedCoreGLTwoKazhdanFinite`, `printedPeriodTwoCoreUnitsKazhdanFinite`, `printedRankTwoCompressionDefectsTrivial` | LANDED 3bbabdc89 |

All eight modules are queued for wiring in `$NM/wire-queue.txt`.

**09-13 ~19:00: the remark tex 1794–1807 is CLOSED.**  All four census rows are `formalized` (0f0126ac0).

## Item 2: the top of sec:torsion-free over the copy waist residuals (coordinator ~18:40)

Module `Manuscript/NonMF/TorsionFreeResidualsV2Copy` (namespace `GroupApproximation.Manuscript.NonMF.TorsionFreeResidualsV2Copy`):
every printed endpoint of the section stated `_of_residuals` over exactly the nine named residuals of
`GGT.VanKampen.relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV2Copy` (ms-cite-1, eb678c70a), with the closed
bridge, Kotowski–Ollivier, Hyde–Lodha group, DGO 2.35 and Gerasimova–Osin 1.1 applied.
LANDED b05937611 (probe 0913-190707-24160 GREEN, BUILT and COMPILED, 22 axiom audits classical); queued for wiring.

Residuals, identical for every endpoint (namespace `GGT.VanKampen`, all `.{0, 0, 0}`):
`OsinLemma94PolygonCountInput`, `OsinLemma94CaseOneRCellStatement`, `OsinTwoGonHoldsSectionStatement`,
`CellPocketCopyCleanStatement`, `CellPocketWalkOuterOffSideStatement`, `CellPocketWalkSideRelatorCellStatement`,
`CellPocketPinchPosStatement`, `OsinSectionPocketFaceSetSectionStatement`, `PocketPinchLabelledPosStatement`.
None has a binder-free producer on main at 19:09 (scan calibrated on the closed bridge).

| endpoint(s) | rows |
|---|---|
| `manuscriptTorsionFreeTheorem_of_residuals`, `…FullMFRadical…`, `…TheoremOsin…`, `printedTorsionFreeTheoremLimitSet_of_residuals` | 0f22bdbc4184, a16637da7249 |
| `printedHullTheorem_of_residuals`, `…Osin…`, `…LimitSet…`, `hullSmallCancellationTorsionFreePrinted_of_residuals` | 8aead549f1fe, 4895f03fdf5f |
| `printedHullProofParagraph_of_residuals` | bcc99703f838 |
| `printedSaturation_of_residuals`, `…Osin…`, `…LimitSet…` | 2f55113239ce |
| `printedSaturationPairAndHullAgain_of_residuals` | 2d1cd22e5f49 |
| `printedSaturationApplyHull_of_residuals` | 2f997e5af4e6 |
| `fournierFacioParagraph_of_residuals` | 8097c371f35d |
| `hullCommonQuotientPrinted_of_residuals`, `printedHullCorollary74_of_residuals` | dab2f2bfe084 |
| `printedTheoremApplySaturation_of_residuals` | 721da4c14d11 |
| `manuscriptRegularNonMFAlgebra_of_residuals`, `…Osin…`, `printedRegularNonMFAlgebraLimitSet_of_residuals` | 7b1fa3182135, 8b1ec28a0e73, dce7a9ff4e83 |

Not covered: `a9dd4b90e479` (Hull 3.12 generating set) is not W1-bound; ms-torsionfree proposes it `formalized`.

## Item 3: the V4 waist (coordinator ~19:35)

Module `GGT/VanKampen/Estimating/OsinGreendlingerWaistV4` (additive, through `_of_pocketParts`):
- `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV4CopySection`, 7 residuals, binder 5 whole.
- `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV4`, 10 residuals: `OsinLemma94ClassEndLoopsInput`,
  `OsinLemma94SameCellPocketInput`, `OsinLemma94ClassCasesInput` (class route, ct-bilateral-cell V3);
  `OsinTwoGonHoldsSectionStatement` (C6′); `CellPocketCopyCleanBothOrdersStatement`,
  `CellPocketWalkOuterOffSideSomeOrderStatement`, `CellPocketWalkEitherFollowsStatement`, `CellPocketPinchPosStatement`
  (binder 5 on the copy through `osinMultipleEdgePocketRegionCopySection_of_pinchOrder`, ms-cite-1 da5b1466e);
  `OsinSectionPocketFaceSetProperSectionStatement`, `PocketPinchLabelledSectionStatement` (binders 6 and 7, w1-binder-7).
- Closed pieces applied: `osinLoopCutSection`, `osinCornerTwoGonSection`, `pocketCellTransport`,
  `GeodesicCollar.StripStep.geodesicCollarStatement_holds`.
- ct-bilateral-cell withdrew its local draft of the same name (19:55).  The class-case split
  (`osinLemma94ClassCases_of_residuals`, `OsinLemma94ClassPairTransfer`, probing) is added when it lands.

Module `Manuscript/NonMF/TorsionFreeResidualsV4`: every endpoint of `TorsionFreeResidualsV2Copy` restated `_of_residualsV4`
over the ten residuals of `_of_residualsV4`.

LANDED 4091f7433 (probe 0913-195844-97206 GREEN, both BUILT and COMPILED, 24 audits classical, 0 errors); queued for
wiring.  Census: the 14 W1 rows add the V4 carriers and the V4 residual list, still `partial`.

Module `GGT/VanKampen/Estimating/OsinGreendlingerWaistV4Split`: `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV4Split`,
12 residuals.  `OsinLemma94ClassCasesInput` comes from ct-bilateral-cell's `osinLemma94ClassCases_of_residuals` (6ba28eb0e), over
the closed `osinLemma94CaseOneWalk` and `osinLemma94CaseTwoInput`, from `OsinLemma94CaseOneRCellStatement`,
`OsinLemma94ClassCaseGapEndpointStatement` and `OsinLemma94ClassCaseGapSpanStatement`.  LANDED 3877f8b63.

V4 residual owners (coordinator ~20:30):

| # | residual | owner(s) |
|---|---|---|
| 1 | `OsinLemma94ClassEndLoopsInput` | ms-binary with ms-core-2, ms-compress-1, ms-inverses-3 |
| 2 | `OsinLemma94SameCellPocketInput` | ms-compress-2 |
| 3 | `OsinLemma94ClassCasesInput` | ct-bilateral-cell with ct-return-tower; binder 3 lanes for the RCell part |
| 4 | `OsinTwoGonHoldsSectionStatement` | w1-binder-1 with ms-inverses-2, ms-inverses-4 |
| 5 | `CellPocketCopyCleanBothOrdersStatement` | ms-torsionfree |
| 6 | `CellPocketWalkOuterOffSideSomeOrderStatement` | CLOSED: w1-binder-3's `cellPocketWalkOuterOffSideSomeOrder` (7d1f00831, `Estimating/OsinPocketCellWalkOrder`; probe 0913-202753-83639 GREEN, 12 audits classical, file hash matches origin) |
| 7 | `CellPocketWalkEitherFollowsStatement` | IN FLUX: ms-cite-1 respells the order assembly over ms-inverses-2's `CellPocketWalkEulerStatement` (eb8811c3c); either-follows fails at pinch-type touches |
| 8 | `CellPocketPinchPosStatement` | IN FLUX: ms-cite-1 ε = 1 refutation test |
| 9 | `OsinSectionPocketFaceSetProperSectionStatement` | ms-intro-2, ms-inverses-2, w1-binder-6 |
| 10 | `PocketPinchLabelledSectionStatement` | w1-binder-7, ms-intro-4 |

When ms-cite-1 lands either change, this lane adds a V4 variant over the new spelling; the landed V4 is not edited in place.

Plan (coordinator ~20:35): ms-cite-1 lands additive `…_of_pinchOrderEuler` taking `CellPocketWalkEulerStatement` (eb8811c3c).
The V4 variant over it applies the closed `cellPocketWalkOuterOffSideSomeOrder`, so residual 6 drops and residual 7 becomes the
Euler statement.  The 14 W1 rows are then re-pointed to that variant.

## Item 4: the V4 Euler variant (coordinator ~20:35, resumed 21:22)

ms-cite-1's `Estimating/OsinPocketMultipleEdgeCopyOrderEuler` landed at 7a45179c4 (probe 0913-203827-69476, same bytes).

Module `GGT/VanKampen/Estimating/OsinGreendlingerWaistV4Euler`:
- `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV4Euler`, 9 residuals: `OsinLemma94ClassEndLoopsInput`,
  `OsinLemma94SameCellPocketInput`, `OsinLemma94ClassCasesInput`, `OsinTwoGonHoldsSectionStatement`,
  `CellPocketCopyCleanBothOrdersStatement`, `CellPocketWalkEulerStatement`, `CellPocketPinchPosStatement`,
  `OsinSectionPocketFaceSetProperSectionStatement`, `PocketPinchLabelledSectionStatement`.  Binder 5 comes from
  `osinMultipleEdgePocketRegionCopySection_of_pinchOrderEuler` with `hout := cellPocketWalkOuterOffSideSomeOrder`.
- `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV4EulerSplit`, 11 residuals (class-word cases split).

Module `Manuscript/NonMF/TorsionFreeResidualsV4Euler`: the 22 endpoints `_of_residualsV4Euler` over the 9 residuals.
LANDED 236898aed (probe 0913-213402-40086 GREEN, both BUILT and COMPILED; queued for wiring).  The 14 W1 rows are re-pointed to the V4 Euler carriers and residual list, still `partial`.
A later waist exists: `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV3` (2b2af4479, class route, seven binders).  Its
binder 5 is `OsinMultipleEdgePocketRegionSectionStatement` on the optimal diagram, the form the V2Copy docstring calls
circular, so this module stays on V2Copy.

Census: `2d5721555dfe` (tex 1796–1798) is `formalized`; `f31fa0413ffd`, `dd5ef3eafd48` and `5e4354e1556b` are `partial`
over `CoreRestrictionLocallyFiniteKernelStatement` alone.  They flip to closed when chain-matricial's
`isLocallyMatricialIn_transientIdeal` and ms-compress-3's glue land.

Printed endpoints (namespace `GroupApproximation.ChainCore.RankTwoLimit`):
`PrintedFixedCoreGLTwoKazhdanFinite` (tex 1795–1796), `PrintedPeriodTwoCoreUnitsKazhdanFinite` (tex 1802–1803),
`PrintedRankTwoCompressionDefectsTrivial` (tex 1801–1802).  The kernel lemmas serve any lane that needs local
finiteness of `K_n(I)` over a finite field (`lem:involution-localization` states it for `K_1(I)`; `thm:core-mf-radical`
for `n ≥ 2` over `F_2`).

## Residual Props

- `CoreRestrictionLocallyFiniteKernelStatement`: for compact metric totally disconnected `X`, `T`, finite field `k`,
  `HasLocallyFiniteKernel (ClopenCrossedProduct.restrict T k (image_chainRecurrentSet T))`.
  Route: chain-matricial's `isLocallyMatricialIn_transientIdeal` (not on main at 17:25; `Dynamics/TransientIdealExact`
  has only `transientIdeal` and exactness), then ms-compress-3's glue in `Dynamics/ClopenCrossedProductAlgebra`
  (`Module k` on `R_X`, `TransientIdealLocallyMatricialStatement`,
  `coreRestrictionLocallyFiniteKernel_of_transientLocallyMatricial`, through
  `hasLocallyFiniteKernel_of_isLocallyMatricialIn`).  No `Module k` instance on `ClopenCrossedProduct T k` exists yet.
- `FixedCoreImageHaagerupStatement`, `PeriodTwoCoreUnitImageHaagerupStatement`: this lane, `Dynamics/RankTwoCoreImageHaagerup`
  (probing).

Census keys (ct-sentences ledger): `f31fa0413ffd` `2d5721555dfe` `dd5ef3eafd48` `5e4354e1556b` (the last holds two printed
sentences).  Rows are appended once the carriers land.

## Progress log

- 09-13 16:45: plan; GHW check passed; four modules probing.

## Refutation of V4 residual `CellPocketPinchPosStatement` (ms-cite-1, 09-14 ~00:05)

- `GGT.VanKampen.OsinPocketCellPinchRose.cellPocketPinchRoseRefutation : CellPocketPinchRoseRefutation`, where
  `CellPocketPinchRoseRefutation := ¬ CellPocketPinchPosStatement.{0, 0, 0}` (`Estimating/OsinPocketCellPinchRefutation`,
  on origin at e0a0776bb).  Checked here: `#audit_closed_axioms`, and ms-cite-1's probe 0913-234315-3209 is GREEN on the origin bytes.
  Witness: a four-petal rose on one-letter relators at ε = 1; a cell pocket face set whose first cell has one dart is not simple,
  and O-equivalence keeps word lengths.
- So every endpoint of this lane binding `hcellPinch` at `.{0, 0, 0}` is vacuous: `TorsionFreeResidualsV2Copy` (b05937611),
  `TorsionFreeResidualsV4` (4091f7433) and `TorsionFreeResidualsV4Euler` (236898aed), and the waists `_of_residualsV2Copy`,
  `_of_residualsV4`, `_of_residualsV4Split`, `_of_residualsV4Euler`, `_of_residualsV4EulerSplit` at those universes.
  `_of_residualsV4CopySection` (binder 5 whole) is not affected.
- Census: the 14 W1 rows now cite the `TorsionFreeGreendlingerLeaf.…_of_greendlinger` carriers over the open waist statement and
  record the vacuity; still `partial`.
- Replacement route (ms-cite-1, awaiting assignment): ms-intro-4's `CellPocketPinchSectionStatement` (d3b0769b8), consumed by
  `CellPocketFaceSet.copyRegion_of_pinchSection`, which needs proper arcs on the cell walk.  No producer on origin; it would be a new
  residual, false on monogon relators without `OsinCCondition`, so it needs a model test.  When an additive
  `osinMultipleEdgePocketRegionCopySection_of_pinchSectionOrderEuler` lands, this lane adds a waist and torsion-free variant over it.

## Item 5: the two-threshold waist (ruling R2, coordinator 23:12; names from ct-return-tower and ct-bilateral-cell)

Dependencies on origin: `OsinLemma94ClassCornerMove` (9133128ae, ct-return-tower), `OsinLemma94ClassSectionTwoThreshold`
(34ca875e8) and `OsinLemma94ClassCasesTwoThreshold` (9bae10a9d), ct-bilateral-cell.

Module `GGT/VanKampen/Estimating/OsinGreendlingerWaistV4TwoThreshold`:
`relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV4TwoThreshold`, 8 residuals: `OsinLemma94ClassEndLoopsInput`,
`OsinLemma94SameCellPocketInput`, `OsinLemma94CaseOneRCellStatement`, `OsinLemma94ClassCaseGapSpanStatement`,
`OsinTwoGonHoldsSectionStatement`, `OsinMultipleEdgePocketRegionCopySectionStatement`,
`OsinSectionPocketFaceSetProperSectionStatement`, `PocketPinchLabelledSectionStatement`.
- Lemma 9.4 from `osinLemma94Section_of_classCountTwoThreshold` over `osinLemma94ClassCasesTwoThreshold_of_residuals`, with the
  closed Case 1 face walk and Case 2; `OsinLemma94ClassCaseGapEndpointStatement` leaves the waist.
- Binder 5 whole, so the refuted `CellPocketPinchPosStatement` is not bound.

Module `Manuscript/NonMF/TorsionFreeResidualsV4TwoThreshold`: the 22 endpoints `_of_residualsV4TwoThreshold` over the 8
residuals.  Status: probing (attic c7b171240).  On GREEN the 14 W1 rows add these carriers next to the `_of_greendlinger` ones.

## Item 6: the live waist V5 (coordinator 08:2x, 09-14), authored OFFLINE

The laptop reboot wiped /private/tmp, including the nm infra and this lane's records (`.files`, green records, `landed.log`,
backups).  Origin is intact.  Per main: author offline only; no probe or landing until the infra is rebuilt.  My earlier landings
and the last row state (1507cedb4) are on origin.

Drafts (in the shared tree, not on origin):
- `GGT/VanKampen/Estimating/OsinGreendlingerWaistV5`: `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV5`, 10 residuals:
  `OsinLemma94ClassEndLoopsInput`, `OsinLemma94SameCellPocketInput`, `OsinLemma94CaseOneRCellStatement`,
  `OsinLemma94ClassCaseGapSpanStatement`, `OsinTwoGonHoldsSectionStatement`, `CellPocketWalkEulerStatement`,
  `CellPocketPinchSectionStatement`, `CellPocketWalkProperArcsSectionStatement`, `OsinSectionPocketFaceSetTwoArcSectionStatement`,
  `PocketPinchLabelledSectionTwoArcStatement`.
  - h94 from ct-bilateral-cell's R2 section (34ca875e8, 9bae10a9d), with the closed Case 1 face walk and Case 2.
  - Binder 5 from ms-cite-1's landed `osinMultipleEdgePocketRegionCopySection_of_pinchSectionOrderEuler` (`OsinPocketMultipleEdgeCopyOrderSection`),
    with `hcopy := cellPocketCopyCleanBothOrders` (bd7e16201, closed audit) and `hout := cellPocketWalkOuterOffSideSomeOrder` (7d1f00831).
    The proper-arc residual is model-tested on paper in that module (fails without `OsinCCondition` on one-letter relators; no known
    counterexample under it).
  - Binders 6 and 7 in the walk-order two-arc forms through `osinSectionPocketCutSection_of_residualsTwoArc` (w1-binder-7, f81311dc9).
  - No refuted binder: `CellPocketPinchPosStatement` is not bound.
- `Manuscript/NonMF/TorsionFreeResidualsV5`: the 22 endpoints `_of_residualsV5` over those 10 residuals.
- Earlier drafts kept: `OsinGreendlingerWaistV4TwoThreshold` and `TorsionFreeResidualsV4TwoThreshold` (binder 5 whole, 8 residuals;
  attic c7b171240).  Their probe failed on infrastructure (github fetch), not on Lean.

When probe and land work again: probe V5, land, re-point the 14 W1 rows to the `_of_residualsV5` carriers with this residual list, and
report to main.

LANDED 8c3fc5f4a (probe 0914-082738-17083 GREEN: both modules BUILT on a real rebuild and COMPILED, 0 errors, 23 audits classical, no sorryAx; queued for wiring).  The 14 W1 rows cite the `_of_residualsV5` carriers with the ten live residuals, followed by the `_of_greendlinger` carriers; still `partial`.  The two-threshold drafts (binder 5 whole) stay unlanded.

## Item 7: waist V6 at leaf level (coordinator ~09:00, 09-14)

Module `GGT/VanKampen/Estimating/OsinGreendlingerWaistV6` (additive, over V5):
`relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV6`, plus the section wrappers `OsinTwoGonEulerWalkSectionStatement`,
`OsinTwoGonEulerGapSectionStatement` and `osinTwoGonHoldsSection_of_eulerWalk` (max thresholds over w1-binder-1's
`twoGonHoldsInput_of_eulerWalk`).  Module `Manuscript/NonMF/TorsionFreeResidualsV6`: the 22 endpoints `_of_residualsV6`.

Reductions applied (all on origin): `osinLemma94ClassEndLoopsInput_of_budget` (68b6b0e96), `osinLemma94SameCellPocketInput_of_loopCut`
(bb887b17d), `osinLemma94CaseOneRCell_of_noSpurPockets` with `osinLemma94CaseOneNoSpurXPocket_of_enclosedLoopCutSucc`, its `Y` form and
`osinLemma94CaseOneRCellSpur_of_enclosure` (w1-binder-8), `twoGonHoldsInput_of_eulerWalk` (c109573e3), `cellPocketWalkEuler_of_noninterleaving`
(358515a30), `cellPocketPinchSectionStatement_of_outerPinchStep` (117d5d3c3), `pocketPinchLabelledSectionTwoArcStatement_of_outerPinchStep`
(f81311dc9).  Refutation scan on origin (`¬ X` for every V5 residual and leaf): none.

LEAF residual list (namespace `GGT.VanKampen`, `.{u, w, v}`; `.{v}` for the vertex count) with owner lanes:

| # | leaf | reduces | owner lanes |
|---|---|---|---|
| 1 | `OsinLemma94ClassEndLoopsBudgetInput` | class end loops | ms-binary (ClassJoins), ms-core-1 (boundary-junction budget), ms-compress-1; ms-core-2 paused (LongTransitions `_of_pieces` and bad-junction reduction pending) |
| 2 | `SameCellPocketCellFreeValueStatement` | same-cell pocket values | ms-compress-2, w1-binder-5 |
| 3 | `SameCellPocketLoopCutStatement` | same-cell pocket values | ms-compress-2, w1-binder-5, ms-traces-2 |
| 4 | `EnclosedSubdiagramLoopCutSuccStatement` | Case 1 relator cell (X, Y, spur) | w1-binder-8, ms-traces-2 (Succ); ms-intro-1 paused |
| 5 | `ClosedWalkEnclosedSubdiagramSuccStatement` | Case 1 spur | w1-binder-8, w1-binder-6, ms-traces-2 (Succ) |
| 6 | `OsinLemma94CaseOneSpurEnclosureStatement` | Case 1 spur | w1-binder-8 |
| 7 | `OsinLemma94ClassCaseGapSpanStatement` | class cases (R2) | ct-bilateral-cell, ct-return-tower |
| 8 | `OsinTwoGonEulerWalkSectionStatement` (section form of `TwoGonEulerWalkInput`) | C6′ | w1-binder-1 |
| 9 | `OsinTwoGonEulerGapSectionStatement` (section form of `TwoGonEulerGapInput`) | C6′ | w1-binder-1 |
| 10 | `NoninterleavingVertexCountStatement` | cell walk Euler | ms-inverses-2 (non-interleaving), w1-binder-6; ms-inverses-4 paused |
| 11 | `CellPocketWalkNoninterleavingStatement` | cell walk Euler | ms-inverses-2 (non-interleaving); ms-inverses-4 paused |
| 12 | `CellPocketOuterPinchStepSectionStatement` | section cell pinch | w1-binder-7 |
| 13 | `CellPocketWalkProperArcsSectionStatement` | binder 5 proper arcs | ms-cite-1 (live): the leaf as spelled needs `OsinLemma97Below`, so the chain is `CellPocketWalkProperArcsBelowInput` → binder-5 below variant → `MultipleEdgeCutBelowInput` → induction variant feeding `hbelow`; recompose when the names land |
| 14 | `OsinSectionPocketFaceSetTwoArcSectionStatement` | binder 6 | w1-binder-7, ms-intro-2, ms-inverses-2, w1-binder-6 |
| 15 | `PocketOuterPinchStepSectionStatement` | binder 7 | w1-binder-7, w1-binder-3 |

LANDED 4fcbe5051 (probe 0914-083907-45210 GREEN: both modules BUILT on a real rebuild and COMPILED, 0 errors, 26 audits classical, no sorryAx; queued for wiring).  The 14 W1 rows cite the `_of_residualsV6` carriers with this leaf list, followed by the `_of_greendlinger` carriers; still `partial`.  Recompose as leaves land.

## Item 8: V7, recomposed leaves (coordinator ~09:10 and w1-binder-1, 09-14)

Changes against V6 (additive; V6 stays): leaf 6 closed by `osinLemma94CaseOneSpurEnclosure` (w1-binder-8, c23f6e753, `#audit_closed_axioms`,
no sorry); leaf 11 closed by `cellPocketWalkNoninterleaving` (ms-inverses-2, a1091f0c8, `#audit_closed_axioms`, no sorry); C6′ from
w1-binder-1's `osinTwoGonHoldsSection_of_copyCleanEuler` (9f29a234d), which needs no following cycle and covers pinch-type touches, instead
of my Euler-walk and gap wrappers.  V7 composes over V5 directly.

Modules: `GGT/VanKampen/Estimating/OsinGreendlingerWaistV7` (`relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV7`) and
`Manuscript/NonMF/TorsionFreeResidualsV7` (22 endpoints `_of_residualsV7`).

LEAF residual list of V7 (namespace `GGT.VanKampen`; `.{v}` for the vertex count), with owners:

| # | leaf | owner lanes |
|---|---|---|
| 1 | `OsinLemma94ClassEndLoopsBudgetInput` | ms-binary (ClassJoins), ms-core-1 (boundary-junction budget), ms-compress-1 |
| 2 | `SameCellPocketCellFreeValueStatement` | ms-compress-2, w1-binder-5 |
| 3 | `SameCellPocketLoopCutStatement` | ms-compress-2, w1-binder-5, ms-traces-2 |
| 4 | `EnclosedSubdiagramLoopCutSuccStatement` | w1-binder-8, ms-traces-2 (Succ) |
| 5 | `ClosedWalkEnclosedSubdiagramSuccStatement` | w1-binder-8, w1-binder-6, ms-traces-2 (Succ) |
| 6 | `OsinLemma94ClassCaseGapSpanStatement` | ct-bilateral-cell, ct-return-tower |
| 7 | `OsinTwoGonCopyCleanSectionStatement` | w1-binder-1 (caveat: edge conditions on the given family; outer spurs or shared edges can break them) |
| 8 | `OsinTwoGonDecompositionEulerSectionStatement` | w1-binder-1; intended producer ms-inverses-2's no-interleaving Euler lemma |
| 9 | `NoninterleavingVertexCountStatement` | ms-inverses-2 (non-interleaving), w1-binder-6 |
| 10 | `CellPocketOuterPinchStepSectionStatement` | w1-binder-7 |
| 11 | `CellPocketWalkProperArcsSectionStatement` | ms-cite-1 (live; below chain via `OsinLemma97Below`) |
| 12 | `OsinSectionPocketFaceSetTwoArcSectionStatement` | w1-binder-7, ms-intro-2, ms-inverses-2, w1-binder-6 |
| 13 | `PocketOuterPinchStepSectionStatement` | w1-binder-7, w1-binder-3 |

LANDED 44929efa6 (probe 0914-084716-64911 GREEN: both modules BUILT on a real rebuild and COMPILED, 0 errors, 23 audits classical, no sorryAx; queued for wiring).  The 14 W1 rows cite the `_of_residualsV7` carriers with this leaf list, followed by the `_of_greendlinger` carriers; still `partial`.  Leaf 11 is recomposed over ms-cite-1's below
chain when its names land.

## Item 9: V8 draft (coordinator ~09:00, 09-14), held for leaf 11

Changes against V7 (additive; V7 stays):
- V7 leaf 2 closed by `sameCellPocketCellFreeValue` (w1-binder-5, dc9addc9d, `OsinUnboundSameCellPocketCellFree`, `#audit_closed_axioms`,
  no sorry).  My V7-era scan searched only `GroupApproximation/GGT` with an exact-conclusion match and missed it; scans now cover the whole tree.
- V7 leaf 12 split by `osinSectionPocketFaceSetTwoArcSection_of_proper_of_wholeSection` (2a4d58ae6, `OsinPocketTwoArcSection`) into
  `OsinSectionPocketFaceSetProperSectionStatement` and `OsinSectionPocketFaceSetWholeSectionTwoArcSectionStatement` (only a section spanning
  all of `∂Δ`).  Not pushed further through `OsinSectionPocketFaceSetFirstTurnSectionStatement.toProper`: first-turn order fails on lakes at
  map level (docstring of `OsinPocketPinchOuterDispatch`).

Drafts `GGT/VanKampen/Estimating/OsinGreendlingerWaistV8` (`relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV8`, 13 leaves) and
`Manuscript/NonMF/TorsionFreeResidualsV8` (22 endpoints), attic-saved and probing.  Leaves: `OsinLemma94ClassEndLoopsBudgetInput`,
`SameCellPocketLoopCutStatement`, `EnclosedSubdiagramLoopCutSuccStatement`, `ClosedWalkEnclosedSubdiagramSuccStatement`,
`OsinLemma94ClassCaseGapSpanStatement`, `OsinTwoGonCopyCleanSectionStatement`, `OsinTwoGonDecompositionEulerSectionStatement`,
`NoninterleavingVertexCountStatement`, `CellPocketOuterPinchStepSectionStatement`, `CellPocketWalkProperArcsSectionStatement`,
`OsinSectionPocketFaceSetProperSectionStatement`, `OsinSectionPocketFaceSetWholeSectionTwoArcSectionStatement`,
`PocketOuterPinchStepSectionStatement`.

Held: per main, the next landed variant also recomposes `CellPocketWalkProperArcsSectionStatement` over ms-cite-1's below chain
(`CellPocketWalkProperArcsBelowInput` → binder-5 below variant → `MultipleEdgeCutBelowInput` → induction variant feeding `hbelow`) once
those names arrive.  The 14 W1 rows stay on the V7 carriers (b9ea4161f) until then.

### Item 9 update: V8 rewritten over the below route (09-14 ~09:10)

ms-cite-1's below chain landed (75284d0c0 `OsinAppendixSectionInductionBelow`, 84799a1c5 `OsinPocketMultipleEdgeCopyBelow`), and w1-binder-1
retracted `OsinTwoGonCopyCleanSectionStatement`: four of its clauses are global facts about the optimal diagram (outer spurs, cell–exterior
edges, exterior side darts, region-pair edges) that only surgeries on O-equivalent copies remove, so no producer can derive it on the given
family.  The unlanded V8 draft above is replaced (the earlier bytes are in attic 4c1986a07).

V8 now composes through `relativeGreendlingerQuasiGeodesicLeastArea_of_pocketPartsBelow`:
- binder 5 below the bound, `osinMultipleEdgeCutBelowSection_of_copyPieces` over `osinMultipleEdgePocketRegionCopyBelowSection_of_pinchSectionOrderEuler`,
  with the distinct-cells section pinch from `cellPocketPinchSectionDistinctStatement_of_outerPinchStep` (28caa3d7f) and the below proper arcs;
- C6′ from `osinTwoGonHoldsSection_of_cleanCopyEuler` (7ec4e6fe2);
- the cell-free value proved and the two-arc face set producer split, as above.

LEAF residual list of V8 (namespace `GGT.VanKampen`; `.{v}` for the vertex count), with owners:

| # | leaf | owner lanes |
|---|---|---|
| 1 | `OsinLemma94ClassEndLoopsBudgetInput` | ms-binary (ClassJoins), ms-core-1 (boundary-junction budget), ms-compress-1 |
| 2 | `SameCellPocketLoopCutStatement` | ms-compress-2, w1-binder-5, ms-traces-2 |
| 3 | `EnclosedSubdiagramLoopCutSuccStatement` | w1-binder-8, ms-traces-2 (Succ) |
| 4 | `ClosedWalkEnclosedSubdiagramSuccStatement` | w1-binder-8, w1-binder-6, ms-traces-2 (Succ) |
| 5 | `OsinLemma94ClassCaseGapSpanStatement` | ct-bilateral-cell, ct-return-tower |
| 6 | `OsinTwoGonCleanCopySectionStatement` | w1-binder-1 (compose the closed thickenings; the face-edge doubling step is unowned) |
| 7 | `OsinTwoGonDecompositionEulerSectionStatement` | w1-binder-1; ms-inverses-2's no-interleaving Euler lemma |
| 8 | `NoninterleavingVertexCountStatement` | ms-inverses-2, w1-binder-6 |
| 9 | `CellPocketOuterPinchStepSectionDistinctStatement` | w1-binder-7 |
| 10 | `CellPocketWalkProperArcsBelowSectionStatement` | ms-cite-1 |
| 11 | `OsinSectionPocketFaceSetProperSectionStatement` | w1-binder-6, w1-binder-3 (first-turn route), ms-intro-2 |
| 12 | `OsinSectionPocketFaceSetWholeSectionTwoArcSectionStatement` | ct-return-tower (inner-pocket producer; calibration model 1478083b7) |
| 13 | `PocketOuterPinchStepSectionStatement` | w1-binder-7, w1-binder-3 |

Refutation scan over all 13 on origin (`¬ X`): none.  Pending, not composed: w1-binder-6's `PocketGlueComponentPlanarStatement`
(`OsinPocketGlueComponents`, drafted, not on origin), the leaf of the Euler variants of the pocket cell and outer transports.  The closed
`pocketCellTransport` stays in V8 until those variants land.

### Item 9 update 2: closures folded in (coordinator ~09:12)

- Leaf 8 `NoninterleavingVertexCountStatement` DROPPED: ms-inverses-2's `cellPocketWalkEuler : CellPocketWalkEulerStatement` (0bd28eecc,
  `OsinPocketWalkEulerSectorFree`, `#audit_closed_axioms`, no sorry) replaces `cellPocketWalkEuler_of_noninterleaving hcount …` in binder 5.
  V8 now has TWELVE leaves (the table above minus row 8).
- Checked, no leaf removed: `sectionPocketWalkEuler` and `sectionPocketKeptCell` (0bd28eecc) produce `OsinSectionPocketFaceSetSectionStatement`
  (`osinSectionPocketFaceSetSection_of_euler`, `_of_keptCell`), not the proper form `OsinSectionPocketFaceSetProperSectionStatement` that the
  two-arc split needs; `sectorFreeVertexCount` (68838eeae) feeds `eulers_of_sectorFree` inside the cell walk Euler proof;
  ms-compress-2's `enclosedBridgeDoublingSucc` and `enclosedLeastAreaFilterSucc` (c2fa6eed0) produce `EnclosedLeastAreaFilterSuccStatement`,
  which no producer on origin turns into leaf 3 (`EnclosedSubdiagramLoopCutSuccStatement`) or leaf 4 (`ClosedWalkEnclosedSubdiagramSuccStatement`).
- The previous V8 draft (13 leaves) probed GREEN at 0914-091156-5879; the recomposed 12-leaf V8 LANDED c891e1be3 (probe 0914-091700-833 GREEN: both modules BUILT on a real rebuild and COMPILED, 0 errors, 23 audits classical, no sorryAx; queued for wiring).  The 14 W1 rows cite the `_of_residualsV8` carriers with the twelve leaves, followed by the `_of_greendlinger` carriers; still `partial`.

## Item 10: V9, budget and enclosed pieces pushed down (ms-inverses-2 and origin scan, 09-14 ~09:30)

Changes against V8 (c891e1be3, stays):
- Leaf `OsinTwoGonDecompositionEulerSectionStatement` CLOSED by `osinTwoGonDecompositionEulerSection` (ms-inverses-2, ac902a9c1,
  `OsinAppendixEulerTwoGonDecompositionEuler`, `#audit_closed_axioms`, no sorry).
- Leaf `OsinLemma94ClassEndLoopsBudgetInput` pushed through `osinLemma94ClassEndLoopsBudgetInput_of_joins` (efa471e68), with
  `osinLemma94LongTransitionInput_of_pieces` over the proved `osinLemma94CuttingTransitionInput` (59a5e1718, closed audit, no sorry),
  `osinLemma94BadJunctionInput_of_pieces`, and `osinLemma94BoundaryJunctionBudgetInput_of_pieces` (1bc1874ba).
- Leaf `ClosedWalkEnclosedSubdiagramSuccStatement` CLOSED by `closedWalkEnclosedSubdiagramSucc` (c6ca441fe, `ClosedWalkEnclosedSubdiagramSuccAssembly`,
  `#audit_closed_axioms`, no sorry).

Modules: `GGT/VanKampen/Estimating/OsinGreendlingerWaistV9` (`relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV9`) and
`Manuscript/NonMF/TorsionFreeResidualsV9` (22 endpoints `_of_residualsV9`).

LEAF residual list of V9 (namespace `GGT.VanKampen`), with owners:

| # | leaf | owner lanes |
|---|---|---|
| 1 | `OsinLemma94ContactTransitionInput` | ms-compress-1, ms-intro-2 |
| 2 | `OsinLemma94CellJunctionValueInput` | ms-core-1, ms-inverses-3 |
| 3 | `OsinLemma94BackwardJunctionCountInput` | ms-core-1, ms-inverses-3 |
| 4 | `OsinLemma94BoundaryValueFailureCountInput` | ms-core-1, ms-inverses-3 |
| 5 | `OsinLemma94ClassJoinsEndLoopsInput` | ms-binary |
| 6 | `SameCellPocketLoopCutStatement` | ms-compress-2, w1-binder-5, ms-traces-2 |
| 7 | `EnclosedSubdiagramLoopCutSuccStatement` | w1-binder-8, ms-traces-2 (Succ) |
| 9 | `OsinLemma94ClassCaseGapSpanStatement` | ct-bilateral-cell, ct-return-tower |
| 10 | `OsinTwoGonCleanCopySectionStatement` | w1-binder-1 (face-edge doubling step unowned) |
| 11 | `CellPocketOuterPinchStepSectionDistinctStatement` | w1-binder-7 |
| 12 | `CellPocketWalkProperArcsBelowSectionStatement` | ms-cite-1 |
| 13 | `OsinSectionPocketFaceSetProperSectionStatement` | w1-binder-6, w1-binder-3, ms-intro-2 |
| 14 | `OsinSectionPocketFaceSetWholeSectionTwoArcSectionStatement` | ct-return-tower (respelling via `OsinPocketInnerWalk` pending) |
| 15 | `PocketOuterPinchStepSectionStatement` | w1-binder-7, w1-binder-3 |

Numbering skips 8 (closed).  Refutation scan over all fourteen on origin (`¬ X`): none.  LANDED 07560f516 (probe 0914-100320-24260 GREEN, both modules BUILT and COMPILED, errors section empty; queued for wiring; the first try failed on infrastructure during the ~09:36 outage).

Rows NOT re-pointed to V9 (main's rule, 09-14 ~10:05): against V8, leaves 4 and 7 are closed, but leaf 1 `OsinLemma94ClassEndLoopsBudgetInput` is only reduced to five pieces (contact transitions, cell junction value, backward junction count, boundary value failure count, class joins end loops), and nothing on origin derives any piece from the budget, so no added leaf is shown strictly weaker.  The rows stay on V8 (3c874d98d).  Proposed instead: `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV8Closures` (V8 with only the two closures, ten leaves, none added), probing.

## Item 11: the pure permutation core of `SeamGlueComponentPlanarStatement` (coordinator ~09:40), CLAIMED

Scope, with no maps, over `Fin k` with γ = `finRotate k` and cycle counts `Nat.card (CombMap.Orbit p)` (fixed points included):
1. the non-crossing criterion `card_orbit_add_card_orbit_le`: cyc(π) + cyc(π⁻¹γ) ≤ k + 1;
2. the superposition count `superposition_le`: for π non-crossing for γ and ρ non-crossing for γ⁻¹,
   k + 2·#orbits⟨π, ρ⟩ ≤ cyc(πρ) + cyc(π) + cyc(ρ).
Statements from w1-binder-5 (map side and assembly owner), under agreement before any proof.  Planned modules under
`GGT/VanKampen/`: cycle count change under a transposition, the criterion, and the superposition.  V9 recomposition keeps priority.
