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
`OsinLemma94ClassCaseGapEndpointStatement` and `OsinLemma94ClassCaseGapSpanStatement`.  Status: probing.

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
