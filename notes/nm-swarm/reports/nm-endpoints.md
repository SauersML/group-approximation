# nm-endpoints lane report

Lane `nm-endpoints`, target census2 U7: the closed top endpoints of `sec:torsion-free`
(`thm:torsion-free`, `cor:regular-nonmf-algebra`, the Fournier-Facio paragraph,
`TheoremC.LiteratureInputs`, `lem:saturation`, `thm:hull`, `TheoremC.Configuration`).

## Landed

- `12e1d1af8`: `GroupApproximation/Manuscript/NonMF/TorsionFreeFourLeaves.lean`. It was
  probed green (probe 0913-013032-80446, the bytes on main), and the `#audit_axioms` line
  of each theorem shows only `propext`, `Classical.choice` and `Quot.sound`. It is now
  root-imported (GroupApproximation.lean:4834). The module has 19 theorems
  `*_of_fourLeaves`, each over exactly the walls its proof uses.
  - Greendlinger and bridge walls only:
    - `thm:hull` at Hull's notion, at Osin's notion, at the limit-set notion, and at a
      torsion-free ambient group;
    - `lem:saturation` at the same three notions (the limit-set form uses the closed
      `GGT.OsinClassification.isAcylindricallyHyperbolicOsin_of_limitSet`);
    - `TheoremC.HullCommonQuotientStatement` and `TheoremC.FournierFacioQuotientStatement`.
  - Those two walls plus Kotowski-Ollivier: `TheoremC.LiteratureInputs` and
    `Nonempty TheoremC.Configuration`.
  - All four walls:
    - `TorsionFreePrinted.FournierFacioParagraph`;
    - `PrintedTorsionFreeTheorem`, plus its radical, Osin and limit-set forms;
    - `PrintedRegularNonMFAlgebra`, plus its Osin and limit-set forms.
- `de1ccf8b3` and `5f94c76f9`: docstring-only fixes; no statement changed. Both modules cited
  `thm:hull` at tex lines 1624–1628, and both now cite 1636–1642:
  - `TorsionFreeLimitSetNotion`, two docstrings (reported by sec5-sentences); probe
    0913-020633-75804 green;
  - `TorsionFreeHullPrintedLeastArea`, the module docstring; probe 0913-021058-94913 green.
- `96ebd17c2`: the TorsionFreeKOLeaves decision (section below).
- `fe61152ed`: docstring-only updates to `TorsionFreeLeafAssembly`,
  `TorsionFreeLiteratureInputsLeastArea` and `TorsionFreeSaturationFromCorrected` (reported
  by sec2-sentences), probe 0913-030945-26927 green for all three. They named
  `TheoremCAssembly` declarations that 2c3c8cb40 deleted: `hullOneStep`, `hullTheorem71`,
  `literatureInputs` and the estimating admissions. They now name
  `HullSC.hullOneStepStatement_of_leastAreaLeaves`,
  `TorsionFree.hullTheorem71_of_leastAreaLeaves` and the surviving
  `GGT.VanKampen.Estimating*Statement`s.
- The ten census rows are re-graded at origin 0358f4537 (section "Census rows"). Wall 1 is the
  only residual.
- `93cb4e04f`: `GroupApproximation/GGT/VanKampen/Estimating/OsinPocketMergeRegion.lean`, the
  value half of the zero-cell pocket merge, built with no shelling (section below). Probe
  0913-062000-78681 was green on the bytes of main. The module is root-imported
  (GroupApproximation.lean:4970).
- `decced35e`: `TorsionFreeSectionAssembly` checks `simpleUniqueTraceAtHypEmbedded_closed` with
  `#audit_closed_axioms` instead of `#audit_axioms` (roster item; no statement changed). Probe
  0913-084302-12415 is green and the module is BUILT. It was already root-reachable through
  `TorsionFreeSectionAssemblyClosedGO`, so there is no wire-queue line.
- The ten rows are re-noted at origin a73ab6f78. Row 8097c371f35d now also carries ko-closed's
  `KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed` and `Hyperbolic.sharpExistence_closed`
  (root-imported), as ko-closed asked. The owner note now points to fff-periodic's
  `TorsionFreeGreendlingerLeaf`.
- The ten rows now cite fff-periodic's `TorsionFreeGreendlingerLeaf` forms `*_of_greendlinger`.
  559636b4a root-imported that module (GroupApproximation.lean:4974), and the rows are re-graded
  at origin 3c6b4b505. Each carrier takes `hgreendlinger` alone, so every row stays partial. Row
  8097c371f35d keeps ko-closed's two `_closed` carriers.

- `cf3c78b35` (attic 88587566e): docstring marks on `TorsionFreeLeafAssembly`,
  `TorsionFreeSectionSentences` and `TorsionFreeSectionAssemblyClosedGO`, from systolic-counts'
  flip list (section "Superseded wrappers"). No statement changed. Probe 0913-133143-40961 is
  green and all three modules are BUILT. They were already root-reachable, so there is no
  wire-queue line.

## Zero-cell pocket merge: the value half (lead ruling ~05:00)

This is the shared producer for the R-cell-free pocket of MultipleEdgeCut and of
SectionPocketCut, and for C6. hull-select owns the statement, the FaceSetBoundary on the union,
the merged ContiguityGeometry, `hweight` and the assembly (`Estimating/OsinPocketZeroCellMerge.lean`).
This lane owns the value.
- `PocketRegion.diagram_relatorCells_eq_nil`: a pocket with no relator cell among its faces has
  no relator cell as a diagram (`diagram_rCellCount_le`).
- `PocketRegion.isRelatorProduct_zero_inner`: so its boundary value is a budget-0 relator
  product, moved onto `P.inner.cycle` by `isRelatorProduct_inner_of_diagram`.
- `PocketRegion.listVal_inner_eq_one` and `PocketRegion.listVal_eq_one_of_isRotated`: the word
  on the pocket cycle, and on every cyclic permutation of it, reads `1`.
- `Surgery.InnerGRegion.ofPocketRegion P hcells boundary (hrot : boundary.cycle ~r P.inner.cycle)`
  sets `value_one` from the above, with no `ofShelling`. `ofPocketRegion_faces` and
  `ofPocketRegion_boundary_cycle` hold by `rfl`.
- Interface, agreed with hull-select on 2026-09-13. hull-select's draft
  `Estimating/OsinPocketZeroCellMerge.lean` (landed at a73ab6f78, 08:42) builds
  `PocketRegion.innerBoundary P hcells hwalk` from `hwalk : P.inner.FollowsBoundary`. Its cycle
  is `P.inner.cycle`. `PocketRegion.toInnerGRegion` passes that boundary to `ofPocketRegion`
  with `hrot := List.IsRotated.refl _`, so `OsinPocketMergeRegion` stays as it is. The converse
  bridge (`Embedded.boundaryStep_of_walk`) is hull-select's. This lane drafted the same bridge
  and did not land it.
- Settled by hull-euler (2026-09-13): `EmptyTwoGonInput` (16d923f27) keeps no `FollowsBoundary`
  hypothesis, since route A needs none. A caller of `ofPocketRegion` or `toInnerGRegion` that
  needs `hwalk` builds `P` as `PocketRegion.ofSimpleClosedWalk` and takes `hwalk` from
  `ofSimpleClosedWalk_followsBoundary` (OsinPocketRegionSimpleWalk.lean:87).
  `MultipleEdgePocketRegionInput` (d00f94876) already concludes that both cycles follow the
  boundary, and hull-respell's `PocketRegion.ofSimpleClosedWalk` (a11a8d850, unverified) builds
  such pockets.
- fff-periodic owns route A of `EmptyTwoGonInput` (lead). A pinched pocket has no
  `Embedded.FaceSetBoundary` on `P.faces`, so `ofPocketRegion` does not apply to it.
  - fff-periodic is building `Surgery.InnerDiscRegion`, keyed by `IsDiscRegion`, in new modules
    `SurgeryInnerDiscCollapse*`, and `InnerDiscRegion.ofPocketRegion` in
    `Estimating/OsinPocketDiscMerge`.
  - Its `value_one` is `P.listVal_inner_eq_one hcells` from this lane's module.
  - This lane had no such variant in flight, and it told fff-periodic that hull-select's
    merged-geometry lemmas may overlap.
  - fff-periodic landed route A at 2aa17abb0 (`Estimating/OsinPocketDiscMerge` and
    `Estimating/OsinPocketDiscEmptyTwoGon`).
- This lane offered two lemmas, to be built only if hull-select asks:
  - `P.inner.FollowsBoundary` from an embedded boundary whose cycle rotates the pocket cycle;
  - given `hwalk`, every embedded boundary rotates the pocket cycle
    (`FaceSetBoundary.exists_cycle_eq_rotate`).

## Residual statements (exact, at origin bf7d5994b)

1. OPEN: `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}`. It has
   no closed producer on main.
   - The root-imported `relativeGreendlingerQuasiGeodesicLeastArea_of_pocketParts`
     (Estimating/OsinAppendixGreendlingerPocketParts.lean:131, a452fa727) takes five section
     Props: `OsinLemma94SectionStatement`, `OsinMultipleEdgeCutSectionStatement`,
     `OsinLoopCutSectionStatement`, `OsinPhiPrimeCountSectionStatement` and
     `OsinSectionPocketCutSectionStatement`.
   - The loop slot closes under LoopCut ruling (A) by ghw-charp2's patch 07,
     `osinLoopCutSection : OsinLoopCutSectionStatement`. That patch is not on origin yet
     (patches 01-10 land as one co-probe). This lane then lands
     `relativeGreendlingerQuasiGeodesicLeastArea_of_loopClosed`
     (Estimating/OsinAppendixGreendlingerLoopClosed, drafted, not in the repo) over the other four
     slots.
   - Below, "no producer" means that no theorem on origin concludes the Prop. The binder-free
     producers named below carry `#audit_axioms`, not `#audit_closed_axioms`, unless marked closed.
   - `OsinLemma94SectionStatement` comes from `osinLemma94Section_of_residuals`
     (OsinLemma94SectionResiduals.lean, hull-unbound, 4002b9371, not root-imported). It passes the
     closed pieces to `osinLemma94Section_of_planarPieces` (OsinLemma94PlanarPieces.lean:441,
     root-imported). Only the polygon count and Case 1 stay hypotheses:
     - `OsinLemma94AntiparallelMetricStatement` is closed (`osinLemma94AntiparallelMetric`).
     - `OsinLemma94PolygonRealizationInput` is closed (`osinLemma94PolygonRealizationInput`,
       `#audit_closed_axioms`, 4002b9371). It applies `osinLemma94PolygonRealizationInput_of_pieces`
       to the binder-free respelling surgery, the arcs and ghw-assembly's
       `osinLemma94PolygonPartitionInput`:
       - OsinLemma94PolygonPartition.lean:145, 746028b24;
       - probe 0913-132334-2532 green, `#audit_closed_axioms`, not root-imported.
     - `OsinLemma94PolygonCountInput` comes from `osinLemma94PolygonCountInput_of_sideBudget`
       (OsinLemma94PolygonCount.lean:98), over `OsinLemma94PolygonSideBudgetInput` (no producer;
       hull-count94).
     - `OsinLemma94CaseOneInput`:
       - On origin, `osinLemma94CaseOneInput_of_walk osinLemma94CaseOneWalk`
         (OsinUnboundCaseOneRun.lean:78) takes no open binder.
       - theoremc-retire's `osinLemma94CaseOneInput_of_walk_of_sameCell` (:89, 3292f7a20) also
         takes `OsinLemma94CaseOneSameCellStatement` (OsinUnboundCaseOneFace.lean:466, no
         producer).
       - Patch 10 (f) is overruled, so `_of_walk` is not deleted. After patches 01-10 it gains the
         same-cell binder, and that Prop is not redundant after patch 09 (d).
     - `OsinLemma94CaseTwoInput` is closed by `osinLemma94CaseTwoInput`:
       - OsinLemma94CaseTwo.lean, sec5-sentences, e0e94015d;
       - probe 0913-131149-5355 green, `#audit_closed_axioms`, not root-imported yet.
       - It applies `osinLemma94CaseTwoInput_of_insertion` to sec2-sentences'
         `separatedCornerInsertionInput` (619b70139).
     - Site 5 (patch 10 (d), `alpha_faceOf_not_cell_of_unbound` at j = i): under (A), an unbound
       dart of cell i whose reverse also lies on cell i lies on no polygon walk. The ruling is
       option (a), owned by fff-periodic:
       - `Covers` takes a factor ⌈1/λ⌉ on the sides, and L depends on λ and c. `dense_of_covers`
         absorbs the factor. This is co-probed with hull-count94.
       - fff-periodic proves case (T), where C2 has no relator cell.
       - Case (C) is a named binder of the Covers input, owned by fff-periodic. It can be
         discharged from the threaded `OsinLemma97Below`.
       - So `osinLemma94PolygonCoversInput`, closed on origin, becomes a producer over the case (C)
         binder once the respelling lands.
   - `OsinMultipleEdgeCutSectionStatement` comes from `osinMultipleEdgeCutSection_of_pieces`
     (OsinPocketMultipleEdgeAssembly.lean:207, hull-select, 2db85602c, root-imported). Its leaves have
     no producer: `OsinMultipleEdgePocketRegionSectionStatement` (kh-ejz), `GeodesicCollarStatement`
     (kh-torsion) and `PocketCellTransportStatement` (go-lemma42).
   - `OsinPhiPrimeCountSectionStatement` comes from `osinPhiPrimeCountSection_of_pieces`
     (OsinAppendixEulerSection.lean:62, hull-euler, 6401c70a6, landed unverified, not root-imported).
     - C5 is applied inside by `cellFaceCountInput`.
     - C4 `OsinCornerTwoGonSectionStatement` comes from the binder-free `osinCornerTwoGonSection`:
       - OsinAppendixEulerCornerTwoGonSection.lean, leavitt-units, 0c42391c2;
       - probe 0913-130704-80770 green, not root-imported.
       - It uses `cornerTwoGonInput` (90245333d).
     - The one leaf with no producer is C6′ `OsinTwoGonHoldsSectionStatement` (debt-conditional).
   - `OsinSectionPocketCutSectionStatement` comes from `osinSectionPocketCutSection_of_pieces`
     (OsinPocketPieces.lean:521, root-imported).
     - `PocketRegionOfSimpleStatement` is closed (`pocketRegionOfSimple`).
     - The collar goes through `pocketCollarStatement_of_geodesicCollar` to `GeodesicCollarStatement`.
     - The pinch goes through `pocketPinchLabelledStatement_of_pocketPinchStatement` and
       `pocketPinchStatement_of_pinched` to `PocketPinchPinchedStatement` (kh-cckw).
     - Its leaves with no producer: `OsinSectionPocketFaceSetSectionStatement` (kh-ejz),
       `PocketPinchPinchedStatement`, `GeodesicCollarStatement`, `PocketCellTransportStatement` and
       `PocketOuterTransportStatement` (go-lemma42).
   - The other producers take `OsinLemma97SectionStatement` (`_of_osinLemma97`), the five parts
     of `_of_parts`, or `OsinSection97PocketInputsStatement` (`_of_pocketInputs`).
   - This lane's value half of the zero-cell merge is at 93cb4e04f.
2. CLOSED: `HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}`.
   - It is proved by `HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed`
     (GGT/HullSCLemma51EmbeddedBridgeHolds.lean:20, 18682110d).
   - That proof applies `relativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement_of_letterPullback`
     to `quotientPeripheralLetterPullbackStatement_holds`
     (GGT/HullSCLemma51LetterPullbackHolds.lean:60).
   - Both carry `#audit_closed_axioms`, and both are root-imported (GroupApproximation.lean:4954,
     4955).
   - Its universes `.{0, 0, 0}` match the `hbridge` binder (TorsionFreeFourLeaves.lean:70).
3. CLOSED: `TheoremC.KotowskiOllivierStatement`, which is `Hyperbolic.SharpExistence`.
   - It is proved by `KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed`
     (Kazhdan/KotowskiOllivierClosed.lean:75, f65f99f17). That proof is
     `kotowskiOllivier_of_pinched (Systolic.mirrorFoldPinched CCKW.cosetComplex)`.
   - It carries `#audit_closed_axioms`. The ko-closed probe 0913-055250-45566 was green on those
     bytes, and the root imports it (GroupApproximation.lean:4824).
   - The leaves are:
     - the pinched fold: `Systolic.mirrorFoldPinched` (GGT/SystolicDiscMirrorFold.lean:33);
     - the distinct fold: `Systolic.mirrorFoldDistinct`;
     - the zip: `CCKW.zipSpur_cosetComplex`.
4. CLOSED: `TorsionFreePrinted.FinitelyPresentedInfiniteSimpleStatement`.
   - It is proved by `HydeLodha.finitelyPresentedInfiniteSimple_closed`
     (GroupTheory/HydeLodha/FinitelyPresentedInfiniteSimpleClosed.lean:49, 47b31bef8).
   - It carries `#audit_closed_axioms` and is root-imported (GroupApproximation.lean:4790).

Every other input is already closed: DGO 2.35, GO 1.1, Chiodo, Minasyan–Osin, the
free-product union geometry, and the hard direction of Osin 1.1.

## Superseded wrappers (systolic-counts' flip list, routed by the lead)

systolic-counts listed 86 declarations blocked only by off-route Props, and no counted census row
among them. The Props are `EstimatingUnboundOutputStatement` (refuted at `.{0, 0, 0}`),
`EstimatingSelectionConstructionStatement`,
`GGT.VanKampen.RelativeGreendlingerQuasiGeodesicStatement` and
`HullSC.RelativeGreendlingerStatement`. Sixteen of the declarations are in this lane's modules,
and each gets a docstring mark only, with no statement change and no deletion:
- `TorsionFreeLeafAssembly`, nine declarations:
  - seven name a least-area form with the same conclusion:
    `HullSC.hullLemma49KernelPowerStatement_of_leastAreaGreendlinger`,
    `HullSC.hullOneStepStatement_of_leastAreaLeaves` and five forms in
    `TorsionFreeLeastAreaAssembly`;
  - `relativeGreendlingerQuasiGeodesicSpelling_of_greendlinger` names its least-area counterpart,
    whose conclusion differs;
  - `hullLemma44Canonical_of_leaves` has no least-area form, so its docstring names the nearest,
    `HullSC.torsionFreeHullCanonicalQuotientStatement_of_leastAreaLeaves`.
- `TorsionFreeSectionSentences`, six declarations:
  - three name stronger forms in `TorsionFreeHullPrintedLeastArea`, with no torsion hypothesis;
  - three name the same-conclusion forms in `TorsionFreeSectionSentencesLeastArea`.
- `TorsionFreeSectionAssemblyClosedGO`: `manuscriptRegularNonMFAlgebra_of_leaves_closedCitations`
  names `manuscriptRegularNonMFAlgebra_of_leastAreaLeaves_closedCitations`.
- Both module docstrings now say that `HullSC.RelativeIsoperimetricBridgeQuasiGeodesicStatement` has
  no producer on main, while the embedded bridge is closed.

The other items on the list are in modules this lane does not own:
- `HullSCLemma49PowerDiagramFromComponents` and `HullSCLemma44Canonical` belong to sec2-sentences.
- `HullSCOneStepQuasiGeodesicLeaves` belongs to hull-respell.
- The lead's rulings draft (~13:40) gives baseline-debt the rest. It also gives baseline-debt the
  stale docstring at `Estimating/Assembly.lean:818` ("Still open, and not addressed here").

systolic-counts landed the list at 20d0ec06d (`notes/nm-swarm/reports/systolic-counts.md`). Its
check on 0183c4b57 covers all 49 flip pairs, since `TorsionFreeLeafAssembly` :173 has two targets.
- Each target is root-reachable and not `sorry`-tainted.
- Each requirement a target names is discharged under the least-area statement.
- BLC:123, the nearest form named at :103, passes the same check.
- The second target of :173 is `TheoremC.manuscriptTorsionFreeFullMFRadical_of_leastAreaInputs`, a
  theoremc-retire form. The docstring names only `TorsionFreeLeastAreaAssembly`'s form.

## Flips (ownership final, roster ~06:36)

This lane re-grades the rows as walls close and lands no flip. The final roster splits the flips:
- theoremc-retire: every `TheoremC*` module and the `_of_leastAreaInputs` forms;
- fff-periodic: `TorsionFreeFourLeaves` and `SectionSentencesFourLeaves`;
- ko-closed: the carrier swap of row 8097c371f35d;
- hull-bridge: this lane's five endpoint modules, with 27 findings. They are
  `TorsionFreeLeastAreaAssembly`, `TorsionFreeOsinNotion`, `TorsionFreeHullPrintedLeastArea`,
  `TorsionFreeLimitSetEndpoints` and `TorsionFreeSectionAssembly`.

fff-periodic's `TorsionFreeGreendlingerLeaf` (1edf0f7b4, probe 0913-063820-983 green) states 23
forms `*_of_greendlinger` over hgreendlinger alone. 559636b4a root-imported it
(GroupApproximation.lean:4974), so the rows now cite it. Each form applies its four-leaf form to
the closed producers its proof uses. Each flip is
`theorem printedFoo : PrintedFoo := TorsionFreeGreendlingerLeaf.printedFoo_of_greendlinger <W1>`,
followed by `#audit_closed_axioms`, where `<W1>` is a closed producer of wall 1.
- Walls 2 to 4 are closed, so every flip now waits on wall 1 alone. Each form applies:
  - the bridge producer only: `thm:hull`, `lem:saturation`, `HullCommonQuotientStatement`,
    `FournierFacioQuotientStatement`;
  - the bridge and Kotowski-Ollivier producers: `LiteratureInputs` and `Configuration` (row
    dab2f2bfe084);
  - all three producers: `FournierFacioParagraph`, `thm:torsion-free`,
    `cor:regular-nonmf-algebra`.
- `hKO` is `KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed`.
- This lane lands no reduced-leaf wrapper, since reshaping a binder retires no finding.

## Census rows

`metadata/nm-census-rows/nm-endpoints.tsv` is keyed by sentence hash.
- Every row is `partial` and names its exact residual premises and the closed ones.
- The rows are:
  - a16637da7249: the torsion-free clause of the abstract;
  - 0f22bdbc4184: thm:torsion-free;
  - dce7a9ff4e83: the sentence at tex 293;
  - 7b1fa3182135 and 8b1ec28a0e73: cor:regular-nonmf-algebra;
  - 4895f03fdf5f and 8aead549f1fe: thm:hull;
  - 2f55113239ce: lem:saturation;
  - 8097c371f35d: the Fournier-Facio sentence;
  - dab2f2bfe084: the G_0 sentence.
- None of them retires a baseline finding: each carrier still takes `hgreendlinger`.
- No row was added for the proof-step rows bcc99703f838, 2d1cd22e5f49, 2f997e5af4e6 and
  721da4c14d11, because no four-leaf theorem proves those sentences exactly.
- The merged census unions the carriers of every lane's row on a hash:
  - 4895f03fdf5f and 8aead549f1fe also carry fff-quotient's `LINE:1636` row, the Hyde–Lodha
    `Q₂` witness for `FinitelyPresentedInfiniteSimpleStatement`. Line 1636 is the `thm:hull`
    header, so that key looks misplaced.
  - 8097c371f35d also carries hl-lemma46's row.
  - dab2f2bfe084 also carries cite-hull's row.
  - All ten hashes also carry fff-periodic's rows. They cite the same `*_of_greendlinger`
    carriers and record the four-leaf forms these supersede.
- hull-bridge's `TorsionFreeGreendlingerForms` (99db3338a, root-imported at 559636b4a,
  GroupApproximation.lean:4989) gives 17 more endpoints over hgreendlinger alone, built on this
  lane's five least-area modules. No row of this lane names it. The lead checked that it does not collide with `TorsionFreeGreendlingerLeaf`.
  - The two modules use separate namespaces, and both stay.
  - Four `_of_greendlinger` names occur in both, which is harmless across namespaces:
    hullCommonQuotient, literatureInputs, fournierFacioParagraph and
    hullSmallCancellationTorsionFreePrinted.
  - hull-bridge gave census the mapping for its 54 baseline lines.

## Wall status on main (checked 2026-09-13 at origin 0358f4537, wiring rechecked at 3c6b4b505)

- Walls 2, 3 and 4 are closed (above).
- theoremc-retire's `TheoremCAssemblyFoldLeaf` states Theorem C over hgreendlinger, hbridge and
  hfold. The root imports it (GroupApproximation.lean:4961).
- Its `TheoremCAssemblyGreendlingerLeaf` (c5f953323, root-imported, GroupApproximation.lean:4969)
  states Theorem C over hgreendlinger alone, per its wire-queue entry:
  `manuscriptTorsionFreeFullMFRadical_of_greendlinger` and
  `manuscriptTorsionFreeSimplified_of_greendlinger`.
- Wall 1 has no closed producer. No closed producer of `OsinLemma97SectionStatement` has
  landed.
- `HullCitationSentences.printedHullTheorem312*` and `printedSaturationHullPair`, and
  `HullTheorem312Lemma58.printedHullTheorem312`, are closed and root-imported. They carry tex
  1629–1630 and 1662 (Hull Theorem 3.12, Corollary 5.7, Lemma 5.8). They are not `thm:hull` and
  not the statement of `lem:saturation`, so no row of this lane changes.

## TorsionFreeKOLeaves: unwired orphan, no deletion (agreed with the lead)

- Leave `Manuscript/NonMF/TorsionFreeKOLeaves.lean` unchanged on main (blob 4c6a119ae). Do not
  probe it and do not queue it for wiring.
- Each of its seven forms is the matching `TorsionFreeFourLeaves.*_of_fourLeaves` form with
  `hKO := KMSGroup.sharpExistence_ghb7_of_fixedCliqueHyp hT6 hhyp`
  (Kazhdan/GHBSharpExistenceSystolic.lean:47). The flip never needs it, and wiring it would
  add seven open-predicate findings to the baseline and retire none.
- Its two `cor:regular-nonmf-algebra` forms still take `hDGO` and `hGO`, but both citations are
  already proved: `TorsionFreeSectionAssembly.simpleUniqueTraceAtHypEmbedded_closed` and
  `TorsionFreePrinted.gerasimovaOsinTheorem11Printed`.

## Open-predicate findings over the least-area leaves (classification)

These findings are blocked only by wall 1. Each retires when its flip lands: the
row names the closed endpoint and says "retires open-predicate <decl>".
- The census note names the Greendlinger and bridge walls (baseline lines 214–289):
  - `TorsionFreeLeastAreaAssembly.manuscriptTorsionFreeTheorem_of_leastAreaLeaves`,
    `manuscriptRegularNonMFAlgebra_of_leastAreaLeaves`,
    `printedSaturationNoOmega_of_leastAreaLeaves`;
  - `TorsionFreeOsinNotion.manuscriptTorsionFreeTheoremOsin_of_leastAreaLeaves`,
    `manuscriptRegularNonMFAlgebraOsin_of_leastAreaLeaves`,
    `manuscriptSaturationOsin_of_leastAreaLeaves`;
  - `TorsionFreeHullPrintedLeastArea.manuscriptSentence_hullTheorem_of_leastAreaLeaves`,
    `manuscriptSentence_hullTheoremOsin_of_leastAreaLeaves`;
  - `TorsionFreeLimitSetEndpoints.manuscriptHullTheoremLimitSet_of_leastAreaLeaves`,
    `manuscriptSaturationLimitSet_of_leastAreaLeaves`;
  - `GGT.RelHyp.fournierFacioQuotientStatement_of_leastAreaLeaves`;
  - `TorsionFreeLiteratureInputsLeastArea.literatureInputs_of_leastAreaLeaves`. Its binders
    also include the Kotowski-Ollivier wall, which the census note does not name.
- The census note names the Hyde–Lodha wall, but the routes consume all four walls (baseline
  lines 220–307):
  - `TorsionFreeLiteratureInputsLeastArea.manuscriptTorsionFreeTheorem_of_hullLeaves`,
    `manuscriptTorsionFreeTheoremOsin_of_hullLeaves`, `manuscriptRegularNonMFAlgebra_of_hullLeaves`,
    `manuscriptRegularNonMFAlgebraOsin_of_hullLeaves`, `fournierFacioParagraph_of_leastAreaLeaves`;
  - `TorsionFreeSectionAssembly.manuscriptRegularNonMFAlgebra_of_hullLeaves_closedGO`, plus its
    Osin and limit-set forms.
- Not this lane (ROSTER):
  - sec5-sentences owns the proof-step carriers
    `TorsionFreeHullParagraphGeneral.*_of_leastAreaLeaves` (row bcc99703f838) and
    `TorsionFreeSectionSentencesLeastArea.*_of_leastAreaLeaves` (rows 2d1cd22e5f49,
    2f997e5af4e6, 721da4c14d11), with their own four-leaf forms;
  - hull-respell, hull-bridge and sec5-sentences own `GGT.RelHyp.osin24HullStep_of_boundedLeaves`.

## Next

- The value half of the zero-cell merge is on main and green, and `hrot` is agreed with
  hull-select (section above). The two offered lemmas get built only if hull-select asks.
- The ten rows cite `TorsionFreeGreendlingerLeaf` (root-imported at 559636b4a). Once wall 1 has a
  closed producer, re-grade them onto the closed flips, which fff-periodic owns.
- `OsinDescentStepInput` is RETIRED as off route (lead, 2026-09-13; audit-sec5 and
  dgo-analytic agree). This lane built nothing on it and deleted nothing. dgo-analytic adds the
  docstring note.
- LoopCut is ruled (A), final: `RespectsSections` gains `target ≠ some source` as its first
  conjunct. ghw-charp2 lands patches 01-10 as one co-probe, and this lane holds every
  `LoopCutInput` edit and runs no probe until then. When patch 07's `osinLoopCutSection` is on
  origin:
  - land `Estimating/OsinAppendixGreendlingerLoopClosed` (unverified), probe it, land it plain
    after green, and queue it for wiring;
  - re-grade the ten rows (hgreendlinger stays residual, over the four slots above), and update
    their residual notes.
- Meanwhile, keep the ten rows current. Wall 1 (`hgreendlinger`) is their only residual.
- A closed `LiteratureInputs` needs its own namespace, because `TheoremC.literatureInputs` was
  the name of the deleted admission.
- Row f2bf6328169e (tex 1725, the DGO and GO sentence) belongs to cite-osin, which grades it
  formalized. census2 U3 lists it as a stale re-grade. It is not this lane's row.
