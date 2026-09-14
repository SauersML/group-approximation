# w1-binder-1

This lane is a wave-2 lane from session `nonsofic-existence-49`. It is an independent second start on `OsinLemma94ClassCountInput`, binder 1 of the post-(A) W1 waist (`Estimating/OsinLemma94PolygonClasses.lean:360`).

## CLAIM

CLAIM cutting-side count GroupApproximation/GGT/VanKampen/Estimating/OsinLemma94CuttingSides.lean

- **Piece.** The cutting half of Osin (38), "`k_i ≤ 4 n_i`", at side level, per polygon of `OsinLemma94RealizedPolygons S`. Assume `S.DartMinimal` and `P.Maximal`. For a polygon `k`, let an entry be a cutting side whose cyclic predecessor is not cutting. Then

  `#{cutting sides of k} ≤ 4 · #{entries of k} + 1`.

  Each entry ends a non-cutting class, so the count pays the cutting classes of `ClassBudget` with `K = 5(29 + 24ε) + 29`, as in audit-intro's budget check.
- **Why unowned.**
  - Roster l.1239 gives "the forest lemma" to audit-intro.
  - But audit-intro's report (f720ed401, 16:17) says "No lane owns it", and the lane is waiting for a sub-piece.
  - No such module exists on origin, on disk or in any `lanes/*.files`.
  - If audit-intro has started, main relays and this lane takes another leaf.
- **Consumers.**
  - hull-count94's `ClassCountInput` assembly (the cutting classes of `ClassBudget`).
  - sec5-sentences' `OsinLemma94LongTransitionInput` (transitions at cutting sides).

## Route (walk level, one planarity input)

- **Notation.** `F` is the set of darts `d` of the walk of `face k` with `alpha d` also on that walk. By `cell_arc`, `boundary_arc` and `short_region`, these are exactly the darts of the cutting sides.
- **I2 (walk only).** A vertex of valence two with one dart in `F` has both edges in `F`.
- **I3.** No valence-one vertex carries an `F` dart. This is `not_leaf_of_dartMinimal` over the closed `pendantPathRemovalInput`.
- **I4 (rotation counting).**
  - An attachment vertex has an `F` edge and a non-`F` edge. It has at most `m_F − 1` corners between two `F` darts.
  - A vertex whose edges are all in `F` has `m_F` such corners.
- **I5 (walk accounting).**
  - Every cutting side after a cutting side, except at the base, starts at a corner between two `F` darts at a vertex of valence at least three (`Maximal`).
  - Every attachment vertex has an entry.
- **I1 (the one planarity input).** The `F` edges form a forest, so `#E_F ≤ #V_F − 1`. This comes from simple closed walks having different faces across.
- **Handshake.** `Σ (m_F − 2) = 2#E_F − 2#V_F ≤ −2`.
  - So `#branch ≤ #attachment − 2`.
  - So #turn corners `≤ 3·#attachment − 6`.
  - So `#cutting ≤ #entries + #turns + 1 ≤ 4·#entries + 1`.

## Modules (LANDED; queued for wiring)

- Statements c22052062 (probe 0913-175651-60438, COMPILED). Count ca497ee7a (probe 0913-180018-76961 GREEN, BUILT; audits are only propext, Classical.choice and Quot.sound).
- `OsinLemma94CuttingSidesStatement` is PROVED over `SameFaceDartForestStatement` alone: `osinLemma94CuttingSides_of_forest`.

- `Estimating/OsinLemma94CuttingSides.lean` (statements):
  - `CombMap.sameFaceDarts f`: the darts with `f` on both sides. `CombMap.sameFaceVertices f`: the vertices they start at.
  - `SameFaceDartForestStatement`: planar `M`, a nonempty `sameFaceDarts f` ⇒ `#sameFaceDarts f + 2 ≤ 2·#sameFaceVertices f`.
  - `OsinLemma94RealizedPolygons.cuttingSides`, `cuttingEntries` (with `mem_` lemmas).
  - `OsinLemma94CuttingSidesStatement`: `#cuttingSides k ≤ 4·#cuttingEntries k + 1` under `DartMinimal` and `Maximal`.
- `Estimating/OsinLemma94CuttingSidesCount.lean` (proof over the forest Prop):
  - `CombMap.sameFaceStarts`, `sameFaceTurns`: darts of `F` whose vertex predecessor is off `F`, or in `F` and different from the successor.
  - `card_filter_turns_add_six_le`: per vertex, `turns + 6 ≤ 3·F + 3·starts`, when no `F` dart is fixed by `sigma`.
  - `card_sameFaceTurns_add_six_le`: summed, with the forest Prop, `turns + 6 ≤ 3·starts`.
  - `range_flatMap_eq_split`, `walk_isChain`, `exists_facePerm_eq_of_not_head`, `facePerm_getLast_eq_head`: walk adjacency.
  - `continuationSides`; `card_cuttingSides_le`; endpoint `osinLemma94CuttingSides_of_forest : SameFaceDartForestStatement → OsinLemma94CuttingSidesStatement`.
  - The route needs no wrap-around adjacency: side `0` is paid by the `+1` twice, and the bound comes out as `4e − 2`.

## CLAIM 2 (main approved 18:1x)

CLAIM cutting-class bridge GroupApproximation/GGT/VanKampen/Estimating/OsinLemma94CuttingClasses.lean

- Statement: for every `Q : OsinLemma94ClassPolygons P`, `#cuttingClasses k ≤ 4·#otherClasses k + 1`, under `DartMinimal` and `Maximal`, over the forest Prop.
- Covered by nothing: `OsinLemma94ClassJoins`/`ClassJunctions` (hull-count94.files) are absent on disk and on origin, audit-intro holds no forest draft, and no `cuttingClasses` declaration exists anywhere.
- Route: cutting classes inject into cutting sides by their first side. Entries inject into other classes, since the side before an entry ends its class (`mem_getLast?_of_next_kind_ne`, over `CyclicRuns.isChain_rotate_range`).

## Residual Props

- `SameFaceDartForestStatement`. ms-compress-4 proposed to prove it in `CombMapSameFaceForest.lean`, by leaf induction with `simpleClosedWalkSides`. Once it lands, this lane imports that module and deletes its copies.

## Progress log

- 16:5x: claim landed.
- 17:19: the lead restarted. Resumed at 17:21; nothing was lost.
- 17:2x: the first attic landing was refused (`NM_ATTIC` flag missing), and the first probe failed on fetch contention (infra).
- 17:3x: statement module v2 and the counting module written; attic landing and probe of both launched.
- 17:51 probe: 3 missing `DecidablePred` instances (`open Classical in` on the `mem_` lemmas), fixed.
- 17:56 probe: statements COMPILED and landed c22052062. The count failed on one name (`Embedded.isChain_rotate_of_isChain_closes`); fixed.
- 18:00 probe GREEN: count landed ca497ee7a. Both modules appended to the wire queue.
- 18:07: ms-compress-4 landed `CombMapSameFaceForest` (0003dced5), which carries the same four declarations (spelling v2).
- 18:12 co-probe 0913-181230-23379 GREEN: CuttingSides, CuttingSidesCount and CuttingClasses all BUILT. Landed at 3d2744463:
  - `OsinLemma94CuttingSides` now imports `CombMapSameFaceForest` and no longer restates `sameFaceDarts`, `mem_sameFaceDarts`, `sameFaceVertices` or `SameFaceDartForestStatement`. Origin has one definition of each.
  - `OsinLemma94CuttingClasses` (new): `cuttingClasses`, `otherClasses`, `exists_class_of_side`, `classSides_disjoint`, `mem_getLast?_of_next_kind_ne`, `card_cuttingClasses_le`, `card_cuttingEntries_le`, `card_cuttingClasses_le_otherClasses`, `OsinLemma94CuttingClassesStatement`, `osinLemma94CuttingClasses_of_forest`.
  - Both are on the wire queue, and wiring pulls in `CombMapSameFaceForest`.
- 18:13: ms-compress-4 proved `sameFaceDartForest : SameFaceDartForestStatement` at b18944a24. The commit only adds declarations; the four shared names are unchanged.
- 18:16 probe 0913-181649-59275 GREEN. `OsinLemma94CuttingClassesClosed` landed at 308984747:
  - `OsinLemma94RealizedPolygons.card_cuttingSides_le_of_dartMinimal (hS) P (hmax) k : #cuttingSides k ≤ 4·#cuttingEntries k + 1`;
  - `OsinLemma94ClassPolygons.card_cuttingClasses_le_of_dartMinimal (hS) (hmax) Q k : #cuttingClasses k ≤ 4·#otherClasses k + 1`;
  - `osinLemma94CuttingSides_closed : OsinLemma94CuttingSidesStatement` and `osinLemma94CuttingClasses_closed : OsinLemma94CuttingClassesStatement`, each with `#audit_closed_axioms`.
  - All four axiom lists are propext, Classical.choice, Quot.sound; the log has no sorryAx. The module is on the wire queue.

## CLAIM 3 (main ~18:30: binder 4, C6′, producers behind `hno` and `havoid`)

CLAIM L4 + L5a two-gon class and walk hypotheses GroupApproximation/GGT/VanKampen/Estimating/OsinAppendixEulerTwoGonClassHyp.lean

- L4: a producer of `TwoGonClassHyp family E x a b i` for the face class of a two-gon of `phiMapO` with no corner in its gap, from `exists_twoGonLabels`, `exists_outer_of_isTwoGon`, `ExtPhiData.faceOf_of_faceClassO_twoGon` and `phiRegionO_of_faceOf_eq` (debt-conditional, landed).
- L5a: the fields `left_side`, `right_side` and `base` of `TwoGonWalkHyp` on the decomposition walk `source.reverseDarts ++ a.rightSide ++ target.darts ++ b.leftSide`.
- Split sent to w1-binder-4 (one message, ~18:35):
  - w1-binder-4 keeps `connected` (its `BoundaryCycleFaceClass` draft), `outer_off`, `cell_off`, the `TwoGonWalkHyp` assembly and the C6′ assemblies.
  - ms-inverses-2 has L1a. ms-torsionfree's inner builder is landed at 2d0b61555.
- Ownership check: debt-conditional has no unlanded drafts, no producer of either structure exists on origin or in the tree, and w1-binder-4's `ClassWalkHyp` file is absent.
- The non-cutting item (other-class count) was cancelled by main: ct-bilateral-cell holds it.
- w1-binder-4 agreed (~18:36). It landed L5b at 20767e008 (`twoGonWalkHyp_of_innerFollows`), which takes `hleft`, `hright` and `hbase` verbatim.
- 18:41 probe RED on two rewrites: the embedding's coercion type under `instances` transparency, and the `cross` ite at side `false`. Both fixed with `congrArg` and type ascriptions.
- 18:57 probe 0913-185733-69734 GREEN, BUILT; all six declarations are [propext, Classical.choice, Quot.sound], and the log has no sorryAx. `Estimating/OsinAppendixEulerTwoGonClassHyp` LANDED at 47f5dcb22 and is on the wire queue:
  - `RegionCandidate.faceClassO_facePerm y : FaceClassO family E y.1 ((phiMapO family E).facePerm y).1`;
  - `RegionCandidate.twoGonClassHyp_of_outer P hlinked hclosed hnondeg hcell hy hyf hnone h4 hb : TwoGonClassHyp family E y.1 (phiRegionO y) (phiRegionO (facePerm² y)) (phiRegionO y).2.source`;
  - `RegionCandidate.twoGonClassHyp_of_linkedComponent S P hcell hy hyf hnone h4 hb`, at `E = linkedComponentO S.family a₀`, with the hypotheses on `y` given by `exists_twoGonLabels`;
  - `RegionCandidate.twoGonWalk_left_side source target ht hsrc htgt`, `twoGonWalk_right_side …` and `twoGonWalk_base source target ht hnondeg htgt`, on `source.reverseDarts ++ a.rightSide ++ target.darts ++ b.leftSide`, with `hsrc : ∀ d ∈ a.sourceArc.darts, d ∈ source.darts` and `htgt : ∀ d ∈ a.targetArc.darts, d ∈ target.darts` (and the same for `b`).

## CLAIM 4 (main ~19:05: binder 4, span inclusions and L2, the following clause on the copy walk)

CLAIM span inclusions GroupApproximation/GGT/VanKampen/Estimating/OsinAppendixEulerTwoGonSpans.lean
CLAIM L2 model test (mixed touch) GroupApproximation/GGT/VanKampen/Estimating/OsinPocketMixedTouchModel.lean

- Span inclusions: `twoGonSource_left/right` from the gap equation `source.darts = a.sourceArc.darts ++ gap ++ b.sourceArc.darts` (`CyclicArc.exists_spanArc`). `twoGonTarget_left` from the start equality and a length bound, `twoGonTarget_right` from the end equality without wrap. Both go through the carrier-transport lemmas `mem_darts_of_start_eq_of_eq_none` and `mem_darts_of_le_of_eq_none`. They discharge the four inclusion clauses of w1-binder-4's `TwoGonInnerFollowsWalkInput`.
- L2 model test. At a touch vertex with two passes, a noncrossing walk turns either lake-type (inner follows there, outer fails; Configuration B) or pinch-type (the reverse; Configuration A). A walk with one touch of each type has neither cycle following. The model is a circle with an outside bubble at one vertex and an inside loop at the other (8 darts, 2 vertices, 4 faces, walk `[0,6,2,4]`). So "outer ∨ inner follows" is not provable from noncrossing alone, for `TwoGonEitherFollowsCopyInput` and for ms-inverses-2's `CellPocketWalkEitherFollowsStatement`. A producer must exclude mixed touches from the pocket geometry, or split the walk at a touch.
- LANDED spans at 4b7ff30b3: `Estimating/OsinAppendixEulerTwoGonSpans`, probe 0913-191558-63004 GREEN, BUILT; on the wire queue. Declarations: `mem_darts_of_start_eq_of_eq_none`, `mem_darts_of_le_of_eq_none`, `twoGonSource_left/right`, `twoGonTarget_left/right`. They give clauses 2–5 of w1-binder-4's `TwoGonInnerFollowsWalkInput` (35e17a915).
- LANDED model at 8c6883be3: `Estimating/OsinPocketMixedTouchModel`, probe 0913-192847-50147 GREEN, BUILT on the first try; the five `#audit_closed_axioms` show [propext, Classical.choice, Quot.sound], no sorryAx; on the wire queue. Endpoint: `noncrossingMixedTouchModel : NoncrossingMixedTouchModel`, a planar map with a noncrossing closed walk neither of whose boundary cycles follows.
- L2 as stated needs a ruling from main: the disjunction is false at map level. The candidate routes, split at a touch or exclude mixed touches geometrically, went to main.
- Main ruled ~19:40: route (c), Euler equalities (w1-binder-6's `PocketRegion.ofNoncrossingClosedWalkEuler`, 2c1a841e8; ms-inverses-2 owns the generic lemma), with (a) as fallback.
- Euler verdict on the mixed model, by hand against `reclosedMap`, not built: both reclosings keep χ = 2.
  - Side reclosing: vertex orbits {0,5}, {1,6,7,2}, {3,4}; E' = 4; F' = 3.
  - Outside reclosing: {0,5,4,3}, {1,6}, {2,7}; E' = 4; F' = 3.
  - So route (c) holds on the mixed touch.
- Hazard: `TwoGonWalkHyp.connected` fails at pinch-type touches (walk darts 0 and 4 of 8c6883be3 lie on different faces with every edge on the walk). The Euler route therefore needs `hno`/`havoid` without `connected`: per walk dart, the face is a pocket face. Plan: (i) `TwoGonEulerWalkInput`, (ii) the per-dart pocket-face variant, (iii) `twoGonHoldsInput_of_eulerWalk`.
- LANDED (i) at eeddf1c9e: `Estimating/OsinAppendixEulerTwoGonEulerWalk`, probe 0913-194656-56158 GREEN, BUILT; audits [propext, Classical.choice, Quot.sound], no sorryAx; on the wire queue.
  - `TwoGonEulerWalkInput`: `TwoGonInnerFollowsWalkInput` with clause 1 replaced by the Euler pair, spelled as the `hinner`/`houter` of `PocketRegion.ofNoncrossingClosedWalkEuler`. ms-inverses-2 agreed to the spelling.
  - `twoGonEulerWalkInput_of_innerFollowsWalk`: the Euler form is weaker, via `eulers_of_eitherFollows`.
- ms-inverses-2 (~19:50): its generic Euler lemma (`NoncrossingClosedWalkEulerNoninterleaving`, unlanded) needs a named no-interleaving hypothesis beyond `IsNoncrossingClosedWalk` and planarity.
  - Counterexample from hull-euler's docstring: the rose with sigma 1↦0↦3↦2↦5↦4↦1 and walk `[0,2,4]` is noncrossing, but reclosing its side gives a torus.
  - So clause 1 of `TwoGonEulerWalkInput` will be discharged by that lemma plus a no-interleaving Prop for pocket walks; sec2-sentences has a hand argument from the joint structure.

## CLAIM 5 (main 20:15: (ii) the pocket faces without `connected`, then (iii) the Euler assembly)

CLAIM pocket faces without connected GroupApproximation/GGT/VanKampen/Estimating/OsinAppendixEulerTwoGonPocketFacesEuler.lean
CLAIM Euler C6′ assembly GroupApproximation/GGT/VanKampen/Estimating/OsinAppendixEulerTwoGonEulerAssembly.lean

- (ii) `TwoGonWalkSideHyp` (the side, outer and cell fields). debt-conditional's transport restated over it, `hno`/`havoid` from a per-walk-dart base, and the base on the decomposition walk for every dart outside the span gaps.
- (iii) `twoGonHoldsInput_of_eulerWalk`, over `TwoGonEulerWalkInput` and a named residual for the span-gap darts. Route: `PocketRegion.ofNoncrossingClosedWalkEuler` → `InnerDiscRegion.ofPocketRegion` → `false_of_mergeDisc`.
- 20:26 resume check after the outage: no records lost, nothing to re-probe, eeddf1c9e on main.
- LANDED (ii) at 55f2bec39: `Estimating/OsinAppendixEulerTwoGonPocketFacesEuler`, probe 0913-203340-29734 GREEN, BUILT on the first try; all seven audits [propext, Classical.choice, Quot.sound], no sorryAx; on the wire queue.
  - `TwoGonWalkSideHyp`, `TwoGonWalkHyp.toSideHyp`.
  - `ExtPhiData.twoGonPocketFace_alpha_of_sideHyp`, `_iff_of_eqvGen_of_sideHyp`, `_of_mem_sideFaces_of_base`.
  - `ExtPhiData.cell_face_not_mem_sideFaces_of_twoGon_of_base` (`hno`) and `ExtPhiData.disjoint_sideFaces_of_twoGon_of_base` (`havoid`).
  - `twoGonPocketFace_of_mem_decomposition` and its six side and arc helpers.
- LANDED (iii) at c109573e3: `Estimating/OsinAppendixEulerTwoGonEulerAssembly`, probe 0913-203855-77139 GREEN, BUILT on the first try; audits clean; on the wire queue.
  - `twoGonHoldsInput_of_eulerWalk : TwoGonEulerWalkInput → TwoGonEulerGapInput → TwoGonHoldsInput`.
  - Route: `PocketRegion.ofNoncrossingClosedWalkEuler` → `Surgery.InnerDiscRegion.ofPocketRegion` → `false_of_mergeDisc`, with `hno`/`havoid` from (ii).
  - It needs neither a following cycle nor `connected`, so it covers Configuration A and mixed touches.
- 21:26 resume check after the session limit: probe 13 green, nothing lost, (iii)'s bytes match the attic copy 53963b72a.

## CLAIM 6 (main 23:12: the producer of `TwoGonEulerGapInput`)

CLAIM two-gon gap faces GroupApproximation/GGT/VanKampen/Estimating/OsinAppendixEulerTwoGonGapFaces.lean

- Step 1, the model test. Check the non-retention claim against the definitions: from the first cell dart of `a`, the rotation of `phiMapO` at cell `i` returns first to the first cell dart of `b`, and the darts in between are exactly `a`'s later source darts and the gap. Do the same at the outer vertex.
- Step 2: the class chain along both gaps, then `twoGonPocketFace_of_faceClassO`.
- Model-test verdict (step 1): the claim holds. This was derived against the definitions, not built as a separate Lean model; the proof below is the check.
  - `CombMap.dual.sigma := M.facePerm`, so `phiMapO`'s rotation is the first return of the collapsed face permutation.
  - At `O`: hull-euler's `exists_sigma_eq_of_twoGon` and `outer_collapsed_facePerm_pow` walk from `b`'s crossing back along `∂Δ` to `a`'s crossing, and no dart in between is retained.
  - At cell `i`: facePerm² y is the first retained dart after `a`'s first source dart, i.e. `b`'s first source dart; with `source.darts = a ++ gap ++ b` the gap lies strictly between.
  - Map-level caution: a region touching cell `i` along a side (not its arc) inside the gap is excluded by debt-conditional's class lemmas, since the face class meets no other region.
- Finding: `TwoGonEulerGapInput` as spelled (inclusions only) doesn't locate the source gap, so its producer is stated with the gap equation of `PocketWalk.exists_of_exteriorAt`. ms-inverses-2's L1a drops that equation, so the respelled span input needs a variant of L1a that keeps it.
- 00:38 probe 0914-003836-16332: the MSI hop died (rc=255) before the summary came back, but the remote log shows the module BUILT: `faceClassO_pow_of_firstReturn` and `twoGonPocketFace_of_outerGap`, both [propext, Classical.choice, Quot.sound]. There is no local record, so the whole module is being re-probed with the cell-side lemma added.
- 00:36 probe 0914-003538: MSI connection down (infra); retried.
- 01:1x: GitHub DNS down (`Could not resolve host`), so the attic landing, the report landing and the probe fetch failed; nothing reached origin. A background job retries once GitHub answers.
- Added `twoGonPocketFace_of_targetSpan` to GapFaces: a target span from `a`'s start to `b`'s end without wrap puts its non-arc darts in the outer gap.

CLAIM Euler span C6′ assembly GroupApproximation/GGT/VanKampen/Estimating/OsinAppendixEulerTwoGonEulerSpan.lean

- `TwoGonEulerSpanInput`: `TwoGonEulerWalkInput` with the inclusions replaced by the gap equation and the target start/end equalities, as `PocketWalk.exists_of_exteriorAt` gives them.
- `twoGonHoldsInput_of_eulerSpan : TwoGonEulerSpanInput → TwoGonHoldsInput`, with no gap residual: the gap darts come from GapFaces, and the inclusions and bounds from `OsinAppendixEulerTwoGonSpans`.
- 02:00 probe 0914-015912 RED:
  - `hpow` was typed on the `FaceBoundary` carrier spelling, so `omega` and `rw` saw a different `source.darts`; fixed by typing it against `source.darts`;
  - `getElem_darts_of_le` is not imported; its proof is inlined.
- 08:30: the laptop reboot wiped `/private/tmp`. NM was rebuilt, the overlay list re-added, and the green records lost, so both modules were re-probed.
- LANDED GapFaces at 15dd6c29b: `Estimating/OsinAppendixEulerTwoGonGapFaces`, probe 0914-083056-26600 BUILT; five audits [propext, Classical.choice, Quot.sound], no sorryAx; on the wire queue.
  - `faceClassO_pow_of_firstReturn`;
  - `twoGonPocketFace_of_outerGap` (consumes hull-euler's `exists_sigma_eq_of_twoGon` and `outer_collapsed_facePerm_pow`);
  - `twoGonPocketFace_of_targetSpan`;
  - `getElem?_darts_facePerm_pow`, `twoGonPocketFace_of_cellGap`.
- EulerSpan in the same probe: one red, `rw [hLo]` against the dependent `Fin` in `target.start`; `omega` now uses `hLo` as a hypothesis.
- LANDED EulerSpan at e660b8b53: `Estimating/OsinAppendixEulerTwoGonEulerSpan`, probe 0914-083320-44815 GREEN; audits [propext, Classical.choice, Quot.sound], no sorryAx; on the wire queue.
  - `TwoGonEulerSpanInput`: the noncrossing decomposition walk, the Euler pair, the source gap equation, and the target start/end equalities.
  - `twoGonHoldsInput_of_eulerSpan : TwoGonEulerSpanInput → TwoGonHoldsInput`, with no other residual.
  - `TwoGonEulerGapInput` (c109573e3) is superseded: its content is proved in the gap-equation spelling.
- 08:4x: after the reboot the rebuilt wire queue had lost five of my modules; re-queued (CuttingSides, CuttingSidesCount, CuttingClasses, CuttingClassesClosed, ClassHyp, EulerWalk, PocketFacesEuler).

## CLAIM 8 (main 08:5x: reduce `TwoGonEulerSpanInput` to the edge conditions and the Euler pair)

CLAIM span input from copy-clean GroupApproximation/GGT/VanKampen/Estimating/OsinAppendixEulerTwoGonSpanOfCopyClean.lean

- `PocketWalk.exists_noncrossing_decomposition_gap_of_copyCleanAt`: ms-inverses-2's decomposition with the gap equation kept (additive; their files untouched).
- `TwoGonCopyCleanInput`, `TwoGonDecompositionEulerInput` (named residuals); `twoGonEulerSpanInput_of_copyCleanAt`, `twoGonHoldsInput_of_copyCleanEuler`.
- Planned next: section-level forms with the `OsinTwoGonHoldsSectionStatement` preamble, and `osinTwoGonHoldsSection_of_copyCleanEuler`, for ct-rank-two-limit's V6 composition.
- The Euler-pair spelling went to ms-inverses-2 in one message. ms-inverses-2 had said earlier that its generic lemma needs a named no-interleaving hypothesis.
- LANDED at 9f29a234d: `Estimating/OsinAppendixEulerTwoGonSpanOfCopyClean`, probe 0914-084129-9185 GREEN on the first try; eight audits [propext, Classical.choice, Quot.sound], no sorryAx; on the wire queue.
  - `PocketWalk.exists_noncrossing_decomposition_gap_of_copyCleanAt`;
  - `TwoGonCopyCleanInput`, `TwoGonDecompositionEulerInput`;
  - `twoGonEulerSpanInput_of_copyCleanAt`, `twoGonHoldsInput_of_copyCleanEuler`;
  - `OsinTwoGonCopyCleanSectionStatement`, `OsinTwoGonDecompositionEulerSectionStatement`, `osinTwoGonHoldsSection_of_copyCleanEuler : … → OsinTwoGonHoldsSectionStatement`.
- The V6 leaf names went to ct-rank-two-limit.

## CLAIM 9 (main 09:0x: the caveat, the edge conditions on the given family; w1-binder-4 paused, the copy route is mine)

CLAIM two-gon copy route GroupApproximation/GGT/VanKampen/Estimating/OsinAppendixEulerTwoGonCopyRoute.lean

- Step 1, model test of `TwoGonCopyCleanInput` on the given family, with outer spurs and shared edges. The `spur` clause of `CopyCleanAt` is global: no edge of the diagram has the outer face on both sides. Least area doesn't exclude outer spurs, so no producer can derive it from the labels of the two-gon.
- Step 2: an O-equivalent copy where `CopyCleanAt` holds (w1-binder-6's outer and side thickenings, w1-binder-5's `cellPocketCopyClean` pattern), carried to the two-gon, and the respelled section leaf for ct-rank-two-limit.
- Model-test verdict: `TwoGonCopyCleanInput` can't be produced on the given family. This is an argument, not a built Lean model; the two-gon hypotheses are the ones C6′ refutes, so no model of them exists.
  - Four clauses are global predicates on the optimal diagram, removed only by closed surgeries on O-equivalent copies:
    - `spur` is exactly `∀ x, ¬ OuterSpurThickening.IsOuterSpur S.diagram x`, removed by `outerSpurThickening`;
    - `cell_outer` corresponds to `¬ IsOuterCellDart` (`outerCellThickening`);
    - `side_outer` to `¬ IsOuterSideDart` (`outerSideThickening`);
    - `regions` to `¬ IsRegionPairDart` (ms-intro-2's `regionPairThickening`, ef924c4d2).
  - Least area constrains relator cells, not boundary spurs or regions sharing an edge, and nothing landed excludes these on the given family. So a producer from the two-gon's labels would have to go through C6′ itself.
- Copy route design (module claimed above):
  - `TwoGonHoldsCleanInput`: `TwoGonHoldsInput` plus the edge conditions for every label pair of the two-gon.
  - `twoGonHoldsCleanInput_of_decompositionEuler`: the body of `twoGonHoldsInput_of_eulerSpan` at a fixed family, over the gap-keeping decomposition.
  - `TwoGonCleanCopyInput`: for a two-gon on `S`, some `S'` over the same `Delta` and `cuts` with `NoLoops`, `NoMultipleEdges` and a two-gon whose label pairs all satisfy the edge conditions.
  - `twoGonHoldsInput_of_cleanCopy`, and the section leaf `osinTwoGonHoldsSection_of_cleanCopyEuler`.
  - Producer of `TwoGonCleanCopyInput` (not started): w1-binder-5's `cellPocketCopyCleanBothOrders` pattern composes the outer, cell-edge, cell-side and region-pair thickenings with an invariant transported per step. The open step is carrying the two-gon of `Φ'_M`, with no corner and no cell, through a face-edge doubling.
- LANDED at 7ec4e6fe2: `Estimating/OsinAppendixEulerTwoGonCopyRoute`, probe 0914-085027-63014 GREEN on the first try; eight audits [propext, Classical.choice, Quot.sound], no sorryAx; on the wire queue.
  - `TwoGonHoldsCleanInput`;
  - `twoGonHoldsCleanInput_of_decompositionEuler`, generated from `twoGonHoldsInput_of_eulerSpan`'s body at a fixed family;
  - `TwoGonCleanCopyInput`, `twoGonCleanCopyInput_of_copyCleanInput` (the given-family form implies it);
  - `twoGonHoldsInput_of_cleanCopy`, `twoGonHoldsInput_of_cleanCopyEuler`;
  - `OsinTwoGonCleanCopySectionStatement`, `osinTwoGonHoldsSection_of_cleanCopyEuler : … → OsinTwoGonDecompositionEulerSectionStatement → OsinTwoGonHoldsSectionStatement`.
- The respelled section leaf went to ct-rank-two-limit.

## CLAIM 10 (main 09:1x: the producer of `TwoGonCleanCopyInput`)

CLAIM two-gon doubling transport GroupApproximation/GGT/VanKampen/Estimating/OsinAppendixEulerTwoGonDoublingTransport.lean
CLAIM outer thickening invariant drivers GroupApproximation/GGT/VanKampen/SurgeryOuterThickeningInvariant.lean
CLAIM clean copy producer GroupApproximation/GGT/VanKampen/Estimating/OsinAppendixEulerTwoGonCleanCopy.lean

- Model test of one doubling step: derived against the definitions, no Lean model, no counterexample.
  - `FaceEdgeDoubling.dartImage` sends `w_j` to the new dart and embeds every other dart. The doubled face reads its old traversal through `dartImage`, and every other face keeps its darts.
  - In each thickening the doubled dart is a spur, outer-cell, outer-side, cell-edge, cell-side or region-pair dart: a side or boundary-edge dart, never the head of a source or target arc. So the retained darts of `phiMapO` (the crossings of the component) are carried by `embed`.
  - The first return of the collapsed face permutation keeps its retained order around every face, and the digon holds no retained dart. So `phiMapO` is carried on retained darts with the same rotation: `IsTwoGon`, the labels and `¬GapAtOHoldsCorner` transport (target profiles are preserved).
  - `¬HoldsCellO`: face classes gain only the digon's darts, a G-face; cells correspond through `cellMap`.
  - `ExtPhiData` on the copy is free: `S.pairwise`, `innerGRegion.cells_avoid` under least area, `nondegenerate`, `noLoops`, then `mono`.
  - To check: the region-pair step carries its holder through `Holding.holdingCandidate`, not along arcs. And `IsCellSideDart` needs cell faces of length > 1, so `side_cell` for a length-1 cell face is not covered by `cellSideThickening`. `cell_self` holds automatically for length-1 faces, since `alpha` is fixed-point-free.
- Plan:
  - (1) the per-step invariant `HasCleanTwoGon` and its transport through one doubling carried along arcs;
  - (2) invariant drivers `exists_spurFree_of_invariant`, `exists_cellFree_of_invariant`, `exists_sideFree_of_invariant`, replicating the strong inductions of the landed drivers;
  - (3) the composition, with `CopyCleanAt` from the freeness predicates, giving `twoGonCleanCopyInput`.
- LANDED (1) statements at a7e2c216e: `Estimating/OsinAppendixEulerTwoGonDoublingTransport`, probe 0914-092347-35905 GREEN on the first try; seven audits [propext, Classical.choice, Quot.sound], no sorryAx; on the wire queue.
  - `HasCleanTwoGon`;
  - named step residuals `TwoGonSpurStepStatement`, `TwoGonOuterCellStepStatement`, `TwoGonOuterSideStepStatement`, `TwoGonCellSideStepStatement`, `TwoGonCellHairStepStatement`, `TwoGonRegionPairStepStatement`.
  - Each takes `Delta.LeastArea`, the surgery's own step precondition and `HasCleanTwoGon S`, and returns `HasCleanTwoGon` of that surgery's step family.
- (2) drivers: `SurgeryOuterThickeningInvariant` (`exists_spurFree_of_invariant`, `exists_cellFree_of_invariant`, `exists_sideFree_of_invariant`, `exists_cellHairFree_of_invariant`) is written and probing.
- Composition order planned for (3):
  - spur → outer cell → outer side, each keeping `HasCleanTwoGon`;
  - cell side, keeping `OuterClean ∧ HasCleanTwoGon` via `outerClean_of_step`;
  - cell hair, also keeping no outer-side and no cell-side dart;
  - region pair, keeping the outer conditions, no cell-side dart and no cell hair, via `noOuterSpur_of_step`, `noOuterCellDart_of_step`, `noOuterSideDart_step`, `noCellSideDart_step`, `noCellHair_step`.
  - Then `CopyCleanAt` for every label pair from the six global freeness predicates. `1 < Delta.boundaryWord.length` comes from the two disjoint nonempty target arcs.
- ~09:3x split with ms-inverses-2 (main's item): ms-inverses-2 proves the six step Props verbatim, in new modules `OsinAppendixEulerPhiMapTransport*`, `OsinAppendixEulerTwoGonDoublingInner*` and `OsinAppendixEulerTwoGonDoublingOuter*`. This lane keeps the drivers and the composition `twoGonCleanCopyInput_of_steps`, which takes the six Props as hypotheses.
- (2) drivers `SurgeryOuterThickeningInvariant`: probe 0914-093020-64478 BUILT; the MSI hop died before the summary came back (rc=255), but the remote log shows four audits [propext, Classical.choice, Quot.sound] and no sorryAx. Re-probe 0914-101108-54760 GREEN for local evidence; landing now.
- LANDED drivers at 0f4475355 (`SurgeryOuterThickeningInvariant`), on the wire queue.
- LANDED (3) at 73835dd09: `Estimating/OsinAppendixEulerTwoGonCleanCopy`, probe 0914-102626-36239 GREEN, BUILT on the first try; four audits [propext, Classical.choice, Quot.sound], no sorryAx; on the wire queue.
- Leaf 6 now reduces to the six step Props, through `osinTwoGonCleanCopySection_of_steps`. With the Euler section Prop, `osinTwoGonHoldsSection_of_stepsEuler` gives `OsinTwoGonHoldsSectionStatement`. ms-inverses-2 is proving the six step Props and the Euler section Prop.
- (3) composition `Estimating/OsinAppendixEulerTwoGonCleanCopy`:
  - `twoGonCopyCleanAt_of_free`;
  - `twoGonCleanCopyInput_of_steps` over the six step Props;
  - `osinTwoGonCleanCopySection_of_steps`, `osinTwoGonHoldsSection_of_stepsEuler`.
- `side_cell` needs `1 < length` of cell `i`'s face for `IsCellSideDart`. For distinct exterior regions `a`, `b` of `i` it holds: on a one-dart face both source arcs would be that dart, so the face across it would lie in both regions, and `eq_of_face_mem_of_face_mem` gives `a = b`.

## Current C6′ leaves (binder 4)

`osinTwoGonHoldsSection_of_cleanCopyEuler` consumes two named section Props:
1. `OsinTwoGonCleanCopySectionStatement`: a two-gon on a clean copy. The producer composes the closed thickenings; carrying the two-gon of `Φ'_M` through face-edge doubling is open and unowned.
2. `OsinTwoGonDecompositionEulerSectionStatement`: the Euler pair of the decomposition walk. ms-inverses-2's no-interleaving lemma plus a no-interleaving Prop for pocket walks.

## State of C6′ on the Euler route

`TwoGonHoldsInput` follows from `TwoGonEulerSpanInput` alone. Its producers:
- the noncrossing decomposition walk with the gap equation: ms-inverses-2's `PocketWalk.exists_noncrossing_decomposition_of_copyCleanAt` builds it but drops the gap equation, so it needs a variant that keeps `⟨Gap, hsrc⟩`;
- the edge conditions `CopyCleanAt`: the clause producers of w1-binder-6, ms-binary, ms-cite-2 and ms-intro-2;
- the Euler pair: ms-inverses-2's no-interleaving lemma plus a no-interleaving Prop for pocket walks.

## Residuals of the Euler C6′ route

- `TwoGonEulerWalkInput` (eeddf1c9e):
  - the noncrossing decomposition walk: ms-inverses-2's L1a plus the `CopyCleanAt` clause producers;
  - the Euler pair: ms-inverses-2's `NoncrossingClosedWalkEulerNoninterleaving` plus a no-interleaving Prop for pocket walks;
  - clauses 2–5: `OsinAppendixEulerTwoGonSpans` from `PocketWalk.exists_of_exteriorAt`;
  - the arc bounds.
- `TwoGonEulerGapInput` (c109573e3), named, unowned. Hand argument, not model-tested in Lean:
  - the gap darts are not retained, since the two-gon face turns at cell `i` and at the outer vertex with no other component region in its corner;
  - so the face class runs along the gaps from the first source dart of `b` and the reversed first target dart of `a` (`faceClassO_of_isChain`);
  - then `ExtPhiData.twoGonPocketFace_of_faceClassO` applies.

## State

The cutting half of Osin (38) is CLOSED, at side level and at class level, with no open binder. For `ClassCountInput`, the cutting classes of `ClassBudget` are paid by `card_cuttingClasses_le_of_dartMinimal`. The rest of the class count (other classes ≤ K n) belongs to sec5-sentences (`OsinLemma94LongTransitionInput`), hull-count94 (the `ClassJoins` assembly) and hull-component (bubbles).
