# w1-binder-4

Lane `w1-binder-4` (session nonsofic-existence-49, wave 2) is an independent second start on binder 4 of the post-(A)
W1 waist, `OsinTwoGonHoldsSectionStatement` (C6′ of Osin's Lemma 9.3). The owners are debt-conditional, baseline-debt,
hs-vanishes and sec2-sentences. This lane never edits their files.

## CLAIM

- CLAIM C6′ uniform noncrossing route `GroupApproximation/GGT/VanKampen/Estimating/OsinAppendixEulerTwoGonNoncrossingRoute.lean`
- CLAIM C6′ merge-disc route `GroupApproximation/GGT/VanKampen/Estimating/OsinAppendixEulerTwoGonMergeDisc.lean`

## Landed

`Estimating/OsinAppendixEulerTwoGonNoncrossingRoute` (probe 0913-172423-51771 GREEN, COMPILED; unwired). The build log of
0913-171621-20850 shows axioms [propext, Classical.choice, Quot.sound] for all three declarations.

- `TwoGonNoncrossingPocketInput`: for the labels of a two-gon, the walk `source.reverseDarts ++ a.rightSide ++ target.darts
  ++ b.leftSide` is noncrossing, its outer cycle follows its boundary, `a` and `b` lie on its side, and no relator cell and
  no other selected region lies on its side, with the printed arc bounds.
- `outerFace_not_mem_sideFaces_of_target_mem`: the exterior face is off the side of a noncrossing walk that holds the darts
  of a nonempty arc of the oriented outer boundary.
- `twoGonHoldsInput_of_noncrossingPocket : TwoGonHoldsInput` from that Prop, through `exists_twoGonLabels`,
  `PocketRegion.ofNoncrossingClosedWalk`, `reclosed_euler` and `emptyTwoGonInput_holds`. There is no split into simple
  and pinched walks.

## Finding: in the lake, U has no PocketRegion, but the collapse does not need one

This is a hand argument, not a Lean model.

- The decomposition bounds `U = a ∪ gap ∪ b`: the source arc spans both source arcs, and the target arc spans both
  targets. `a.rightSide` and `b.leftSide` are the outer sides of `U`.
- Suppose `a.rightSide` and `b.leftSide` touch at a vertex `v`. Then the complement of `U` has two components:
  - the exterior side;
  - a lake, bounded by `b.leftSide[v..] ++ invDarts(source span) ++ a.rightSide[..v]`, which holds cell `i`.
- Nothing rules the touch out:
  - sec2-sentences found nothing in the family fields that does (report, 17:14);
  - audit-sec5 sees nothing short of Lemma 9.7(b) (dgo-analytic report, binder 5 lake section).
- `v` is not a vertex of `Φ'_M`, so the lake lies in the other face at cell `i`. The face `f` can still be an empty
  two-gon with no corner in its gap.
- Consequences:
  - The outer cycle of the walk does not follow its boundary (Configuration B, `OsinPocketLakeModel`). So
    `TwoGonNoncrossingPocketInput` as landed may be false in the lake.
  - No `PocketRegion` has faces `U`, because `PocketRegion.outer` needs a disc complement. So `EmptyTwoGonInput` cannot
    fire on `U`. This affects every C6′ route through `EmptyTwoGonInput`, including the planned module 4.
- The proved collapse does not need the complement:
  - `Surgery.InnerDiscRegion` (`SurgeryInnerDiscCollapse.lean:45`) carries only the inner disc region, `outer_not_mem`,
    `cells_avoid` and `value_one`.
  - `false_of_disc_collapse_singleton` (`OsinPocketDiscMerge.lean:210`) takes it directly.
  - `emptyTwoGonInput_holds` uses its `PocketRegion` only through `InnerDiscRegion.ofPocketRegion` and the rotation of
    the inner cycle.

## Next: the merge-disc residual (new module, claimed above)

- `TwoGonMergeDiscInput`: an `InnerDiscRegion` of `S.diagram` whose cycle rotates to the decomposition, with every other
  selected region disjoint from its faces, and the arc bounds. There is no outer clause and no containment of `a` and `b`.
- `twoGonHoldsInput_of_mergeDisc`: C6′ from it, through `mergedGeometry` and `false_of_disc_collapse_singleton`.
- Producers of the disc from a noncrossing walk:
  - the inner cycle follows (Configuration B, the lake);
  - the outer cycle follows, plus `reclosed_euler` (Configuration A, the pinched two-gon).

## In flight: `Estimating/OsinAppendixEulerTwoGonMergeDisc` (probing; attic copy landed)

- `GloballyDistinguishedSectionFamily.false_of_mergeDisc`: the argument of `emptyTwoGonInput_holds`, run at the level of
  `Surgery.InnerDiscRegion` with generic labels. The contiguity geometry is built from the rotated decomposition through
  `mergedGeometry`.
- `TwoGonMergeDiscInput`, and `twoGonHoldsInput_of_mergeDisc : TwoGonHoldsInput` from it.
- Subsumption scan:
  - `OsinPocketZeroCellMergeFalse` (:55) and `OsinPocketKeptCellAbsorbed` (:283) also refute with an `InnerDiscRegion`,
    but they take the merged geometry `H` as a hypothesis, so they are not duplicates.
  - `emptyTwoGonInput_holds` is this lemma at `R := InnerDiscRegion.ofPocketRegion P`.

## Leaves of a producer of `TwoGonMergeDiscInput`

- L1: `hw`, a noncrossing pocket walk equal to the decomposition. sec2-sentences argues that it holds when the sides meet
  only at vertices, and fails when they share an edge.
- L2: the inner cycle or the outer cycle follows its boundary.
  - Inner: `toDiscRegion_of_followsBoundary`.
  - Outer: `reclosed_euler` then `toDiscRegion_of_euler`.
- L3: `value_one` for a disc region with no relator cell. `PocketRegion.diagram` collapses the complement through
  `P.outer`, so in a lake the value must come from the region's own reclosed map instead.
- L4, L5: `TwoGonClassHyp` for the face class of the two-gon, and `TwoGonWalkHyp` for the walk. These are
  debt-conditional's hypotheses behind `cell_face_not_mem_sideFaces_of_twoGon` (`hno`) and
  `disjoint_sideFaces_of_twoGon` (`havoid`).

## Residual

- The first-turn property of the pocket walk, or directly `hw` with one of the two following clauses. sec2-sentences owns
  the first-turn producer and reports it blocked by the lake. That is why the merge-disc residual allows inner following.
- `hno` and `havoid` on the walk: debt-conditional's `TwoGonWalkHyp` (module 3), or absorption (sec2-sentences).

## Progress log

- 2026-09-13 ~17:05: claim landed (45e056fef).
- 17:16: first probe GREEN on MSI, but the lead restart at 17:19 killed the local waiter before it wrote the record.
- 17:24: re-probe GREEN, record written; route module landed.
