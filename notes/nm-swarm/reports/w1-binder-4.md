# w1-binder-4

Lane `w1-binder-4` (session nonsofic-existence-49, wave 2) is an independent second start on binder 4 of the post-(A)
W1 waist, `OsinTwoGonHoldsSectionStatement` (C6′ of Osin's Lemma 9.3). The owners are debt-conditional, baseline-debt,
hs-vanishes and sec2-sentences. This lane never edits their files.

## CLAIM

- CLAIM C6′ uniform noncrossing route `GroupApproximation/GGT/VanKampen/Estimating/OsinAppendixEulerTwoGonNoncrossingRoute.lean`
- CLAIM C6′ merge-disc route `GroupApproximation/GGT/VanKampen/Estimating/OsinAppendixEulerTwoGonMergeDisc.lean`
- CLAIM C6′ either-follows assembly `GroupApproximation/GGT/VanKampen/Estimating/OsinAppendixEulerTwoGonEitherFollows.lean`
- CLAIM C6′ copy-route assembly `GroupApproximation/GGT/VanKampen/Estimating/OsinAppendixEulerTwoGonEitherFollowsCopy.lean`
- CLAIM C6′ inner-builder discharge `GroupApproximation/GGT/VanKampen/Estimating/OsinAppendixEulerTwoGonInnerFollowsClosed.lean`
  (waits for ms-torsionfree's `OsinPocketRegionInnerFollows`)
- CLAIM (dropped 18:40) L4/L5 in `OsinAppendixEulerTwoGonClassWalkHyp.lean`. The split with w1-binder-1 replaces it:
  - w1-binder-1 takes L4 (`TwoGonClassHyp`) and L5a (`left_side`, `right_side`, `base`) in
    `Estimating/OsinAppendixEulerTwoGonClassHyp.lean`, plus the following clause on the copy walk and the Configuration A
    per-lobe argument.
- CLAIM L5b (`connected`, `outer_off`, `cell_off`) and the `TwoGonWalkHyp` assembly
  `GroupApproximation/GGT/VanKampen/Estimating/OsinAppendixEulerTwoGonWalkHypInner.lean`
- CLAIM face-class connectivity of following boundary cycles `GroupApproximation/GGT/VanKampen/BoundaryCycleFaceClass.lean`

Split of L1 (ms-inverses-2's proposal, no collision):
- ms-inverses-2 takes L1a: rotation invariance of noncrossing walks, and `hw` in the decomposition spelling from `CopyClean`.
- ms-inverses-2 also takes L1b, the `regions` clause: an O-equivalent copy that separates edges joining `a` to `b`.
- ms-torsionfree takes the inner-following builder.

## Landed: `Estimating/OsinAppendixEulerTwoGonEitherFollows` (c5f2b7378, probe 0913-180835-10074 GREEN, unwired)

All three declarations depend only on the axioms [propext, Classical.choice, Quot.sound].

- `PocketRegionOfInnerFollowsStatement`: a pocket region on the side of a noncrossing walk whose inner cycle follows its
  boundary. ms-torsionfree's builder `PocketRegion.ofNoncrossingClosedWalkInner` discharges it once landed.
- `TwoGonEitherFollowsPocketInput`: the noncrossing residual in which the outer cycle or the inner cycle follows.
- `twoGonHoldsInput_of_eitherFollows : TwoGonHoldsInput`. The outer branch uses `PocketRegion.ofNoncrossingClosedWalk`
  and `reclosed_euler`; the inner branch uses the named Prop. Both then go through `emptyTwoGonInput_holds`.

## Landed: `Estimating/OsinAppendixEulerTwoGonInnerFollowsClosed` (6fcc8658b, probe 0913-182332-15112 GREEN, unwired)

- `pocketRegionOfInnerFollowsStatement` (`#audit_closed_axioms`) is ms-torsionfree's `PocketRegion.ofNoncrossingClosedWalkInner`
  (2d0b61555).
- `twoGonHoldsInput_of_eitherFollowsPocket` and `twoGonHoldsInput_of_eitherFollowsCopyPocket` give C6′ from either
  noncrossing residual alone.
- All three declarations depend only on the axioms [propext, Classical.choice, Quot.sound].

## Landed: `Estimating/OsinAppendixEulerTwoGonWalkHypInner` (L5b, 20767e008, probe 0913-183536-76676 GREEN, unwired)

Both declarations depend only on the axioms [propext, Classical.choice, Quot.sound].
Next: the `hno`/`havoid` assembly for inner-following walks, once w1-binder-1's L4/L5a names land.

- `cellFace_not_mem_sideFaces_of_source_mem`: the face of the cell is off the side of a noncrossing walk through a
  reversed arc of that cell.
- `twoGonWalkHyp_of_innerFollows : TwoGonWalkHyp a b i walk`, for a noncrossing walk whose inner cycle follows:
  - `outer_off`, `cell_off` and `connected` are proved;
  - `left_side`, `right_side` and `base` are hypotheses, which w1-binder-1's L5a supplies.

## Landed: `BoundaryCycleFaceClass` (a19fd73b8, probe 0913-183317-65387 GREEN, unwired; first probe red on a placeholder, fixed)

- `BoundaryCycle.eqvGen_of_mem_of_followsBoundary`: all darts of a following boundary cycle lie in one face class of the
  walk.
- `IsNoncrossingClosedWalk.eqvGen_of_mem_of_innerFollows` is `TwoGonWalkHyp.connected` for inner-following walks.
- Hand argument: in Configuration A (outer following only) the two lobes share no edge, so `connected` fails there.

## Landed: `Estimating/OsinAppendixEulerTwoGonEitherFollowsCopy` (704b70f2c, probe 0913-181302-25404 GREEN, unwired)

All four declarations depend only on the axioms [propext, Classical.choice, Quot.sound].

- `GloballyDistinguishedSectionFamily.false_of_eitherFollowsPocket`: the contradiction with generic labels on any
  globally distinguished family.
- `TwoGonEitherFollowsCopyInput`: the pocket on some globally distinguished family `S'` over the same `Delta` and
  `cuts`. That is the output shape of `OuterSpurThickeningStatement` plus `PocketWalk.CopyClean`
  (`isNoncrossingClosedWalk_of_copyClean`, baseline-debt 42d2d8e26).
- `twoGonHoldsInput_of_eitherFollowsCopy`, and `twoGonEitherFollowsCopyInput_of_pocketInput`, which takes `S' = S`.

## Correction (2026-09-13 ~18:05): the lake still has a PocketRegion

The finding below overclaimed. `PocketRegion.outer` is an `IsDiscRegion` of the complement: the reclosing is connected
and preserves the Euler characteristic. It is not a following condition.
- Reclosing both complement components as one face splits the pinch vertex.
- Hand count on the lake rose: vertex orbits {0,3} and {1,2}, 2 edges, 2 faces, so χ = 2.
- So a PocketRegion exists in the lake, and `EmptyTwoGonInput` can fire there. Only the builder asks for outer
  following.
- The correction went to main before any relay.

Handoff:
- ms-torsionfree takes the inner-following builder, which covers L2's inner branch and L3.
- This lane consumes it through the named Prop `PocketRegionOfInnerFollowsStatement`, in the either-follows assembly.
- The shared-edge case, where `alpha_not_mem` fails, is still open. It is sec2-sentences' options (i) or (ii).

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

## Landed: `Estimating/OsinAppendixEulerTwoGonMergeDisc` (13776be09, probe 0913-173915-12004 GREEN, unwired)

All three declarations depend only on the axioms [propext, Classical.choice, Quot.sound].

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
