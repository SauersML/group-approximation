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
