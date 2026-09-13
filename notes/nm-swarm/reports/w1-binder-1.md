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

## Progress log

- 16:5x: claim landed; statement module next.
