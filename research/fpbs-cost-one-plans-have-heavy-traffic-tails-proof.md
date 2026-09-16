---
rg: 2
id: fpbs-cost-one-plans-have-heavy-traffic-tails-proof
kind: route
title: Cut the used graph into large Voronoi cells and charge the Cheeger boundary to crossing traffic
target: fpbs-cost-one-plans-have-heavy-traffic-tails
requires:
  - fpbs-traffic-variational-cost-identities
  - fpbs-khezeli-products-have-fixed-price-one
artifacts:
  - research/artifacts/fpbs-cost-one-plans-have-heavy-traffic-tails-2026-09-16.md
---

Lemma 4 of the artifact adds a direct copy for each uncovered request. This
keeps B and every tail, and makes the used graph's components whole orbits.

Lemma 5 builds a Borel maximal independent set of the distance-2R graph by
countable colouring and greedy selection. It assigns points to the nearest
marker, breaking ties by a Borel order. Cells are finite, contain the R-ball,
and are spanned by parent copies of total measure one minus the marker
measure.

Lemma 6 is the mass transport count: by freeness a cell is a finite subset of
the group, so generator requests leaving cells have measure at least h_S.

Every leaving request crosses a copy joining two cells. Such copies have
measure at most B - 1 + 1/(R+1). The change-of-variables identity and the
pointwise bound k <= T+1+Q 1_{Q>T} give the inequality. Let R -> infinity.

Corollaries (a)-(d) are elementary manipulations of the inequality. The
strictness corollary uses two established nodes. Khezeli's theorem gives
fixed price one for F_2 x Z. Theorem 5.1 of the conditional-traffic artifact
supplies plans with B -> 1 and J -> 0. The inequality itself and corollaries
(a)-(d) use no imported theorem.
