---
rg: 2
id: rank-two-h1-triangle-presentation-no-brick-coding-proof
kind: route
title: Affine corner graphs give (C1) and constant row sums; the corner theorem then kills every brick coding
target: rank-two-h1-tile-two-graphs-admit-no-brick-coding
requires:
  - triangle-presentation-tile-two-graphs-have-affine-corner-graphs
  - two-graph-brick-codings-die-at-connected-corners
artifacts:
  - research/artifacts/nv-brick-coding-corner-kill-2026-09-17.md
---

Full proof: Part G of the artifact.

1. By `triangle-presentation-tile-two-graphs-have-affine-corner-graphs`, every vertex of
   `Λ_T` emits `q^2` edges of each colour. So the row sums are constant and both colours
   occur, which completes (R1). Every corner graph `B_1(a)` is connected, which is (C1).
2. With (R2) and (R3) assumed, `two-graph-brick-codings-die-at-connected-corners` applies
   and excludes brick codings in every dimension.
