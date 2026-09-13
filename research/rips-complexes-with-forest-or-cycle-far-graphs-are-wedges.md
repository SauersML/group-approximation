---
rg: 2
id: rips-complexes-with-forest-or-cycle-far-graphs-are-wedges
kind: claim
title: "A Rips complex whose far graph has only trees and cycles as components is a point or a wedge of spheres"
distinct_from:
  rips-complexes-of-finite-planar-sets-are-wedges-of-spheres: that claim covers every finite planar set; this one needs the far graph to be a disjoint union of trees and cycles, for any finite metric space
---

Let `(X, d)` be a finite metric space and `r > 0`. Its **far graph** `H_r(X)`
has vertex set `X` and joins `x, y` when `d(x, y) > r`. The Rips complex
`R_r(X)` (simplices of diameter `≤ r`) is the independence complex
`Ind(H_r(X))`. If every connected component of `H_r(X)` is a tree or a cycle,
then `R_r(X)` is contractible or homotopy equivalent to a finite wedge of
spheres.

Planar instances: regular `m`-gons at scales between the second-longest and
the longest chord (far graph a perfect matching or an odd cycle), and every
finite planar set in which each point is farther than `r` from at most two
others (far graph of maximum degree `≤ 2`). In the bounded search
`research/artifacts/zp-planar-rips-search-2026-09-13.md`, most reduced cores
with homology above degree 1 were of this kind.

## Attempts

- Proof in `rips-complexes-with-forest-or-cycle-far-graphs-are-wedges-proof`.
