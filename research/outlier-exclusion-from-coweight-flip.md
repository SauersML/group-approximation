---
rg: 2
id: outlier-exclusion-from-coweight-flip
kind: route
title: Treat the free swap projection as one common complemented coweight sheet
target: sl3-outliers-carry-no-balanced-free-involution
requires:
  - coweight-triangle-charges-every-common-sheet-flip
---

**INVALIDATED PROPOSAL.**  Apply the rank-two coweight triangle to the
balanced projection `P=(1+s)/2` supplied by a hypothetical free swap
involution, treating each denominator translate as an approximate copy of
`1-P`.  If all three complement errors vanished, `(CTA8)` would indeed give
a contradiction.

`free-swap-is-midpoint-not-coweight-flip` computes the actual errors forced
by amalgamated freeness: every one converges to `1/sqrt(2)`, so the triangle
bound is satisfied with large slack.  The free pattern is independence,
not complement transport.  No improvement of the `1/3` constant, and no
use of the exact triangle word alone, can bridge that fixed gap.
