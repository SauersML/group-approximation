---
rg: 2
id: flat-iwahori-step-fails-on-a-diluted-character
kind: route
title: Retain a fixed operator defect while dilution makes the sixth-flat parameter budget vanish
target: dilution-obstructs-flat-quadratic-iwahori-repair
requires:
  - modular-vertex-charts-have-uniform-schatten-control
artifacts:
  - research/artifacts/iwahori-dilution-moment-obstruction-2026-09-08.md
---

The artifact checks the one-dimensional modular character and all three
Iwahori mismatches explicitly. The surviving mismatch is a length-six
unitary word with operator defect two on the original block, which
padding preserves before correction.

A superlinear normalized-HS residual in a dimension `O(n)` has vanishing
operator norm. Telescoping the word forces generator movement at least
`(2-o(1))/6`. Schatten norm comparison gives the quantitative moment-ratio
bound for every repair, independently of its construction.

The prerequisite supplies operator movement at most four times the
parameter-tuple operator norm. The proposed sixth-flat square-root and
linear parameter budgets make that norm `O(n^(-1/12))`, a contradiction.
The same explicit input has a trivial exact repair of linear HS cost,
which proves the stated scope distinction.
