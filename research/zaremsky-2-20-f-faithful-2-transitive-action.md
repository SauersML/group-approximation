---
rg: 2
id: zaremsky-2-20-f-faithful-2-transitive-action
kind: claim
title: "Zaremsky Problem 2.20 resolved: does Thompson's group F admit a faithful 2-transitive action?"
root: true
distinct_from:
  thompson-f-admits-a-faithful-2-transitive-action: that claim is the affirmative answer; this claim is the question, established by either answer
  thompson-f-has-no-faithful-2-transitive-action: that claim is the negative answer; this claim is the question, established by either answer
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 2, Problem 20, verbatim:
"(Added 10/2/25) Does F admit a faithful 2-transitive action? (Question of Le
Boudec–Matte Bon)".

This claim is the question. It is established only through an answer route:

- **Yes**: `zaremsky-2-20-by-yes` requires `thompson-f-admits-a-faithful-2-transitive-action`.
- **No**: `zaremsky-2-20-by-no` requires `thompson-f-has-no-faithful-2-transitive-action`.

Never write a `requires: []` route into this claim.

## Precise reading

`F` is Thompson's group of piecewise linear homeomorphisms of `[0,1]` with
dyadic breakpoints and slopes powers of 2. An action of `F` on a set `Ω` is
2-transitive if `F` is transitive on ordered pairs of distinct points. Since
`F` is infinite, a faithful action needs `|Ω| ≥ 3`, and every 2-transitive
action on at least 3 points is automatically faithful
(`thompson-f-two-transitive-actions-are-faithful`). So the question asks
whether the transitivity degree `td(F)` of Hull and Osin is 2 (yes) or 1 (no).
Known: `td(F) ≤ 2` (Le Boudec–Matte Bon, arXiv:1906.05744, Corollary 5.3),
recorded as `thompson-f-transitivity-degree-at-most-two`. The same paper
(p. 4, v3): "we do not know whether this could be improved from 2 to 1"; it
also asks (p. 23) whether stabilizers of partitions of an `F`-orbit give
2-transitive actions on `F/H`.

Equivalent group-theoretic form: is there a subgroup `H < F` with exactly two
`(H,H)`-double cosets and `|F/H| ≥ 3`?

## Where the problem stands (2026-09-13, unreviewed results)

Any point stabilizer `H` of a 2-transitive action must satisfy:

1. `H` is maximal of infinite index, and `H ∩ [F,F] ≠ 1`;
2. `H` contains no rigid-stabilizer group `F_U^c` of compactly supported
   elements in an interval (`thompson-f-two-transitive-rigid-stabilizers-fix-no-point`).
   So `H` acts minimally on `(0,1)` and is not confined
   (`thompson-f-two-transitive-stabilizers-minimal-not-confined`);
3. `H` is closed in the Golan–Sapir sense
   (`thompson-f-two-transitive-stabilizers-are-piecewise-closed`).

Condition 3, and with it the grid condition of Le Boudec–Matte Bon
Proposition 5.1(2) at dyadic points, holds for EVERY maximal subgroup of
infinite index: Golan (arXiv:2209.03244) proves they are all closed, and
closedness gives the splitting, which is equivalent to the grid condition at
that point. So Proposition 5.1 cannot separate `td(F) = 1` from 2. Condition 2
is a genuine restriction: it kills stabilizers of closed subsets of `(0,1)`
and every action on orbits in `(0,1)`. What remains is maximal closed
subgroups containing no `F_U^c`, such as stabilizers of dense sets of dyadic
fractions (Jones' subgroup is the stabilizer of the dyadic fractions with odd
digit sum, Golan–Sapir arXiv:1501.00724 Theorem 2) and the non-parabolic
maximal subgroups of Golan–Sapir (arXiv:1508.00493) and Golan
(arXiv:2209.03244).

## Attempts

- 2026-09-13 (lane z2-20-f-2-transitive): status confirmed open (Zaremsky list
  July 2026; Le Boudec–Matte Bon v3). Conditions 1–3 are proved. The detailed
  test protocol for the remaining candidates is on
  `thompson-f-admits-a-faithful-2-transitive-action`; the case analysis is on
  `thompson-f-has-no-faithful-2-transitive-action`.
