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
2-transitive if `F` is transitive on ordered pairs of distinct points of `Ω`.
Since `F` is infinite, a faithful action needs `|Ω| ≥ 3`, and every
2-transitive action on at least 3 points is automatically faithful
(`thompson-f-two-transitive-actions-are-faithful`). So the question asks
whether the transitivity degree `td(F)` of Hull and Osin (the supremum of `k`
such that `F` has a faithful `k`-transitive action) is 2 (yes) or 1 (no).

Known partial result: `td(F) ≤ 2` (Le Boudec–Matte Bon, arXiv:1906.05744,
Corollary 5.3), recorded as `thompson-f-transitivity-degree-at-most-two`. The
same paper says (p. 4, v3) "we do not know whether this could be improved from
2 to 1", records (p. 23) that Hull and Osin asked for `td(F)`, and asks whether
stabilizers of partitions of an `F`-orbit in `[0,1]`, such as a maximal
subgroup of Golan–Sapir, give 2-transitive actions on `F/H`.

The natural actions of `F` on its orbits in `(0,1)` preserve the order, so
they are transitive on increasing pairs but not on ordered pairs: none is
2-transitive.

## Attempts

- 2026-09-13 (lane z2-20-f-2-transitive): status check. Zaremsky's list
  (July 12, 2026) still records the problem as open, and Le Boudec–Matte Bon
  v3 (June 2021) leave it open. Automatic faithfulness is proved. By Le
  Boudec–Matte Bon Proposition 5.1 together with the fact that `[F,F]` is not a
  single `F`-conjugacy class, every 2-transitive action satisfies the grid
  condition: for each `x ∈ (0,1)`, orbits of the left and right parts of the
  stabilizer of `x` meet in at most one point. Attack plans are on the two
  answer claims.
