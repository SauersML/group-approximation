---
rg: 2
id: zaremsky-1-03-qi-to-connected-space-implies-type-fn
kind: claim
title: "Zaremsky Problem 1.3 resolved: is a group quasi-isometric to an (n-1)-connected proper geodesic space of type F_n?"
root: true
distinct_from:
  every-fg-group-is-qi-to-a-contractible-proper-space: that claim settles the literal metric-only reading negatively for every group; this claim is the question under the geodesic reading, which that construction does not touch
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 1, Problem 3, verbatim:
"If a finitely generated group is quasi-isometric to an (n − 1)-connected
proper metric space, is the group of type F_n? (The converse is true.)"

**Reading.** Read literally, with an arbitrary proper metric, the answer is
no for every n ≥ 2 and every finitely generated group that is not of type
F_n: `every-fg-group-is-qi-to-a-contractible-proper-space` restricts the path
metric of a Cayley graph to a spanning tree. That construction uses a metric
which is not a length metric, so the list surely means a proper **geodesic**
metric space, the setting of the converse (the universal cover of the
n-skeleton of a K(G,1) with finite n-skeleton). This claim is that question:

> Let n ≥ 2 and let G be a finitely generated group quasi-isometric to a
> proper geodesic metric space X that is (n − 1)-connected. Must G be of
> type F_n?

For n = 1 there is nothing to ask: every finitely generated group is of type
F_1. G is of type F_n if and only if it is coarsely (n − 1)-connected. The
content of the question is whether plain (n − 1)-connectedness of X, with no
uniform bound on the size of fillings, forces that.

This claim is the question. It is established only through an answer route:

- **Yes**: `zaremsky-1-03-by-yes` requires
  `fg-group-qi-to-n-connected-geodesic-space-is-type-fn`.
- **No**: `zaremsky-1-03-by-no` requires
  `some-non-fn-group-is-qi-to-n-connected-geodesic-space`.

Never write a `requires: []` route into this claim.

## Attempts

- 2026-09-13 (lane z1-03-qi-fn): the literal reading fails (see above).
- The geodesic case n = 2 is settled positively:
  `fg-group-qi-to-simply-connected-geodesic-space-is-fp`, reviewed PASS by
  z-verify-topology (`research/artifacts/zp-review-topology-2026-09-13-part2.md`
  §12a). Only edges have to be realized in X, and geodesics do that.
- For n ≥ 3 the open question reduces to a combinatorial one.
  `short-detour-enumeration-gives-contractible-qi-2-complex` (reviewed PASS,
  §12b) shows that a group with a short-detour enumeration is
  quasi-isometric to a contractible proper geodesic 2-complex. So a no answer
  follows from `some-non-f3-group-has-a-short-detour-enumeration`, and a yes
  answer would force every group with such an enumeration (every almost
  convex group, for instance) to be of type F_∞.
- Test cases under way: the Stallings–Bieri group SB_3 and the double
  F_2^2 *_{SB_2} F_2^2
  (`research/artifacts/zp-sb3-short-detour-2026-09-13-part1.md`).
