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

- 2026-09-13 (lane z1-03-qi-fn): the literal reading fails (see above). Under
  the geodesic reading, the case n = 2 is being written up as a positive
  theorem. A coarse loop is realized by geodesics and filled by a disc in X.
  Uniform continuity of the disc gives a fine triangulation, and projecting
  it to G fills the loop at a bounded Rips scale. Only edges need realizing
  in X, so no uniformity is used. For n ≥ 3, realizing 2-simplices needs
  discs in X of bounded diameter for small loops, and plain simple
  connectivity does not give them. That is the open case.
