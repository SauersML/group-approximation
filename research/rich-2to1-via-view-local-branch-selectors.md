---
rg: 2
id: rich-2to1-via-view-local-branch-selectors
kind: route
title: Dead -- orient Grassmann 2-to-1 instances with a selector that reads only bounded, parity-faithful views of the source 3LIN right-hand sides
target: rich-2to1-games-conjecture
requires: []
---

**Dead.** The attack takes the known hard Grassmann 2-to-1 instances
(`two-to-two-games-theorem`). It orients every constraint by a branch selector,
so that the orientation lift is a unique game. The lift has soundness at most
the source value, and its right merge is fully rich. The selector reads only
what it needs at each edge: the window's equations and a bounded neighbourhood of
right-hand sides. Completeness above one half would be certified by the honest
labelling of a near-satisfying assignment.

It is killed by `view-local-branch-selectors-are-gauge-blind`. Take the gauge
`I -> I^z = (M, b + Mz)`, which is a value-preserving polynomial-time map on 3LIN.
Whenever the view sees no parity of window variables beyond `H_U`, the branch bit
of the transported witness is exactly uniform given everything the selector
reads. So the honest lift value is `1/2` in expectation, and it concentrates
uniformly over equivariant witness menus of size `exp(o(n))`. The route needs
parity leakage on a `1 - 2 eta' - o(1)` fraction of edges. That is a different
route: `parity-leaking-branch-selectors-reach-near-perfect-completeness`.
