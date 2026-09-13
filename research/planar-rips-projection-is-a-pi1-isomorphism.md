---
rg: 2
id: planar-rips-projection-is-a-pi1-isomorphism
kind: claim
title: "The Rips complex of a finite planar set maps to its shadow by a pi_0- and pi_1-isomorphism, so its fundamental group is free"
distinct_from:
  rips-complexes-of-finite-planar-sets-are-wedges-of-spheres: that claim is about the full homotopy type; this one records the components and the fundamental group only
---

Let `X ⊆ R^2` be finite and `r > 0`. The projection `p: R_r(X) → R^2` sends
each vertex to its point and extends linearly over simplices; its image is the
shadow `S(X; r) = ∪ conv(Y)` over `Y ⊆ X` with `|Y| ≤ 3` and `diam(Y) < r`
(Carathéodory). Then `p: R_r(X) → S(X; r)` induces bijections on path
components and isomorphisms on fundamental groups.

Consequence: `π_1(R_r(X))` is free, because the shadow is a compact planar
polyhedron and each of its components is homotopy equivalent to a finite
graph.

Both conventions (diameter `< r` and `≤ r`) are covered for finite `X`, by
changing `r` slightly.
