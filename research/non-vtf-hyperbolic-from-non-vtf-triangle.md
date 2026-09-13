---
rg: 2
id: non-vtf-hyperbolic-from-non-vtf-triangle
kind: route
title: A hyperbolic triangle of finite groups with no vertex-injective finite quotient is a non-virtually-torsion-free hyperbolic group
target: non-virtually-torsion-free-hyperbolic-group
requires: [hyperbolic-triangle-of-finite-groups-not-virtually-torsion-free]
---

Let `G` be the colimit of the premise triangle. It satisfies the hypotheses of
Caprace–Conder–Kaluba–Witzel, arXiv:2011.09276, Theorem 3.1, with strict inequality
(read at source 2026-09-13).
- By (v), `G` is non-elementary hyperbolic, in particular infinite.
- By (i), the vertex groups inject into `G`. So `G` has nontrivial torsion.

Suppose `G` had a torsion-free finite-index normal subgroup `N`. Then `N` would meet
every vertex group trivially, and `G -> G/N` would be a finite quotient injective on all
three vertex groups. The premise excludes such a quotient, so `G` is not virtually
torsion-free.
