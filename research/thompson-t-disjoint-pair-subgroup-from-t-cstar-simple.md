---
rg: 2
id: thompson-t-disjoint-pair-subgroup-from-t-cstar-simple
kind: route
title: If Thompson's group T is C*-simple, T itself is a C*-simple subgroup with a disjointly supported pair
target: thompson-t-has-cstar-simple-subgroup-with-disjoint-pair
requires:
  - thompson-t-is-cstar-simple
---

Take `H = T`. `T` contains disjoint pairs: for instance two nontrivial elements of `F`
supported in the disjoint dyadic intervals `(1/8, 1/4)` and `(1/2, 3/4)`. Every dyadic interval
carries a nontrivial element of `F` supported inside it, e.g. a conjugate of `x_0 x_1^-1`
rescaled into that interval.

This route closes a cycle with `thompson-f-not-amenable-from-cstar-simple-disjoint-pair` and
`thompson-t-cstar-simple-from-f-not-amenable`, recording an equivalence; the cycle warning is
expected.
