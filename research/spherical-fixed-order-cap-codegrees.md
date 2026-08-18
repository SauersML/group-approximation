---
rg: 2
id: spherical-fixed-order-cap-codegrees
kind: claim
title: Every fixed-order intersection of distinct trace-separated spherical candidates has negligible relative density
artifacts:
  - research/trace-separation-sphere-distance-concentration.md
  - research/spherical-candidate-pairwise-codegrees.md
---

Fix `m>=2` and a finite tested word set.  For a normalized-HS unitary table in
dimension `d`, suppose distinct tested words have regular trace separation
`|tau(U_w^*U_w')|=o(1)`.  For a uniform input sphere point `x`, let

```text
a_j = U_(w_j) x,  j=1,...,m,
```

for `m` distinct tested words.  With probability `1-o_d(1)` over `x`, the
intersection of the `m` radius-one spherical caps centered at the `a_j` has
measure `o(p_d)`, where `p_d` is the measure of one radius-one cap; in fact the
ratio is exponentially small in `d`.

Consequently, after sampling a sufficiently large independent point cloud,
every fixed-order same-output codegree involving distinct word colours is
`o` of a one-colour degree outside `o(N)` roots, simultaneously over the
finite tested window.

This strengthens `spherical-candidate-pairwise-codegrees`: no new moment of
order `m` is needed.  Pairwise trace separation plus the exact quadratic-form
concentration already controls all fixed-order intersections.  It advances the
probabilistic half of `spherical-candidate-hypergraph-quasirandom`, but does
not by itself provide its divisibility package or the coupled matching theorem.
