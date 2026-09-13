---
rg: 2
id: rips-complexes-of-planar-sets-are-wedges-of-spheres
kind: claim
title: "Every connected Rips complex of every subset of the plane is homotopy equivalent to a wedge of spheres"
distinct_from:
  rips-complexes-of-finite-planar-sets-are-wedges-of-spheres: that claim covers finite point sets only; this one covers every subset of the plane under both diameter conventions
---

For every `X ⊆ R^2` with the Euclidean metric and every `r > 0`, if the Rips
complex `R_r(X)` (simplices = finite subsets of diameter `≤ r`, or `< r`) is
connected, then it is homotopy equivalent to `∨_{i∈I} S^{n_i}` for some index
set `I` and dimensions `n_i ≥ 1`.

It implies `rips-complexes-of-finite-planar-sets-are-wedges-of-spheres`.

## Attempts

- Known cases (context, unverified in this graph): subsets of a circle
  (Adamaszek; Adamaszek–Adams give a point, an odd sphere, or a wedge of even
  spheres of one dimension). The fundamental group is free for finite planar
  sets (Chambers–de Silva–Erickson–Ghrist).
- No general mechanism is known beyond the fundamental group. A proof has to
  control higher homotopy; any argument that only uses the free fundamental
  group cannot suffice, since for example `S^1 × S^2` has fundamental group
  `Z` and is not a wedge. See the negative attempts on
  `some-finite-planar-set-has-a-non-wedge-rips-complex`.
