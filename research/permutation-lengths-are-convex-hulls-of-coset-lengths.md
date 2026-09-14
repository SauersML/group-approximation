---
rg: 2
id: permutation-lengths-are-convex-hulls-of-coset-lengths
kind: claim
title: Every Hamming length of a finite group action is a convex combination of coset-action lengths
distinct_from:
  regular-action-makes-weak-sofic-defects-maximal: that computes one action's Hamming length and draws the transport consequence; this describes the whole cone of achievable Hamming lengths on a finite group and turns the chart question into a linear program over the subgroup lattice.
  weakly-sofic-groups-are-surjunctive: that is the open dynamical conclusion; this is the exact description of the data a counting proof may draw on.
artifacts:
  - research/artifacts/weak-soficity-surjunctivity-route-2026-09-12.md
---

Let `H` be a finite group. For a finite `H`-set `V` write
`l_V(z) = 1 - fix(z)/|V|`, and for `L <= H` write `l_{H/L}` for the length of
the left coset action. Then

```text
l_V = sum_i ( |H/L_i| / |V| ) l_{H/L_i} ,
```

the sum running over the orbits of `V`, with `L_i` a point stabilizer of the
`i`-th orbit. The coefficients are nonnegative and sum to `1`. So the lengths
arising from finite `H`-sets are exactly the convex combinations of the coset
lengths `l_{H/L}`, `L <= H`.

**Consequence for the counting route.** By Section 1 of the artifact, a
Gromov--Weiss transport of a cellular automaton along a weakly sofic
approximation `(H, l, phi)` needs a finite `H`-set `V` with `l_V` small on the
multiplicative defects and bounded below on `phi(F \ {1})`. By the displayed
decomposition, the search for `V` is a linear program over the subgroup lattice
of `H`: find a probability vector `(lambda_L)` with

```text
sum_L lambda_L l_{H/L}(k)      <= delta      for every defect k,
sum_L lambda_L l_{H/L}(phi(g)) >= c'         for every g != 1 in F.
```

The two ends of the lattice are the two failures already recorded. At `L = 1`
the coset length is discrete, so it is maximal on defects, which is
`regular-action-makes-weak-sofic-defects-maximal`. At `L = H` it is identically
zero, so it separates nothing. A chart system exists exactly when some
intermediate mixture separates the images of `F` while nearly fixing the
defects, and the dual of that program is where a proof or a refutation of
`weakly-sofic-groups-are-surjunctive` has to live.

Nothing here asserts that such a mixture exists or fails to exist. It replaces
a search over all finite `H`-sets by a search over subgroups, and it shows the
given bi-invariant length `l` enters only through which elements it certifies
as defects and which as separated.
