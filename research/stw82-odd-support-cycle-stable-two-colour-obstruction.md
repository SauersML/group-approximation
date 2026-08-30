---
rg: 2
id: stw82-odd-support-cycle-stable-two-colour-obstruction
kind: claim
title: A uniformly thick odd support cycle obstructs every small indivisible two-colour perturbation
distinct_from:
  stw82-indivisible-order-zero-reuse-is-graph-colouring: that is the exact unperturbed chromatic theorem; this proves a quantitative obstruction stable under arbitrary perturbations and stage-dependent colourings.
  stw82-two-by-two-colour-reuse-quantitative-obstruction: that optimizes over the two matchings of two pairs of maps; this applies to an odd cycle of any length.
---

Let `phi_v:F_v->B`, for `v` in a finite set `V`, be cpc order-zero maps
from unital C*-algebras, and put `h_v=phi_v(1)`.  Suppose distinct vertices

```text
v_0,v_1,...,v_(2m)
```

form an odd cycle (indices modulo `2m+1`) with

```text
kappa=min_i norm(h_(v_i) h_(v_(i+1))) > 0.            (O1)
```

If maps `phi'_v` satisfy `norm(phi_v-phi'_v)<=delta` and can be assigned,
without splitting, to two global colours such that each same-colour direct
sum is cpc order zero, then

```text
delta >= kappa/2.                                     (O2)
```

The statement remains valid for a sequence of families, cycles, and
colourings which vary with the stage: a uniform lower bound on `kappa`
precludes perturbation error tending to zero.
