---
rg: 2
id: free-quotient-obstructs-flexible-uniform-rank-stability
kind: claim
title: A quotient onto F_2 obstructs flexible uniform rank-metric stability over every field
distinct_from:
  amenable-group-algebra-rank-stability-iff-rf: that is weak pointwise stability of an amenable group algebra; this is uniform group stability in invertible matrices over all pairs of group elements, and gives a negative theorem for groups with a free quotient.
  sofic-stable-implies-residually-finite: that concerns permutation actions in normalized Hamming distance; this concerns invertible matrices in normalized rank distance.
---

Let `Gamma` be a group admitting a surjection onto the rank-two free group
`F_2`. For every field `K`, `Gamma` is not flexibly uniformly
`K`-stable in the normalized rank metric.

More precisely, there are uniform `3/n`-representations

```text
phi_n : Gamma -> GL_n(K)
```

whose flexible normalized-rank distance from every genuine representation
`Gamma -> GL_N(K)` is at least

```text
1/6 - 1/(6n).
```

**ESTABLISHED 2026-08-31** by
[[bachner-free-quotient-rank-instability-citation]].
