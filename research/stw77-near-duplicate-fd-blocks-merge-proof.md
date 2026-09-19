---
rg: 2
id: stw77-near-duplicate-fd-blocks-merge-proof
kind: route
title: Collapse each near-duplicate cluster to its diagonal copy
target: stw77-near-duplicate-fd-blocks-merge
requires:
  - stw77-fd-commutant-splitting-iff-proper-supports
---

For each cluster form the diagonal copy of its matrix algebra and set

```text
E={sum_C sum_(j in C) sigma_(C,j)(y_C):
   y_C in M_(n_C)} subset D.
```

This is a unital finite-dimensional subalgebra of `B`. One minimal projection
in its `C`-summand is exactly `p_C`, so every minimal support of `E` is
properly infinite. By
`stw77-fd-commutant-splitting-iff-proper-supports`, `B intersect E'` contains
isometries `s_1,s_2` with orthogonal ranges.

Replace the coordinates of `x_l` in cluster `C` by the transported reference
coordinate and call the resulting element `y_l`. Then `y_l in E` and
`||x_l-y_l||<=delta`, because the norm on a finite direct sum is the maximum
of the coordinate norms. Hence

```text
||[s_t,x_l]||
 <= ||[s_t,y_l]||+2||x_l-y_l||
 <= 2 delta.
```

This proves the claim.
