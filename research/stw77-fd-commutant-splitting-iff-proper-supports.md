---
rg: 2
id: stw77-fd-commutant-splitting-iff-proper-supports
kind: claim
title: A finite-dimensional relative commutant splits exactly when every minimal support is properly infinite
artifacts:
  - research/artifacts/stw77-map-oinfty-audit-2026-08-30.md
distinct_from:
  projection-return-models-force-central-splitting: that uses closeness to image elements to prove proper infiniteness of model projections; this characterizes the finite-dimensional commutant directly and needs no projection return.
---

Let `D subset B` be a unital finite-dimensional C*-subalgebra.  Write

```text
D=direct_sum_(j=1)^r M_(n_j)
```

and choose one minimal projection `p_j` in each simple summand.  The following
are equivalent.

1. `B intersect D'` contains two isometries with orthogonal ranges.
2. Every `p_j` is properly infinite in `B`.

The second condition is independent of the chosen minimal projection in each
summand.  Thus finite-dimensional model commutation has one exact obstruction:
a block whose minimal support is not properly infinite.
