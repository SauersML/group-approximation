---
rg: 2
id: berend-locally-closed-primitive-dimension-is-two
kind: claim
title: Every locally closed Hausdorff Berend primitive stratum has dimension at most two, sharply
distinct_from:
  berend-primitive-spectrum-has-one-faithful-generic-point: that identifies the primitive points and the generic point; this computes the supremal covering dimension of all locally closed Hausdorff primitive strata.
  stw99-lxxxvi-berend-groups-decomposition-rank: that asks whether decomposition rank is infinite; this proves that ordinary primitive-space dimension remains equal to two and cannot supply such a lower bound.
artifacts:
  - research/artifacts/stw99-lxxxvi-berend-frontier-2026-08-30.md
---

Let `A = C(T^3) ⋊ Z^2` be the Berend crossed product.  Every closed
subset of `Prim(A)` which omits the generic point `0` is a finite union of
closed subsets of finite-orbit two-torus strata.  Every nonempty open
subset of `Prim(A)` contains `0`.

Consequently, if `S subset Prim(A)` is locally closed and Hausdorff, then

`dim(S) <= 2`.                                                   `(BLH1)`

The bound is attained by the closed copy of `T^2` associated to any finite
orbit.  Thus the locally-closed Hausdorff primitive dimension of `A` is
exactly two.

This is a no-go for a soft topological proof of infinite decomposition
rank.  All ordinary Hausdorff pieces of the primitive spectrum have the
same finite dimension as the proper quotient models.  The unresolved
information is entirely in their non-Hausdorff accumulation at `0`.
