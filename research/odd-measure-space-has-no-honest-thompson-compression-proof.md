---
rg: 2
id: odd-measure-space-has-no-honest-thompson-compression-proof
kind: route
title: Integrate the translated pieces against the invariant Haar measure
target: odd-measure-space-has-no-honest-thompson-compression
requires: []
artifacts:
  - research/artifacts/ternary-lift-signed-thompson-crossed-product-2026-09-12.md
---

**Haar measure.**
* `V` acts on the compact group of `F_2`-measures by continuous group automorphisms, so it preserves
  normalized Haar measure and the coset `M_-`.
* On a finite partition `P`, the image of `lambda` is uniform on the odd vectors of `F_2^P`.
  Basic clopens have positive measure, and `lambda(mu(C) = 1) = 1/2`.

**No compression.** `lambda(U) >= sum lambda(g_i A_i) = sum lambda(A_i) = 1`. So `M_- \ U` is a
null clopen set, hence empty.

**The partial isometry.** For `v = sum [g_i] 1_(A_i)` with disjoint images, the cross terms
`[g_i^-1] 1_(g_i A_i cap g_j A_j) [g_j]` vanish. So `v* v = 1` and `v v* = 1_(union g_i A_i)`.

**The naive lift.** Pointwise in `(mu(00), mu(01))` one checks
`1_(U_00) + 1_(U_01) - 1_(U_0) = 2 . 1_(U_00 cap U_01)`.

Proposition 4 of the artifact.
