---
rg: 2
id: stw77-proper-support-model-stability-proof
kind: route
title: Centralize a finite packet in the exact model commutant
target: stw77-proper-support-models-force-oinfty-stability
requires:
  - stw77-fd-commutant-splitting-iff-proper-supports
  - oinfty-map-stability-is-central-isometry-splitting
---

Fix contractions `x_1,...,x_m in C` and `epsilon>0`.  Choose `D` as in the
claim with approximants `d_i in D` satisfying

```text
norm(x_i-d_i)<epsilon/2.
```

The finite-dimensional commutant theorem supplies orthogonal isometries
`s_0,s_1 in B intersect D'`.  Therefore

```text
norm([s_l,x_i])
 <= 2 norm(x_i-d_i)
 < epsilon                                      (l=0,1).
```

Thus the central-isometry defect vanishes on every finite subset of `C`.
The central-isometry characterization gives a unital embedding

```text
O_infinity -> B_omega intersect C',
```

which is O-infinity-stability of the inclusion.  A unital
nuclear-dimension-zero map has the required one-sided finite-dimensional
models by `zero-dimensional-unital-maps-are-locally-fd`; adding condition 2
gives the final assertion.
