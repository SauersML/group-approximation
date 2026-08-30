---
rg: 2
id: stw77-projectionwise-target-zero-map-proof
kind: route
title: Apply projectionwise proper infiniteness to every local model block
target: stw77-zero-maps-into-projectionwise-proper-targets
requires:
  - zero-dimensional-unital-maps-are-locally-fd
  - stw77-proper-support-models-force-oinfty-stability
---

For every finite subset of `phi(A)` and every tolerance,
`zero-dimensional-unital-maps-are-locally-fd` supplies a unital
finite-dimensional subalgebra `D subset B` approximating that subset.
Every minimal projection of `D` is nonzero, hence properly infinite in `B`
by hypothesis.  Thus every such `D` satisfies the exact support condition in
`stw77-proper-support-models-force-oinfty-stability`, which gives a unital
embedding

```text
O_infinity -> B_omega intersect phi(A)'.
```

This is O-infinity-stability of `phi`.
