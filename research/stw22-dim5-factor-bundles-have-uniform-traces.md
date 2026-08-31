---
rg: 2
id: stw22-dim5-factor-bundles-have-uniform-traces
kind: claim
title: Countably generated factorial bundles over five-dimensional bases have only uniform traces
distinct_from:
  stw22-dim4-factor-bundles-have-uniform-traces: that theorem uses degree-three half-slack selection; the present theorem adds degree four.
  stw22-full-fundamental-group-trivial-bundles-finite-dimensional: that theorem is all-degree for one fixed full-fundamental-group fibre; the present theorem permits arbitrary nontrivial mixed finite-factor bundles through dimension five.
artifacts:
  - research/artifacts/stw22-dim5-factor-bundle-breakthrough-2026-08-31.md
---

Let `K` be compact Hausdorff with `dim(K)<=5`, and let `(M,E)` be a
factorial tracially complete C-star algebra over `K`. If its uniform
`2`-norm Hilbert `C(K)`-module completion is countably generated, then
every bounded positive trace on every fibre gap vanishes and

```text
T(M)={a |-> integral_K tau_x(a_x) dmu(x):
      mu a Radon probability measure on K}.            (AF5-4)
```

Thus every trace is uniform-`2`-norm continuous. Fibre type and matrix
size may vary arbitrarily; no common ambient factor, local triviality,
hyperfiniteness, property Gamma, or metrizability of `K` is assumed.