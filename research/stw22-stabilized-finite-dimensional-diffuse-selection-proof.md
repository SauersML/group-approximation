---
rg: 2
id: stw22-stabilized-finite-dimensional-diffuse-selection-proof
kind: route
title: Choose the finite weighted sphere degree dictated by the base dimension
target: stw22-finite-dimensional-diffuse-factor-bundles-have-uniform-traces
requires:
  - stw22-dim1-factor-bundles-have-uniform-traces
  - stw22-diffuse-weighted-copy-all-finite-sphere-fillings
  - stw22-tracefree-fibre-gap-ideals-force-trace-continuity
artifacts:
  - research/artifacts/stw22-diffuse-all-degree-induction-audit-2026-08-31.md
---

Let `D=dim(K)<infinity`. Stabilization gives the type-free complete ambient
Hilbert space, nonempty closed lower-semicontinuous weighted-copy values,
and operator-ball recovery. Countable generation makes all diffuse fibres
separable-predual.

For `D>=1`, apply the weighted theorem in degree `D-1`. Its values are
`(D-1)`-connected and equi-`LC^(D-1)`, so Michael with index `D-1`
selects exact globally slack copies over `K`. The case `D=0` uses
nonemptiness and zero-dimensional selection. Operator-ball recovery returns
the tuple to `M`.

The standard spectral cut, central cutoff, and arbitrary-`m` replication
give `m sigma([c])<=||sigma||` for every bounded positive gap trace.
Letting `m->infinity` and then removing the cut proves (AD-6).