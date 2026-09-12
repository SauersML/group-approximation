---
rg: 2
id: finite-router-fine-prefix-return-firewall-proof
kind: route
title: Compare the coarse and fine Pauli Fourier traces in the regular representation
target: finite-router-fine-prefix-return-collapses-mark
requires:
  - selector-correlated-direct-power-router
  - one-coarse-to-fine-prefix-isometry-closes-the-reservoir
---

Expand the projections in `(RFR1)` in the finite subgroup algebra.  Every
nonidentity Pauli word has zero canonical group trace, so `q`, `e`, and `f`
have traces `1/2`, `1/4`, and `1/8`.  Trace invariance under unitary
conjugacy rules out `(RFR3)`, and
`||p-r||_2^2>=|tau(p)-tau(r)|` gives `(RFR7)`.

The balanced finite router removes its multiplicity unitary and supplies
the label reflection `(RFR5)`.  Substituting it and the coarse reflection
into the support row `(RFR6)` gives `J_x e J_x^*=f` on the selected corner,
so the same trace contradiction applies.  Therefore the router is a valid
local nonlinear compiler but cannot be welded to the Leavitt return by a
tracially functorial relation.

