---
rg: 2
id: sl3-depth-two-clifford-orbit-enumeration-proof
kind: route
title: Exhaust the mod-four adjoint module under elementary conjugations
target: sl3-depth-two-clifford-fiber-has-thirty-six-types
requires:
  - depth-two-clifford-types-form-a-finite-fiber-folner-graph
---

The script `experiments/sl3_mod4_adjoint_orbits.py` encodes a traceless
matrix by its six off-diagonal entries and two independent diagonal entries,
giving exactly `4^8` codes.  It conjugates by the six elementary matrices
`x_ij(1)` and exhausts every orbit by breadth-first search.  These matrices
generate `SL_3(Z/4Z)`, so the resulting connected components are precisely
the adjoint orbits.  The script visits every one of the `65536` codes once
and returns the distribution `(CT36-2)`; its weighted sum independently
checks the enumeration.

Because `3` is invertible modulo `4`, the trace form on
`sl_3(Z/4Z)` is nondegenerate.  It equivariantly identifies adjoint and
coadjoint orbit sets, proving the claimed Clifford-type classification.

