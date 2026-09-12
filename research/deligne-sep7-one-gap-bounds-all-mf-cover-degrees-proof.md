---
rg: 2
id: deligne-sep7-one-gap-bounds-all-mf-cover-degrees-proof
kind: route
title: Use phase Lipschitz continuity and the nearest point of each rational grid
target: deligne-sep7-one-gap-bounds-all-mf-cover-degrees
requires:
  - deligne-sep7-norm-parameter-closed-subgroup
  - deligne-sep7-all-cover-mf-radical-classification
artifacts:
  - research/artifacts/deligne-sep7-all-cover-mf-classification.md
---

The infimum of the finite-window maximal defect over all positive matrix
dimensions is `2 pi B`-Lipschitz in the circle parameter: this holds for
each tuple by the triangle inequality and hence for their infimum. It is
zero at every parameter in `P_op`. A gap at `theta_0` excludes the
full-circle alternative, so `P_op=(1/m)Z/Z` with `m` positive and even.
Choose its point nearest `theta_0`; its distance is at most `1/(2m)`.
The Lipschitz estimate gives `epsilon <= pi B/m`.

The classification prerequisite says that every MF degree divides `m`,
and hence is at most `m`. Alternatively use its entire `q`-point grid
and the same nearest-point estimate directly. If `B=0`, the identity
tuple has zero defect, contradicting the gap assumption.

Finally, if no finite window has a positive infimum at a fixed parameter,
choose tuples on the first `n` multiplication pairs with defect below
`1/n`, including `(e,e)`. This pair gives `||U_e-I||->0`; replacing
`U_e` by `I` costs `o(1)` on every fixed pair. Extend the other values
arbitrarily off these finite windows. A diagonal sequence is a point-norm
model at the parameter, proving the
contrapositive of the last assertion.
