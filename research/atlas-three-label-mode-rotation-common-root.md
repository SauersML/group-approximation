---
rg: 2
id: atlas-three-label-mode-rotation-common-root
kind: route
title: Solve the order-one rotation common-root equations for the three-label Atlas slice
target: binary-leavitt-unit-group-hyperlinear
requires:
  - atlas-order-one-weyl-atlas-is-one-laurent-common-root-test
  - atlas-three-mode-balanced-area-coefficient-table
---

For every literal relator `s in bar_S`, form the Laurent polynomial
`f_s(z)` in `(OWA4)` by retaining the exponent-balanced two-unitary moments
in the exact three-label expansion.  Compute the gcd/zero set of the finite
family

```text
f_s(z)-1,       s in bar_S,                            (OWR0)
```

and test its intersection with the non-torsion part of the unit circle.

Any non-torsion common root compiles, through rational Weyl approximants whose
orders tend to infinity, to full-coefficient regular-A8
microstates killing the canonical packet.  This proves the explicit nonsofic
binary Leavitt unit group hyperlinear.  Conversely, no order-one Weyl model
on this three-label slice can work unless `(OWR0)` has such a root.

The route is finite and symbolic once the fixed literal packet is expanded;
it requires no increasing-dimensional optimization.  Roots of unity are
excluded by the faithful canonical trace and finite-dimensional fibers of the
rational rotation algebra, not by substituting one fixed irreducible Weyl
trace.  The latter shortcut is invalid because extra exponent classes survive
modulo the fixed order.

The exact missing input is tracked by
`atlas-three-mode-balanced-area-coefficient-table`.  The repository contains
generators and verification scripts for the 4,648 words but not the cited
merged JSON artifact and not the balanced-area Laurent coefficients.
