---
rg: 2
id: atlas-three-label-mode-rotation-common-root
kind: route
title: Solve the order-one rotation common-root equations for the three-label Atlas slice
target: binary-leavitt-unit-group-hyperlinear
requires:
  - atlas-order-one-weyl-atlas-is-one-laurent-common-root-test
---

For every literal relator `s in bar_S`, form the Laurent polynomial
`f_s(z)` in `(OWA4)` by retaining the exponent-balanced two-unitary moments
in the exact three-label expansion.  Compute the gcd/zero set of the finite
family

```text
f_s(z)-1,       s in bar_S,                            (OWR0)
```

and test its intersection with the unit circle away from `z=1`.

Any common root `z!=1` compiles, through rational Weyl approximants whose
orders tend to infinity, to full-coefficient regular-A8
microstates killing the canonical packet.  This proves the explicit nonsofic
binary Leavitt unit group hyperlinear.  Conversely, no order-one Weyl model
on this three-label slice can work unless `(OWR0)` has such a root.

The route is finite and symbolic once the fixed literal packet is expanded;
it requires no increasing-dimensional optimization.  The point `z=1` is the
small-phase commutative wall.  Roots of unity different from one must remain
in the search: approaching one through primitive phases of growing order is
not the same as using its one fixed finite-dimensional irreducible Weyl
representation.
