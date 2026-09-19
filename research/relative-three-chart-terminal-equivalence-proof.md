---
rg: 2
id: relative-three-chart-terminal-equivalence-proof
kind: route
title: Apply the triangle colimit universal property in both directions
target: relative-three-chart-correction-is-km-regular-stability
requires:
  - triangle-colimit-llp-reduces-to-relator-local-splitting
  - kernel-section-builds-relative-p13-chart
  - simple-kazhdan-kac-moody-lattices-exist
---

Suppose first that the relative simultaneous correction assertion holds.
After using the ambient gauges to place the three corrected representations
on one Hilbert space, denote them by `rho_12,rho_13,rho_23`.  Their exact
agreement on every diagram arrow makes them a cocone from the finite-group
diagram to `U(D)`.  The defining universal property of the colimit gives a
unique homomorphism

```text
rho:Gamma->U(D)                                        (RTC2)
```

restricting to the three `rho_ij`.  The triangle vertex groups generate
`Gamma`, so the assumed generatorwise perturbation estimate is exactly the
global correction estimate.  Flexible dimension changes are identical on
both formulations.  This proves one implication.

Conversely, restrict any genuine correction `(RTC2)` to the three finite
vertex groups.  The restrictions agree literally on every overlap, preserve
the same flexible dimension, and inherit the global generatorwise estimate.
This proves the equivalence.

Finally, if one compatible vertex representation retains a nonzero regular
summand, some nonidentity element of that finite vertex group has nonidentity
image.  The glued representation `(RTC2)` is therefore nontrivial.  By
simplicity its kernel is trivial, so `Gamma` would embed in the finitely
generated linear group `rho(Gamma)`.  Malcev residual finiteness would make
`Gamma` residually finite, impossible for an infinite simple group.  Hence
the compatible regular zero set is empty, proving the final assertion.
