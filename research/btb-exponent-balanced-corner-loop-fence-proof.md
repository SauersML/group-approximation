---
rg: 2
id: btb-exponent-balanced-corner-loop-fence-proof
kind: route
title: Tensor the Morita rectangular model with the inverse finite Weyl gauge
target: btb-balanced-loops-stop-at-same-object-reflection
requires:
  - mixed-steinberg-loops-admit-morita-rectangular-model
  - literal-prefix-three-root-swap-retains-typed-carriers
  - fixed-d8-holonomy-has-no-determinant-density
  - controlled-pauli-corner-has-clifford-groupification
---

Use the finite typed rectangular model for every multiplication triangle.
On a packet simple carrying phase `zeta`, tensor the two edge gauges with a
clock--shift Weyl pair carrying `zeta^(-1)`.  The outer and multiplicity
phases cancel, while the source and target object identities remain distinct
typed copies placed in the same ambient carrier.  Fixed-module block filling
gives the normalized-HS remainder estimate.  The support-reflection row is
not an associativity or scalar-projective identity and retains the
uncontrolled Clifford multiplicity involution, so it is exactly the first
row not realized by this model.
