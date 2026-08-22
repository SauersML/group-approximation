---
rg: 2
id: atlas-m2-scalar-refutation-proof
kind: route
title: Evaluate the four scalar frontiers on the regularized GL8 witness
target: atlas-m2-escape-kills-collision-only-scalars
requires:
  - atlas-multiplicity-two-packet-collision-hub-escape
  - atlas-q14-augmented-zero-set-has-x30-one-escape
---

The multiplicity-two witness route already passes from its literal matrices
to `Reg(G)` and proves that every packet context is exact regular, collision
is one, and the hub opcode is `lambda(h)` for an order-four element `h`.
Regular-character orthogonality gives `(M2S1)`.  Each Dirichlet summand and
each root energy is nonnegative, so the hub term alone gives `E_T>=1`, while
`x_23=1` gives `S>=2` and `(M2S2)`.  These values contradict the four stated
upper/readout claims at zero residual.

The recorded q14 value of the witness is nonidentity, which proves the scope
qualification.  The augmented finite-factor claim supplies the separate
q14-exact point with `x_30^2=1`, proving the universal-tracial fence without
asserting a finite-dimensional augmented escape.

