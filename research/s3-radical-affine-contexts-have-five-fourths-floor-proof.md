---
rg: 2
id: s3-radical-affine-contexts-have-five-fourths-floor-proof
kind: route
title: Enumerate the four radical atoms and exhaust affine endpoint charts
target: s3-radical-affine-contexts-have-five-fourths-floor
requires:
  - six-generator-one-jump-router-has-s3-radical-atlas
  - robust-rank-one-endpoint-marginal-floor
---

In the `K=J=-1` sector the total commutator form is the standard three-Pauli
form.  Conjugation by the three `x_i` words makes the joint spectral atoms of
the two independent even-parity `z` words equitracial, giving `(RAF1)`.
Direct substitution of its four atoms into the three failure predicates gives
`(RAF2)--(RAF3)`.

For minimality, a nonconstant affine function on the four-element space `R`
has one of six truth tables.  The verifier enumerates four endpoint functions
and three pair-permutation transports, rejects degenerate atlases with an
empty failure context, and minimizes total failure count, maximum pointwise
count, spread, and word/transport complexity in that order.  Assertions
require a surviving atlas; the printed minimum is five and the displayed
identity-transport atlas attains it.
