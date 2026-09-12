---
rg: 2
id: character-hnn-and-holonomy-proof
kind: route
title: Compare common-edge covariance with the two-edge relative stable word
target: character-hnn-retains-and-or-holonomy
requires:
  - finite-character-idempotents-have-exact-hnn-transport
  - agent-free-compressor-chart-edge-has-multiplicity-gauge
  - positive-cross-gram-mass-alone-has-no-holonomy-floor
---

Conjugate the two controlled covariance equations and their commutator by a
single stable letter to obtain `(CHH1)--(CHH2)`.  Omitting the packet removes
the tensor-factor typing by the multiplicity-gauge theorem.  For two stable
letters, composing one transport with the adjoint of the other gives
`(CHH3)`; the same theorem leaves that commutant unitary arbitrary, and the
cross-Gram firewall shows scalar overlap does not control it.  These exhaust
the common-edge and separate-edge character-transport constructions.
