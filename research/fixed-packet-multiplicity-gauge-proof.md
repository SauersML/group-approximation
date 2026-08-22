---
rg: 2
id: fixed-packet-multiplicity-gauge-proof
kind: route
title: Apply Schur's lemma and retain a nontrivial multiplicity root
target: fixed-packet-correction-retains-multiplicity-gauge
requires:
  - hadamard-selector-commutator-charges-two-path-leakage
---

# Apply Schur's lemma and retain a nontrivial multiplicity root

Two implementers of the same automorphism differ by an operator commuting
with the irreducible packet, so Schur's lemma gives `(FPG2)`.  Balanced words
cancel the multiplicity factor, while a torsion clause only restricts it to a
finite root.  Choosing a nontrivial permitted root gives the exact stationary
countermodel.  Packet averaging and spectral cuts act on the first tensor
factor and therefore leave this model unchanged.

