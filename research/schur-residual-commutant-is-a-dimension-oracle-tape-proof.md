---
rg: 2
id: schur-residual-commutant-is-a-dimension-oracle-tape-proof
kind: route
title: Evaluate the standard identity in the matrix commutant of the paid Pauli factor
target: schur-residual-commutant-is-a-dimension-oracle-tape
requires:
  - schur-flip-cells-expose-residual-matrix-tape
  - two-generator-amitsur-levitzki-dimension-oracle
---

The commutant equality in `(RMT1)` gives `(SAT1)`.  Polynomial evaluation
commutes with tensoring by the identity, and `(ALO3)` applied at dimension
`L` gives `(SAT2)`.  The inverse relation at instruction `L` would then read
`0=I`, so no finite residual factor realizes the whole countable tape.

