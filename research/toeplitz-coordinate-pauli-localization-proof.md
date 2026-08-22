---
rg: 2
id: toeplitz-coordinate-pauli-localization-proof
kind: route
title: Apply the coordinate Pauli expectation and commute the compressed Gram
target: toeplitz-coordinate-paulis-localize-relative-cells-and-grams-polynomially
requires:
  - toeplitz-head-jacobi-words-give-uniform-expanders
  - pauli-generator-average-has-inverse-linear-gap
  - fixed-pauli-pair-hs-rounding
artifacts:
  - research/artifacts/toeplitz-coordinate-pauli-gram-localization-2026-08-21.md
---

Use only the nested Pauli heads and polynomial derivations supplied by the
first prerequisite, not its Clifford normalizer channel.  The coordinate
Pauli expectation places a new pair in the old commutant with `sqrt(n)`
loss; fixed-pair rounding finishes the relative cell.

For the Gram statement, support commutation gives
`[X,W]=(E-H)[U,W]E`.  Expanding `[X^*X,W]` gives the factor two in `(TCP8)`,
and the same coordinate expectation proves `(TCP11)`.
