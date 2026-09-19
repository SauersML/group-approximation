---
rg: 2
id: schur-pauli-words-name-atomwise-half-quarter-flags-proof
kind: route
title: Balance the relative and baseline Pauli cuts by their conjugate flips
target: schur-pauli-words-name-atomwise-half-quarter-flags
requires:
  - every-forbidden-atom-has-fixed-schur-pauli-words
  - predicate-rank-gate-doubles-restriction-multiplicity
---

On a forbidden selector atom the named relative pair generates a copy of
`M_2` in the commutant of the baseline packet.  Its `X_a` word conjugates
`Z_a` to `-Z_a`, so the two `Z_a` spectral projections have equal trace.
The chosen baseline `X_0` commutes with the relative factor and conjugates
`Z_0` to `-Z_0`; it therefore exchanges the two `Z_0` spectral cuts inside
each fixed `Z_a` cut.  This proves the half and conditional-half trace
identities in `(SPF3)`.  Fixed packet exactification transports the finite
word functional calculus with its existing dimension-independent modulus.

