---
rg: 2
id: de-la-salle-same-pvm-gate-audit
kind: route
title: Read the Pauli game through Fourier PVM semantics and the repeated-coordinate compiler
target: de-la-salle-pauli-game-starts-after-the-same-pvm-gate
requires:
  - quadratic-repetition-supports-complete-commutation-overlay
  - sparse-clifford-cycles-refute-average-commutator-rounding
---

Theorem 3.11 and Corollary 3.9 start with two primitive PVMs indexed by
`F_2^N`; Fourier transform makes each one an exact additive action before the
code-column test is applied.  Compare this with the group-word compiler:
quadratic coordinate repetition makes exact PVM semantics bounded-occurrence
and perfect-complete, but near satisfaction gives only approximate agreement
and average commutation.  The sparse Clifford cycle supplies an explicit
uniform obstruction to rounding from that latter datum alone.  Hence the
paper's Pauli conclusion is downstream of, not a proof of, the repeated-LDPC
same-PVM gate.
