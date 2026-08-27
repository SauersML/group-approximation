---
rg: 2
id: taller-vidick-uniform-rank-pressure-return
kind: route
title: Replace noisy three-XOR rejection by one uniform Clifford rank bit
target: multiplicity-return-transducer
requires:
  - oracularizable-tracial-source-gives-affine-rank-pressure
  - finite-schur-clifford-packet-flexible-hs-exactification
  - finite-group-multiplicity-mismatch-pays-hs-energy
  - uniform-affine-lcs-rank-return
---

Start from the exact tracial local packet model and uniform finite-dimensional
rank pressure supplied by
`oracularizable-tracial-source-gives-affine-rank-pressure`.  Its controlled Pauli
lifts include parity failures and Alice--Bob consistency failures, so
imperfect completeness no longer kills the marked tracial model and no common
classical assignment is assumed.

For finite-dimensional profiles, `(TAP3)` forces a positive average mass of
affine failure bits.  Those failures are exactly the rank-jump sectors of
`(TXR1)`.  Packet exactification, the uniform return `(UAR1)`, and finite-group
multiplicity payment then turn this mass into a constant normalized-HS floor.

This route removes three burdens from the Fanizza lane: arbitrary nonlinear
predicate groupification, recurrence with runtime-dependent polynomial
certificates, and fresh selector installation between tape levels.  It does
not remove the global return theorem, Alice--Bob overlap transport, or the need
to prove that the chosen tracial source mark survives the full incidence.
