---
rg: 2
id: taller-vidick-uniform-rank-pressure-return
kind: route
title: Replace noisy three-XOR rejection by one uniform Clifford rank bit
target: multiplicity-return-transducer
requires:
  - taller-vidick-lcs-re-hardness
  - three-xor-violation-is-one-clifford-rank
  - finite-schur-clifford-packet-flexible-hs-exactification
  - finite-group-multiplicity-mismatch-pays-hs-energy
  - uniform-three-xor-rank-return
---

Apply the Taller--Vidick reduction to a fixed tracial/non-embeddable BCS
source, using the same algebraic honest strategy in the tracial tensor power.
Do not demand that its noisy three-XOR output equations hold.  Instead attach
the uniform packet `(TXR1)` to every equation.  The controlled Pauli lift is
exact on every honest joint spectral atom, including atoms on which the random
mask makes the XOR check fail, so imperfect completeness no longer kills the
marked tracial model.

For finite-dimensional profiles, the Taller--Vidick soundness gap forces a
positive average mass of failed three-XOR checks.  Those failures are exactly
the rank-jump sectors of `(TXR1)`.  Packet exactification, the uniform return
`(UXR1)`, and finite-group multiplicity payment then turn this mass into a
constant normalized-HS floor.

This route removes three burdens from the Fanizza lane: arbitrary nonlinear
predicate groupification, recurrence with runtime-dependent polynomial
certificates, and fresh selector installation between tape levels.  It does
not remove the global return theorem or the need to prove that the chosen
tracial source mark survives the full incidence.
