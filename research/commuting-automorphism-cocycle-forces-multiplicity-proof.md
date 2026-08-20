---
rg: 2
id: commuting-automorphism-cocycle-forces-multiplicity-proof
kind: route
title: Factor the stable letters by Schur's lemma and take determinants
target: commuting-automorphism-cocycle-forces-multiplicity
requires: []
---

Schur's lemma gives `rho(u)=U_alpha tensor P` and
`rho(v)=U_beta tensor Q` on `T tensor C^m`.  Commutation of `u,v` implies
`PQ=zeta^(-1)QP`.  Determinants give `zeta^m=1`, hence `r|m`.

Writing `m=qr+s`, use `q` exact `r`-dimensional Weyl blocks and repair only
the last `s<r` dimensions.  The normalized squared HS cost is `O(r/m)`, which
proves the stated limitation.

