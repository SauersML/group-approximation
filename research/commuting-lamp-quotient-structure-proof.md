---
rg: 2
id: commuting-lamp-quotient-structure-proof
kind: route
title: Kill the sign and coordinatize the telescope coset space
target: commuting-lamp-quotient-structure
requires: []
artifacts:
  - notes/COMMUTING_LAMP_QUOTIENT_STRUCTURE_AND_MF_FORK_2026-08-14.md
---

## Direct proof

`zeta` is central and lies in the lamp kernel, so the quotient splits as
`(ClLamp(X)/<zeta>) semidirect V`, and the Clifford presentation modulo the
sign is the presentation of the elementary abelian `2`-group on the basis
`X`; distinctness of sites survives because a finite Clifford subgroup on
`|F|` sites has order `2^{|F|+1}`.

For the coordinates, the `tau`-exponent gives `level : X -> Z` with fibre
`T/Gbar_{-n}`, and `SL_3(Z)` preserves `2^n Z^3`, so
`(v,A)Gbar_{-n} |-> v + 2^n Z^3` is a bijection onto `Z[1/2]^3/2^n Z^3`
intertwining the affine action.  Rescaling by `y = 2^{-n} w` normalizes every
fibre to `(Z[1/2]/Z)^3` and turns the translation action at level `n` into
translation by `2^{-n} v`; `tau` doubles representatives and shifts the
level, hence acts as the identity in the rescaled coordinate.  Section 2 of
the cited note carries out both computations.
