---
rg: 2
id: native-sl3-commuting-involution-group-proof
kind: route
title: Map the finite native presentation onto the arithmetic coset lamp group
target: native-sl3-commuting-involution-group
requires:
  - exact-projective-codensity-has-a-uniform-trace-square-gap
---

Finite presentation is immediate from the finite presentation of `A`, one
new involution, the finitely many centralizer relators for `S_C`, and the one
commuting-conjugate relator.

Map the group to `(direct_sum_(A/C) C_2) rtimes A`, sending `c` to the lamp
at `C`.  Its stabilizer contains `C`, and distinct lamps commute.  Since
`hC!=C`, the marked word maps to the product of two distinct nonzero lamps;
hence it is nontrivial in the presented group.

For an exact finite-dimensional unitary representation `rho`, finite-
dimensional codensity gives `rho(C)'=rho(A)'`.  The centralizer relators put
`rho(c)` in the left side, hence it commutes with `rho(h)` and kills the
marked commutator.
