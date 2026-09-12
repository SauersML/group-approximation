---
rg: 2
id: stabilizer-logical-quarter-turn-proof
kind: route
title: Quarter-turn one member of an anticommuting logical Pauli pair
target: stabilizer-checks-either-have-logical-shears-or-erase-payload
requires: []
---

For isotropic `R<=F_2^(2n)`, the usual stabilizer decomposition gives a
logical Pauli representation of the nondegenerate quotient `R^perp/R` on
the selected syndrome carrier.  If this quotient is nonzero, choose a
symplectic pair `ell,m`.  Their Pauli representatives commute with every
check and anticommute with each other.  Hence the quarter-turn about
`P(ell)` fixes all checks and sends `P(m)` to `iP(ell)P(m)`.  Conjugation by
the second logical Pauli makes the trace of `P(ell)` equal its negative, so
it is zero; expanding the squared normalized `2`-norm gives `(SCB4)`.

Nondegeneracy gives `dim(R^perp/R)=2(n-dim R)`.  Its vanishing is therefore
equivalent to a maximal isotropic stabilizer and a one-dimensional selected
carrier in the irreducible Pauli packet.  Tensor multiplicity is untouched
by all checks, proving the final reservoir statement.

