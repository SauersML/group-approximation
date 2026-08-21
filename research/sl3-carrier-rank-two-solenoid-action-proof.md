---
rg: 2
id: sl3-carrier-rank-two-solenoid-action-proof
kind: route
title: SNAG on the metabelian core and conjugation invariance of the trace
target: sl3-carrier-has-rank-two-solenoid-action
requires: []
---

**Part 1.**  The diagonal subgroup of `SL_3(Z[1/p])` is
`D = {diag(p^a, p^b, p^c) : a + b + c = 0} iso Z^2`, and it
normalizes each root subgroup `R_alpha = {e_alpha(r) : r in Z[1/p]}`
with `diag(d) e_(ij)(r) diag(d)^(-1) = e_(ij)((d_i/d_j) r)`, i.e.
multiplication by `p^(<alpha, x>)` where `<alpha, x> = a_i - a_j`.
The three positive roots give the pairings `(a - b)`, `(b - c)`,
`(a - c)`; any two are linearly independent on `Z^2`.  `U` is the
Heisenberg-type group `Z[1/p]^3` (two generators and their
commutator), and `Q = D ltimes U` is metabelian-by-abelian
(solvable), a subgroup of `Gamma`.  A unitary representation of
`Z[1/p]^3`-quotients decomposes by SNAG as a projection-valued
measure on the Pontryagin dual `hat(Z[1/p])^3`, each factor the
`p`-adic solenoid `Sigma_p`; conjugation by `x in D` implements the
dual automorphism scaling the `alpha`-coordinate by
`p^(<alpha, x>)`.  This is a `Z^2`-action by solenoid automorphisms
whose expansion data along the roots realizes two multiplicatively
independent directions.

**Part 2.**  Let `tau` be a trace of `Gamma` (or a trace of a group
containing `Gamma`, restricted).  The scalar spectral measure `mu` of
`tau|_U` is defined by `hat(mu)(u) = tau(u)` under the isomorphism of
`C^*(U)`-states with measures on the dual; conjugation invariance
gives `hat(mu)(x u x^(-1)) = tau(x u x^(-1)) = tau(u) = hat(mu)(u)`
for `x in D` — wait, invariance of the measure corresponds to
`hat(mu)(x u x^(-1)) = hat(mu)(u)`, and indeed both sides are values
of `tau` at conjugate group elements, equal by the trace property.
So `mu` is invariant under the `Z^2`-action of Part 1.  For the
regular trace, `hat(mu) = delta_e` on `U`, i.e. `mu` is joint Haar.
For a carrier trace over `delta_e` the same computation applies to
the restriction to `Gamma`, and by
`hnn-carrier-enemy-moment-splitting` the single-block moments couple
the letter to this measure only through scalars, so the leak's
interaction with `mu` sits in two-block words.

**Part 3.**  Immediate from Parts 1-2 and the statement of the
`SL_2` obstruction in `far-sector-is-solenoid-measure-rigidity`: the
missing second independent direction is present, so the invariant
measures relevant to the enemy live under a rank-two abelian action
of algebraic origin, the hypothesis class of higher-rank
measure-rigidity theory (Katok--Spatzier; Einsiedler--Katok--
Lindenstrauss), rather than under a single hyperbolic map.
