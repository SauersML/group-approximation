---
rg: 2
id: sofic-model-via-unistochastic-dephasing
kind: route
title: Dead — square the entries, Birkhoff-decompose, and read off permutations
target: hyperlinear-implies-sofic
requires: []
---

**Dead.**  Recorded as an attempt; the kill is
`dephasing-destroys-multiplicativity`, which carries the `invalidates` key.

The attempt: send each microstate unitary `U_g` to its unistochastic matrix
`P_g(i,j) = |(U_g)_{ij}|^2`, which is doubly stochastic; write each `P_g` as a
convex combination of permutation matrices (Birkhoff); sample one permutation
per generator; and argue that the group-law defect of the sampled permutations
is controlled by the HS defect of the unitaries.

Where it dies: at the last step, and not for a quantitative reason.  Dephasing
is not multiplicative — `P_{UV} ≠ P_U P_V`, with a two-by-two Hadamard witness
— so the sampled permutations have no relation to the table at all; the map
that was supposed to transport the relations destroyed them before the
sampling.  Passing to tensor powers does not help, since the same failure is
inherited copy by copy.

The residue is a design rule for the live routes: classicalization must come
*after* the multiplication constraints have been imposed on coherent
path-amplitude data, never before.
