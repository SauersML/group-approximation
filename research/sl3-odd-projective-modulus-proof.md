---
rg: 2
id: sl3-odd-projective-modulus-proof
kind: route
title: Pass projective centrality to the ultraproduct and invoke odd-sector collapse
target: sl3-odd-correctable-sector-has-uniform-projective-modulus
requires:
  - odd-congruence-lambda-exact-sector-collapses
---

Assume a violating sequence.  Ambient presentation defect tending to zero
defines an exact ultraproduct representation `pi` of `Gamma`.  Generatorwise
closeness to the exact congruence representations makes its lattice
restriction Lambda-exact of level prime to `p` in the sense of the required
claim.

Projective subgroup energy tending to zero makes every commutator
`[U,pi(c)]` scalar.  Multiplication shows the scalars define a character of
`SL_3(Z)`, and perfectness kills it.  The required odd-sector theorem then
makes `U` commute with all of `pi(Gamma)`, contradicting positive energy at
`h`.

If no uniform modulus `(OCP3)` existed, choose for each `j` data with total
input at most `1/j` and output bounded below by a fixed epsilon after passing
to a subsequence.  The same ultraproduct contradiction proves the modulus.
