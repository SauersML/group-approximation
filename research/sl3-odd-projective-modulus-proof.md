---
rg: 2
id: sl3-odd-projective-modulus-proof
kind: route
title: Pass projective centrality to the ultraproduct and invoke odd-sector collapse
target: sl3-odd-correctable-sector-has-uniform-projective-modulus
requires:
  - odd-congruence-lambda-exact-sector-collapses
  - unbalanced-torus-extracts-near-central-denominator-coordinate
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

For the direct bound `(OCP4)`, an exact lattice representation of congruence
level `N` coprime to `p` extends in the same dimension to `Gamma` through
reduction modulo `N`.  Apply the second required claim to that extension.
Fixed-word telescoping changes source projective energy by `O(xi)`.  It
bounds the unbalanced torus-word defect and every overlap conjugacy defect
by `O(delta+xi)`.  Substitution in `(NCD2)` gives

```text
e(U,rho(h))<=K_odd(q+xi+(delta+xi)^2),
```

with one constant independent of dimension, level, and multiplicity.
