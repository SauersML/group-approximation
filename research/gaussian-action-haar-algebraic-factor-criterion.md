---
rg: 2
id: gaussian-action-haar-algebraic-factor-criterion
kind: claim
title: Gaussian action algebraization is exactly permutation containment
distinct_from:
  haar-algebraic-actions-have-permutation-koopman-spectrum: that supplies the necessary Koopman obstruction for every measurable factor; this proves necessity and sufficiency specifically for Gaussian actions.
  z-haar-algebraic-factors-have-lebesgue-plus-torsion-spectrum: that computes the spectral consequence for one transformation; this works for every countable acting group and gives an exact representation-theoretic criterion.
  algebraic-compact-action-envelope-for-non-ce-relation: that asks for a crossed-product embedding, possibly non-Cartan; this exactly decides only the proposed Gaussian action-factor route.
---

Let `Lambda` be countable and let `sigma_pi` be the Gaussian p.m.p. action
associated to a separable real orthogonal representation `pi` of `Lambda`.
The following are equivalent.

1. `sigma_pi` is a measurable factor of an automorphism action of `Lambda`
   on some compact second-countable abelian Haar group.
2. `pi` is unitarily contained in a countable real permutation
   representation `ell^2(I,R)` of `Lambda`.

Thus Gaussian compactification is neither a universal algebraic-envelope
device nor merely subject to a loose spectral test: permutation containment
is the exact gate.  For `Lambda=Z`, condition 2 is equivalent to the maximal
spectral type of the complexification of `pi` being dominated by circle Haar
measure plus atoms at roots of unity.
