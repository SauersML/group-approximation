---
rg: 2
id: clifford-word-groupification-proof
kind: route
title: Intersect the discrete Clifford monomials with first chaos and form the signed semidirect product
target: clifford-word-bogoliubov-groupification-is-signed-monomial
requires: []
---

In the `z=-1` corner, the image of a normal-form word of `Cl_I` is a sign
times `c_(i_1)...c_(i_k)` for a finite ordered subset.  Distinct subsets give
orthogonal vectors for the tracial inner product.  The intersection of this
word set with first chaos is therefore exactly `{+/-c_i}`.  Equation `(CBG5)`
proves necessity of `(CBG2)`.

Under `(CBG2)`, the representation identity for `pi` gives the cocycle law
for `epsilon(g,i)`, and direct substitution in `(CBG1)` proves `(CBG3)` is a
group action.  The `z=-1` corner of `L(Cl_I)` has precisely the Clifford
monomial trace and Bogoliubov covariance, proving `(CBG4)`.  Every finitely
generated subgroup of `Cl_I` lies in the finite Clifford group on finitely
many sites, so `Cl_I` is locally finite.  Standard permanence of soficity
under amenable extensions proves the final assertion.

