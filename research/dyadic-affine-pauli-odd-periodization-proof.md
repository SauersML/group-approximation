---
rg: 2
id: dyadic-affine-pauli-odd-periodization-proof
kind: route
title: Reduce a finite dyadic address table modulo one odd prime
target: dyadic-affine-pauli-patterns-have-odd-periodizations
requires: []
---

Enlarge the finite address set to contain every intermediate address occurring
in the prescribed word table.  Express each nonzero difference as
`u/2^v` and choose an odd prime `m` dividing none of the finitely many
nonzero numerators `u`.  Reduction in `F_m` is then well defined and
injective on the enlarged set.  Translation by one and dilation by two give
an equivariant quotient of `BS(1,2)` onto the finite affine group
`F_m rtimes <2>`.

On `(C^2)^(tensor m)` place Pauli `X_r,Z_r` at site `r` and identify their
centers as `J=-I`.  The affine group acts by genuine tensor-factor
permutations.  Equivariance preserves every declared address equality and
covariance relation, while injectivity preserves every declared inequality;
same-site Pauli and off-site commutation relations hold exactly.  The finite
semidirect product is therefore an exact marked realization of the whole
finite table.  No separation of unrelated actor words is asserted or needed.
