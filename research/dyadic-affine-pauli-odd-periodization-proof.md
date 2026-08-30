---
rg: 2
id: dyadic-affine-pauli-odd-periodization-proof
kind: route
title: Reduce the finite address set modulo an avoiding odd prime
target: dyadic-affine-pauli-patterns-have-odd-periodizations
requires: []
---

Let `F` be the finite set of dyadic addresses named by the table.  Write each
nonzero difference of two elements of `F` as `u/2^v` with nonzero integer
`u`.  Choose an odd prime `p` dividing none of these finitely many numerators.
Because `2` is invertible modulo `p`,

```text
rho_p(n/2^s)=n 2^(-s) mod p
```

is well defined; the choice of `p` makes it injective on `F`.

Let `ell` be the multiplicative order of `2` in `(Z/pZ)^*`.  Translation by
one and multiplication by two generate the finite affine group

```text
A_p=(Z/pZ) semidirect <2>,
```

and satisfy `t a t^(-1)=a^2`.  Thus `A_p` is a finite quotient of the
dyadic affine group, and reduction modulo `p` intertwines every affine address
operation appearing in the finite table.  Injectivity preserves every named
equality and inequality of sites.

For each site `x in Z/pZ`, take Pauli generators `X_x,Z_x` with one common
central involution `J`, imposing

```text
[X_x,Z_x]=J,       [X_x,X_y]=[X_x,Z_y]=[Z_x,Z_y]=1
```

when `x!=y`.  This is a finite central product of `p` copies of the order-eight
Pauli group.  The affine group permutes its site indices, giving a finite
semidirect product.  On `(C^2)^(tensor p)`, let `X_x,Z_x` be the usual Pauli
matrices on tensor factor `x`, let `J=-I`, and implement affine permutations
by the corresponding tensor-factor permutation unitaries.  These matrices
satisfy the central-product and covariance relations exactly.

Pull the given finite table through `rho_p` and this tensor-Pauli model.
Affine covariance, same-site Pauli relations, off-site commutation, and all
declared site equalities or inequalities are exact, while the marked center
remains `-I`.  Hence every table in the stated class has an exact finite
odd-periodic realization, proving the claim.
