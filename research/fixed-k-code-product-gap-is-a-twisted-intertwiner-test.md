---
rg: 2
id: fixed-k-code-product-gap-is-a-twisted-intertwiner-test
kind: claim
title: The conjugation gap of a fixed-K code product is a finite twisted-intertwiner distance test
distinct_from:
  complete-overlay-code-group-has-uniform-conjugation-gap: that treats the purely abelian group and obtains gap directly from code distance; this identifies the extra finite set of K-twisted sectors.
  uniform-conjugation-kazhdan-gap-gives-face-hamiltonian-gap: that transfers an assumed group gap to face pinchings; this computes the group gap for a proposed direct-product model.
---

Fix a finite group `K`.  Let

```text
g_i=(k_i,a_i) in K x A,       A=F_2^r,       1<=i<=L,
```

be involutions generating the direct product.  Every unitary representation
decomposes into irreducible sectors `(rho,chi)`, where `rho` is an irrep of
`K` and `chi` a character of `A`.  On the Hilbert-Schmidt block from
`(sigma,psi)` to `(rho,chi)`, the normalized conjugation energy is

```text
(1/L)sum_i ||rho(k_i)T-(-1)^(u_i)T sigma(k_i)||_2^2,
u_i=(chi+psi)(a_i).                                      (FKG1)
```

Consequently the normalized conjugation gap is exactly the minimum of
`(FKG1)` over the finitely many pairs `(rho,sigma)`, nonzero matrices `T`,
and codewords `u` arising from character differences, excluding the genuine
commutant sectors.

This yields a finite-dimensional design criterion.  Because `K` is fixed,
all matrix sizes in `(FKG1)` are bounded.  A uniform gap follows if the
empirical labeled columns `(k_i,a_i)` stay a fixed distance from every zero-
energy twisted intertwiner pattern.  Ordinary code distance proves this only
for `rho=sigma=1`: then `(FKG1)` is four times the relative weight of `u`.
For nontrivial `K` sectors, the signs of a codeword can cancel a one-
dimensional twist or more general intertwiner pattern.  Those finitely many
patterns must be excluded explicitly; repeating K labels at positive density
alone is not sufficient.

Thus there is no spectral obstruction to a fixed-K product construction,
but its correct hypothesis is a finite **twisted code-distance** condition,
not merely classical distance plus a Cayley gap in `K`.
