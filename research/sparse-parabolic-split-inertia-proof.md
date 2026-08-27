---
rg: 2
id: sparse-parabolic-split-inertia-proof
kind: route
title: Extend the character over its split inertia group and induce the orbit model
target: sparse-parabolic-atom-has-split-inertia
requires:
  - surviving-leavitt-corona-character-has-infinite-parabolic-orbit
---

Write the group law in `N semidirect H` additively on `N`:

```text
(n,h)(m,k)=(n+h.m,hk).                                 (1)
```

If `h in H_chi`, then `chi(h.m)=chi(m)`.  Therefore

```text
chi_tilde((n,h)(m,k))
 =chi(n+h.m)
 =chi(n)chi(m)
 =chi_tilde(n,h)chi_tilde(m,k),                        (2)
```

which proves that `(SPI2)` is a character of `I_chi`.  In particular its
restriction to the stabilizer factor `H_chi` is trivial.  More generally,
for any unitary representation `sigma` of `H_chi`,

```text
(n,h) |-> chi(n)sigma(h)                               (3)
```

is a representation of `I_chi`.  This records the complete freedom of the
multiplicity gauge.

Induce `(SPI2)` from `I_chi` to `G`.  In the standard coset basis indexed by
`H/H_chi`, `N` acts diagonally by the orbit characters `h.chi`, while `H`
permutes those basis lines.  Thus every orbit atom is one-dimensional.  A
word returning the base atom belongs to `I_chi` and acts on that line by the
scalar `(SPI2)`.  Since `(SPI2)` is an honest character rather than a
projective representation, every commutator of returning words has scalar
`+1`.  Replacing `(SPI2)` by `(3)` tensors every atom with the same
multiplicity space and changes only the unconstrained stabilizer gauge.

Because `H` acts on `H/H_chi` by permutations, each actor word sends a
rank-one orbit atom onto exactly one rank-one orbit atom.  Two paths with the
same source and target are scalar multiples of the same one-dimensional
isometry, so their cross-Gram has modulus one rather than zero.  Path
multiplicity therefore does not manufacture orthogonal ranges on the target
atom.

For the literal infinitude witness, fix the upper-left root subgroup

```text
U={x_ij(r):r in L}~=(L,+).
```

In characteristic two every finitely generated subgroup of `(L,+)` is a
finite vector space over `F_2`.  Hence coefficients `r_1,...,r_s` generate a
group `U_0` of order at most `2^s`.  Restricting the preceding monomial
construction to the finite `U_0`-orbit gives finite permutation and diagonal
matrices satisfying exactly every covariance and return relation among this
fixed menu.  All nonzero orbit atoms have equal rank one.  This proves that
the infinite union of these finite orbit tables cannot, by itself, yield a
fixed finite rank or holonomy obstruction.

The established infinite-orbit theorem remains essential only to identify
the other regime: no one finite menu captures the full Leavitt coefficient
orbit.  Passing from one fixed menu to the whole orbit requires word radius
or packet size to grow, while an opposite-root actor leaves the normalizer
and destroys the character-atom permutation model.  Those are precisely the
two possibilities excluded from the scoped claim.
