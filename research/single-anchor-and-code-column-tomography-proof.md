---
rg: 2
id: single-anchor-and-code-column-tomography-proof
kind: route
title: Apply bicommutants and diagonalize code-column conjugations in the Pauli basis
target: single-anchor-cannot-pin-pauli-gauge
requires: []
---

The single-anchor proof is purely algebraic.  The stabilizer of an anchor
family is the unitary group of its commutant.  Equality of that stabilizer
with the unitary group of `A'` gives equality of the two finite-dimensional
von Neumann algebras, and taking commutants gives `(SAP2)`.

For `(SAP3)`, write

```text
Y=sum_(a,b in F_2^n) X(a)Z(b) tensor Y_(a,b).
```

Normalized-HS orthogonality makes the squared distance to `A'` equal
`sum_((a,b)!=(0,0))||Y_(a,b)||_2^2`.  Conjugation by `X(s)` multiplies the
`(a,b)` coefficient by `(-1)^(s.b)`, so its averaged commutator energy is

```text
2(1-E_s (-1)^(s.b)) ||Y_(a,b)||_2^2.
```

For `b!=0`, the spectral-gap hypothesis makes this at least
`(2/c)||Y_(a,b)||_2^2`.  The `Z` calculation gives `2/c'` when `a!=0`.
Summing proves `(SAP3)`.

Finally, commutation of Pauli labels is the standard nondegenerate
symplectic form on `F_2^(2n)`.  Fewer than `2n` labels have a nonzero
symplectic-orthogonal vector.  Its Pauli operator is an exact gauge invisible
to all the anchors, proving the lower bound.

