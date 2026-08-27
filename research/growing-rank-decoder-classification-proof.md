---
rg: 2
id: growing-rank-decoder-classification-proof
kind: route
title: Pass between rank approximations and the rank ultraproduct and compare the two inverse defects
target: growing-rank-decoder-is-linear-soficity
requires: []
artifacts:
  - research/artifacts/matrix-cyclotomic-lift-and-rank-decoder-audit-2026-08-21.md
---

## Direct proof

Quotienting `product_n M_(d_n)(k)` by sequences of normalized rank tending to
zero turns the maps `theta_n` into a unital algebra homomorphism.  Positive
rank retention is exactly injectivity.  The converse follows by choosing
coordinate representatives on each finite-dimensional word space and
diagonalizing the finite demands.  This is the approximation/ultraproduct
equivalence in the definition of a linear-sofic algebra.  Restricting a
unital algebra embedding to the group-basis units gives a linear-sofic group
embedding.  For `k=C`, the converse is Theorem 1.2 (Corollary 7.7 in the body)
of Arzhantseva--Paunescu, *Linear sofic groups and algebras*.  That converse
is not asserted here for arbitrary `k`.

For square matrices over any field,

```text
dim ker(I-AB) = dim ker(I-BA).
```

Indeed `B` maps the first kernel injectively into the second, with inverse
`A`, and symmetrically.  Thus `rank(I-AB)=rank(I-BA)` at every coordinate.
The identity persists in the rank ultraproduct and after fixed matrix
amplification, proving stable finiteness.  An embedded algebra can therefore
contain no one-sided inverse with a nonzero reverse defect.

Finally, normalized-rank error does not directly become Hamming error on the
underlying vector set: if two matrices differ by rank `r`, their equality set
has proportion `|k|^(-r)`, which need not tend to one when `r=o(d_n)` but
`r->infinity`.  Hence this construction stops at linear soficity; it does not
silently prove soficity.  Nor can a group-level linear-sofic model over `F_2`
simply be extended linearly and assumed faithful on `F_2[G]`: that extra
faithfulness is precisely the coefficient-algebra decoder being classified.
