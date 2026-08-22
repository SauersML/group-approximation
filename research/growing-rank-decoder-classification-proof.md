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
equivalence in the definition of a linear-sofic algebra.  The equivalence
between linear soficity of `G` and of `k[G]` is Theorem 1.1 of
Arzhantseva--Paunescu, *Linear sofic groups and algebras*.

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
silently prove soficity.
