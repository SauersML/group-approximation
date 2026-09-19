---
rg: 2
id: finite-product-lift-of-internal-mf-reflections-proof
kind: route
title: Put the factors on a block diagonal and descend target maps through every coordinate kernel
target: finite-product-lift-of-internal-mf-reflections
requires:
  - binary-leavitt-all-ranks-full-mf-radical
  - mf-radical-product-and-restricted-sum-formulas
---

Embed `product_i K_i` block diagonally in

```text
GL_m(L_(F_2)(1,2)).
```

The binary Leavitt prefix-code isomorphism identifies this matrix group with
`U`, proving `(FPL2)`.

Let `theta:product_i K_i->M`, with `M` MF.  Restriction to the `i`th
coordinate kills `ker(pi_i)` by `(FPL1)`.  Hence `theta` kills their direct
product, which is exactly `ker(Pi)`, and descends uniquely to
`product_i Q_i`.  Conversely every map from the quotient pulls back through
`Pi`, proving `(FPL3)`.

Intersecting kernels gives `(FPL4)`.  Restricting the same bijection to maps
killing `N` and intersecting again gives `(FPL5)`.  Finite products of MF
groups are MF, so triviality of the quotient radical gives `(FPL6)`.

Coordinate conjugation proves the normal-generation assertion, and the union
of finite coordinate generating sets generates `K`.  Since the argument only
uses the factorization property, it applies verbatim to each additional
target class.
