---
rg: 2
id: stw01-products-qt-linear-iff-ultraproducts-are
kind: claim
title: An l-infinity product of unital algebras has quasitrace linearity iff its factors and all norm ultraproducts do
distinct_from:
  stw01-matrix-product-algebras-have-qt-linearity: that proves linearity for products of matrix algebras by an explicit center-valued-trace argument; this is a reduction for arbitrary unital factors, from the product to its ultraproducts.
  stw01-extensions-preserve-qt-linearity: that reduces a product to the c_0-sum and the corona; this reaches the ultraproducts, which the ideal-gluing theorems do not.
artifacts:
  - research/artifacts/stw01-central-fiber-qt-linearity-2026-09-16.md
---

Let `(A_i)_(i in I)` be unital C\*-algebras.  Every bounded 2-quasitrace on
`prod_i A_i` is a trace iff two conditions hold:

- every bounded 2-quasitrace on each `A_i` is a trace;
- every bounded 2-quasitrace on each norm ultraproduct `prod_omega A_i` is a trace,
  for every free ultrafilter `omega` on `I`.

The same computation shows that the sequence algebra
`l^infinity(N, A) / c_0(N, A)` has quasitrace linearity iff every ultrapower
`A_omega` does.

The product is a `C(beta I)`-algebra through `l^infinity(I)`.  The fiber at a
principal point `i` is `A_i`.  The fiber at a free `omega` is `prod_omega A_i`: an
element with `lim_omega ||a_i|| = 0` factors as `theta(f) b` with
`f_i = ||a_i||^(1/2)`.

The "only if" direction is quotient pullback.  The "if" direction is the point of
the claim.  The ideal-gluing permanence theorems reduce a product only to smaller
products, while this reduces it to its ultraproducts.
