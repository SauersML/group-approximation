---
rg: 2
id: fpbs-product-no-amenable-wq-normal-via-residual-class
kind: route
title: The product case is a special case of the residual fixed-price-one non-acylindrically-hyperbolic class
target: fpbs-product-no-amenable-wq-normal
requires:
  - fpbs-residual-price-one-non-ah-class-nonuniqueness
  - fpbs-khezeli-products-have-fixed-price-one
  - fpbs-osin-ah-groups-not-products-not-torsion
---

Let `H` and `K` be infinite finitely generated groups such that `G = H x K` has
no infinite amenable wq-normal subgroup. We check the three hypotheses of
`fpbs-residual-price-one-non-ah-class-nonuniqueness`.

* `G` is finitely generated.
* `G` is nonamenable. Otherwise `G` itself is an infinite amenable subgroup,
  and it is wq-normal in `G`, because no proper subgroup contains it.
* **Hypothesis 1.** `G` has fixed price one by
  `fpbs-khezeli-products-have-fixed-price-one`.
* **Hypothesis 2.** `G` is not acylindrically hyperbolic by
  `fpbs-osin-ah-groups-not-products-not-torsion` item 1.
* **Hypothesis 3.** This is the assumption.

So that claim gives `p_c < p_u` on every Cayley graph of `G`.

This route turns the product claim into a special case of the residual claim.
It proves nothing new about percolation. Its content is that the product
Attempts are Attempts on known members of the residual class. The class is
nonempty (`fpbs-residual-class-has-torsion-products`).
