---
rg: 2
id: fpbs-product-split-amenable-wq-normal
kind: route
title: Split nonamenable products by whether they have an infinite amenable wq-normal subgroup
target: fpbs-product-every-generating-set
requires:
  - fpbs-amenable-wq-normal-class-nonuniqueness
  - fpbs-product-no-amenable-wq-normal
---

A nonamenable product `H x K` of infinite groups either has an infinite
amenable wq-normal subgroup or has none. The first case is contained in
`fpbs-amenable-wq-normal-class-nonuniqueness`. It covers every product in
which some factor has an infinite amenable subgroup `A`, because `{1} x A` is
wq-normal. That includes `F_2 x Z` and `F_2 x F_2`, taking `A` cyclic. Its
premise is relative subcriticality along `{1} x A`. The second case is
`fpbs-product-no-amenable-wq-normal`. Together they give the product root for
every generating set.

This mirrors `fpbs-bs-split-by-amenable-wq-normal-subgroup` on the product
class, so the product question joins the same decomposition as the universal
goal instead of forming a parallel region.
