---
rg: 2
id: fpbs-no-amenable-wq-normal-via-cost-and-acylindricity
kind: route
title: Remove the groups covered by Lyons and by Choi--Seo from the complement of the amenable wq-normal class
target: fpbs-no-amenable-wq-normal-class-nonuniqueness
requires:
  - fpbs-non-fixed-price-one-has-nonuniqueness
  - fpbs-sc-choi-seo
  - fpbs-residual-price-one-non-ah-class-nonuniqueness
---

Let `Gamma` be a nonamenable finitely generated group with no infinite amenable
wq-normal subgroup. There are three cases.

1. **Not of fixed price one.** `fpbs-non-fixed-price-one-has-nonuniqueness`
   gives `p_c < p_u` on every Cayley graph.
2. **Acylindrically hyperbolic.** `fpbs-sc-choi-seo` gives the same.
3. **Otherwise.** `Gamma` satisfies the three hypotheses of
   `fpbs-residual-price-one-non-ah-class-nonuniqueness`.

The cases are exhaustive, so this route is a genuine decomposition of its
target rather than a restatement. Two of its three premises are established
imports.
