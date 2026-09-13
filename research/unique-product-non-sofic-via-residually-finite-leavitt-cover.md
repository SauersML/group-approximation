---
rg: 2
id: unique-product-non-sofic-via-residually-finite-leavitt-cover
kind: route
title: Residual finiteness of the hyperbolic Leavitt cover gives a unique-product nonsofic group
target: unique-product-non-sofic-group
requires: [hyperbolic-kazhdan-leavitt-cover-is-residually-finite, hyperbolic-kazhdan-group-has-infranormal-kazhdan-subgroup, rf-hyperbolic-rigid-pair-host-gives-up-nonsofic-group]
---

Let `G` be the hyperbolic Kazhdan Leavitt cover, assumed residually finite by
`hyperbolic-kazhdan-leavitt-cover-is-residually-finite`.  It contains the rigid
pair `Gamma_hat <= G_hat` of
`hyperbolic-kazhdan-group-has-infranormal-kazhdan-subgroup`.

`rf-hyperbolic-rigid-pair-host-gives-up-nonsofic-group` then gives a deep normal
finite-index subgroup `G_k` with unique products.  The restricted pair
`Gamma_hat cap G_k <= G_hat cap G_k` is still infranormal, not normal, and
Kazhdan.  Its integer-lamp wreath `W` has unique products and is not sofic.  ∎

This is Case 2 of `non-rf-hyperbolic-group-or-unique-product-nonsofic-group-proof`,
recorded as a route so the single open input is visible.
