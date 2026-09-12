---
rg: 2
id: clifford-ce-gives-bare-wall
kind: route
title: The Clifford crossed product already contains the bare wall
target: bare-relative-wall-exists
requires: [kun-thom-clifford-crossed-product-ce]
artifacts:
  - notes/TRUE_CLIFFORD_COMPRESSOR_SITE_GROWTH.md
  - notes/TRUE_RELATIVE_WALL_IS_COMMUTANT_GROWTH.md
---

In `M_Cl=Cl(G/Gamma) crossed_product G` the root Majorana `c_(Gamma)`
centralizes `pi(Gamma)` and is moved by `pi(h)` to `c_(h Gamma)!=c_(Gamma)`,
so `M_Cl` carries a wall unconditionally; `clifford-compressor-site-growth`
computes the resulting growth index to be infinite at every strict positive
compressor.  Connes embeddability of `M_Cl` therefore supplies the wall in a
Connes-embeddable model.

This edge records the ordering of the lane: the assigned crossed-product
claim implies the bare-wall claim, and also — through the diagonal doubling
`c_x tensor c_x` of `TRUE_DOUBLE_CLIFFORD_KUN_THOM_REDUCTION.md` — Connes
embeddability of the Bernoulli algebra `L(W)`.  It is the strongest, not the
cheapest, entry point to Q3.4.
