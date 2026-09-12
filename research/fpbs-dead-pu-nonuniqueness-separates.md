---
rg: 2
id: fpbs-dead-pu-nonuniqueness-separates
kind: route
title: Dead - separate the product thresholds by nonuniqueness at p_u
target: fpbs-product-every-generating-set
requires:
  - fpbs-pu-nonuniqueness-commuting-subgroups
  - fpbs-critical-no-infinite-cluster
---

**Dead.** This naive argument runs as follows. Every Cayley graph of a
nonamenable direct product has no unique infinite cluster at `p_u`
(Gaboriau--Tucker-Drob), and there is no infinite cluster at `p_c` (BLPS), so
`p_c != p_u`.

The step fails because "no unique infinite cluster" includes the case of no
infinite cluster at all. That case is exactly what collapse `p_c = p_u`
produces. `fpbs-pu-nonuniqueness-cannot-separate` proves this and invalidates
the route. The missing input is `theta(p_u) > 0`, which on its own is
equivalent to separation.
