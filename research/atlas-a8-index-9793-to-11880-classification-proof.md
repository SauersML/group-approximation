---
rg: 2
id: atlas-a8-index-9793-to-11880-classification-proof
kind: route
title: Filter the post-O8-(2) order interval and apply the A8 low-index orbit list
target: atlas-a8-index-9793-to-11880-reaches-natural-a12
requires: []
artifacts:
  - experiments/atlas_a8_index_9793_to_11880_order_sieve.py
  - experiments/atlas-a8-index-9793-to-11880-order-sieve.json
---

CFSG family order formulas give the complete list `(SIA12-4)`.  The attached
exact prime-power enumeration reproduces the seven rank-one rows, inserts the
two higher-rank rows and endpoint, and asserts that only `A12` passes
Lagrange divisibility by `20160`.

Restrict the natural degree-twelve action of `A12` to `A`.  Every nontrivial
orbit action is faithful because `A8` is nonabelian simple.  The standard
low-index subgroup list for `A8` says that its only nontrivial transitive
degree below thirteen is the natural degree eight.  Two such orbits cannot
fit in twelve points, so `(SIA12-3)` follows.  This proves the endpoint
embedding classification without a packet computation.

