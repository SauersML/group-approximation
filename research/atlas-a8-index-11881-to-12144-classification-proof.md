---
rg: 2
id: atlas-a8-index-11881-to-12144-classification-proof
kind: route
title: Filter the post-A12 simple-order interval to the M24 equality
target: atlas-a8-index-11881-to-12144-reaches-m24
requires: []
artifacts:
  - experiments/atlas_a8_index_11881_to_12144_order_sieve.py
  - experiments/atlas-a8-index-11881-to-12144-order-sieve.json
---

The CFSG order list gives exactly `(SIM24-3)`.  The attached exact arithmetic
replay evaluates the `L2(787)` order formula, inserts the sporadic endpoint,
and asserts that only `M24` passes Lagrange divisibility by `20160`.  It also
pins `|M24|/|A8|=12144`, proving `(SIM24-1)--(SIM24-2)`.

