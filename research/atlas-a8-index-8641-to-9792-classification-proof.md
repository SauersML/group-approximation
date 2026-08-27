---
rg: 2
id: atlas-a8-index-8641-to-9792-classification-proof
kind: route
title: Filter the complete post-O8+(2) order interval by A8 divisibility
target: atlas-a8-index-8641-to-9792-reaches-o8m2
requires: []
artifacts:
  - experiments/atlas_a8_index_8641_to_9792_order_sieve.py
  - experiments/atlas-a8-index-8641-to-9792-order-sieve.json
---

CFSG family order formulas, equivalently the cited CTblLib table, show that
the six rows in `(SIM1)` are the complete interval.  The attached exact
prime-power enumeration reproduces all five `L2(q)` rows, appends the sole
higher-rank endpoint, and asserts that only `O8-(2)` has order divisible by
`20160`.  The ATLAS maximal-subgroup row `(A8 x 3):2` proves existence at the
endpoint, giving `(SIM2)`.

