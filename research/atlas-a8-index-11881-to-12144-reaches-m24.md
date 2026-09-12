---
rg: 2
id: atlas-a8-index-11881-to-12144-reaches-m24
kind: claim
title: The first simple A8 overgroup after A12 is M24 at index 12144
artifacts:
  - experiments/atlas_a8_index_11881_to_12144_order_sieve.py
  - experiments/atlas-a8-index-11881-to-12144-order-sieve.json
distinct_from:
  atlas-a8-index-9793-to-11880-reaches-natural-a12: that reaches and classifies the natural A12 endpoint; this crosses the next complete simple-order interval to the sporadic M24 endpoint.
---

Let `S` be finite nonabelian simple and `A~=A8<S`.  If

```text
11880 < [S:A] <= 12144,                              (SIM24-1)
```

then

```text
S~=M24,       [S:A]=12144.                           (SIM24-2)
```

The complete simple-order interval strictly after `A12` through `M24` is

```text
L2(787), M24.                                        (SIM24-3)
```

Only `M24` has order divisible by `|A8|=20160`; its order is
`244823040=12144*20160`.  The interval and orders are independently listed
in the GAP Character Table Library
[*Simple Groups by Group Order*](https://www.math.rwth-aachen.de/homes/Thomas.Breuer/ctbllib/ctbltoc/views/simplebyorder.html).

