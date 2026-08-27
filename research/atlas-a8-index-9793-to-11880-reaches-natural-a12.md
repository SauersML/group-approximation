---
rg: 2
id: atlas-a8-index-9793-to-11880-reaches-natural-a12
kind: claim
title: The first simple A8 overgroup after O8-(2) is natural A12 at index 11880
artifacts:
  - experiments/atlas_a8_index_9793_to_11880_order_sieve.py
  - experiments/atlas-a8-index-9793-to-11880-order-sieve.json
distinct_from:
  atlas-a8-index-507-to-990-reaches-natural-a11: that classifies the earlier alternating endpoint; this crosses the complete post-O8-(2) interval and classifies the A12 endpoint.
  atlas-natural-a8-supports-collapse-before-collision: that excludes natural-support pairs once present; this proves every A8 at the endpoint is natural-support.
---

Let `S` be finite nonabelian simple and `A~=A8<S`.  If

```text
9792 < [S:A] <= 11880,                               (SIA12-1)
```

then

```text
S~=A12,       [S:A]=11880.                           (SIA12-2)
```

Moreover, in the natural degree-twelve action, `A` has orbit decomposition

```text
8+1+1+1+1,                                           (SIA12-3)
```

and is `Alt(X)` on its eight-point support.

The complete simple-order interval is

```text
L2(739), L2(743), 3D4(2), L2(751), L3(11),
L2(757), L2(761), L2(769), L2(773), A12.             (SIA12-4)
```

Only `A12` has order divisible by `20160`; its order is
`239500800=11880*20160`.  The list agrees with the GAP Character Table
Library [*Simple Groups by Group Order*](https://www.math.rwth-aachen.de/homes/Thomas.Breuer/ctbllib/ctbltoc/views/simplebyorder.html).

