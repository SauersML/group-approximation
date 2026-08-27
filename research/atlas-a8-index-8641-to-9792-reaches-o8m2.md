---
rg: 2
id: atlas-a8-index-8641-to-9792-reaches-o8m2
kind: claim
title: The first simple A8 overgroup after O8+(2) is O8-(2) at index 9792
artifacts:
  - experiments/atlas_a8_index_8641_to_9792_order_sieve.py
  - experiments/atlas-a8-index-8641-to-9792-order-sieve.json
distinct_from:
  atlas-a8-index-2201-to-8640-reaches-o8p2: that stops at the plus-type orthogonal group; this crosses the next complete simple-order interval.
---

Let `S` be a finite nonabelian simple group containing `A~=A8`.  If

```text
8640 < [S:A] <= 9792,                                (SIM1)
```

then

```text
S ~= O8-(2),             [S:A]=9792.                 (SIM2)
```

The complete simple-group order list strictly after `O8+(2)` through
`O8-(2)` is

```text
L2(709), L2(719), L2(727), L2(729), L2(733), O8-(2).
```

Lagrange eliminates the five rank-one groups: none of their orders is
divisible by `|A8|=20160`.  The endpoint has

```text
|O8-(2)|=197406720=9792*20160,
```

and its ATLAS maximal subgroup `(3 x A8):2` exhibits the required subgroup.

The order list and endpoint data agree with the GAP Character Table Library
[*Simple Groups by Group Order*](https://www.math.rwth-aachen.de/homes/Thomas.Breuer/ctbllib/ctbltoc/views/simplebyorder.html)
and the [ATLAS `O8-(2)` page](https://brauer.maths.qmul.ac.uk/Atlas/v3/clas/O8m2/).

