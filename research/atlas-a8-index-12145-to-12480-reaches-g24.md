---
rg: 2
id: atlas-a8-index-12145-to-12480-reaches-g24
kind: claim
title: The first arithmetic A8-overgroup candidate after M24 is G2(4) at index 12480
artifacts:
  - experiments/atlas_a8_index_12145_to_12480_order_sieve.py
  - experiments/atlas-a8-index-12145-to-12480-order-sieve.json
distinct_from:
  atlas-a8-index-11881-to-12144-reaches-m24: that crosses the preceding A12-to-M24 interval; this crosses the next complete simple-order interval.
  atlas-g24-contains-no-a8: that removes the arithmetic endpoint using maximal subgroups; this only identifies it by order.
  atlas-a8-index-44551-to-48960-reaches-l44: that reaches the later genuine subfield L4(4) endpoint; this identifies the earlier empty G2(4) endpoint.
---

Let `S` be finite nonabelian simple and suppose `|A8|` divides `|S|`.  If

```text
12144 < |S|/|A8| <= 12480,                           (SIG24-1)
```

then

```text
S~=G2(4),       |S|/|A8|=12480.                     (SIG24-2)
```

There is no intervening simple-group order after `M24`; the next row is

```text
|G2(4)|=251596800=12480*20160.                       (SIG24-3)
```

The interval and factorization agree with the GAP Character Table Library
[*Simple Groups by Group Order*](https://www.math.rwth-aachen.de/homes/Thomas.Breuer/ctbllib/ctbltoc/views/simplebyorder.html).
