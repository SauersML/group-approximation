---
rg: 2
id: atlas-a8-index-2201-to-8640-reaches-o8p2
kind: claim
title: The first simple A8 overgroup after HS is O8+(2) at index 8640
artifacts:
  - experiments/atlas_a8_index_2201_to_8640_order_sieve.py
  - experiments/atlas-a8-index-2201-to-8640-order-sieve.json
distinct_from:
  atlas-a8-index-991-to-2200-reaches-hs-s8-derived: that stops at the sporadic HS equality class; this crosses the next classical interval and reaches the triality group O8+(2).
---

Let `S` be finite nonabelian simple and suppose `A~=A8<S`.  If

```text
2201 <= [S:A] <= 8640,                              (SIO1)
```

then equality holds on the right:

```text
S ~= O8+(2),       [S:A]=8640.                     (SIO2)
```

The complete CFSG order interval from `HS` through `O8+(2)` has only three
orders divisible by `|A8|`: `L2(449)` at prospective index 2245, `S4(7)` at
index 6860, and `O8+(2)` at index 8640.  The first has 2-rank at most two,
whereas `A8` contains `C2^4`.

An embedding `A8 -> PSp4(7)` would pull back along
`Sp4(7)->PSp4(7)` to a four-dimensional linear representation of `A8` or
its Schur double cover `2.A8`.  A nontrivial composition factor would be a
faithful projective `A8` module of dimension at most four.  The [ATLAS A8
Brauer-representation list](https://brauer.maths.qmul.ac.uk/Atlas/alt/A8/)
records minimum faithful degree eight in characteristic seven for both `A8`
and `2.A8`.  If every composition factor were trivial, the perfect pullback
would have a unipotent 7-group image and hence trivial image.  Both cases are
impossible.  This removes `S4(7)` and proves `(SIO2)`.

