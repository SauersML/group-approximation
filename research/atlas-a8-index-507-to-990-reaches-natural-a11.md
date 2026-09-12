---
rg: 2
id: atlas-a8-index-507-to-990-reaches-natural-a11
kind: claim
title: The first simple A8 overgroup after M23 is natural A11 at index 990
artifacts:
  - experiments/atlas_a8_index_507_to_990_order_sieve.py
  - experiments/atlas-a8-index-507-to-990-order-sieve.json
distinct_from:
  atlas-a8-index-91-to-496-reaches-standard-l5: that stops at the standard L5(2) embedding and separately identifies M23; this continues the complete simple-order audit through A11.
  atlas-natural-a8-supports-collapse-before-collision: that excludes arbitrary marked natural-support pairs once present; this first proves every A8 at the next simple boundary is of that form.
---

Let `S` be finite simple and suppose `A~=A8<S`.  If

```text
507 <= [S:A] <= 990,                                (SIA1)
```

then equality holds on the right:

```text
S~=A11,       [S:A]=990,                            (SIA2)
```

and in the natural degree-eleven action `A` is `Alt(X)` for an eight-element
support `X`, fixing the other three points.

Equivalently, no finite simple group contains `A8` at an index from 507
through 989.  The only index-990 embedding family is already the natural
alternating-support family.

