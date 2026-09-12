---
rg: 2
id: atlas-first-rank-five-relator-no-weyl-proof
kind: route
title: Read the constant first row and verify its Bezout certificate
target: atlas-first-rank-five-relator-kills-order-one-weyl-slice
requires:
  - atlas-order-one-weyl-atlas-is-one-laurent-common-root-test
  - atlas-three-mode-balanced-area-coefficient-table
artifacts:
  - experiments/atlas-rank5-balanced-area.json
  - experiments/atlas-rank5-balanced-area-17081560.log
---

The exact coefficient-table artifact is bound to the deterministic packet by
the matching word-list hash

```text
9e751115287b18fbe847309379d2710ffa0b1466c836d32ff4ec24446e6c2b99.
```

Its first row, `root_12_1e`, contains only exponent `A=0`, with coefficient
`16953689/41287680`.  Hence

```text
f_(root_12_1e)(t)-1=-24333991/41287680
```

is a nonzero constant.  The exported multiplier
`-41287680/24333991` multiplies it to exactly `1`; the artifact checks this
identity in rational arithmetic and records running gcd `1`.  A fresh local
execution reproduced the JSON byte for byte.

The established common-root criterion says an order-one Weyl phase must be a
common nonzero root of all `f_s(t)-1`.  This single constant row has no root
over `C`, so no such phase exists.  In particular the proposed order-one
rotation route is impossible, without making any assertion about general
non-Heisenberg pairs of coefficient unitaries.
