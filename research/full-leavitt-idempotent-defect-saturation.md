---
rg: 2
id: full-leavitt-idempotent-defect-saturation
kind: claim
title: One complementary Leavitt root normally generates the rank-20 Steinberg group
artifacts:
  - research/artifacts/hilbert-hotel-st20-full-mf-radical-2026-08-21.md
  - GroupApproximation/Steinberg/BinaryLeavitt.lean
---

For `q=s1*t1`, `t1*q*s1=1`; hence `q` is nonzero and full.  The two
Steinberg commutators

```text
[x_41(a*t1),x_13(q)] = x_43(a*t1*q),
[x_43(a*t1*q),x_32(s1)] = x_42(a)
```

put one complete root subgroup in `<<x_13(q)>>`.  Weyl root permutations put
every root subgroup there, so `x_13(q)` normally generates `St_20(R)`.
Its image normally generates every quotient in which it is identified with
the compression defect; no separate saturation family is needed.
