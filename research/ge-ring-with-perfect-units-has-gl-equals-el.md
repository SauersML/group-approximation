---
rg: 2
id: ge-ring-with-perfect-units-has-gl-equals-el
kind: claim
title: A GE-ring with perfect unit group has GL equal to EL in every rank at least two
distinct_from:
  leavitt-gl-equals-el-and-perfect-unit-group: that is the binary Leavitt statement, proved internally by prefix-code self-similarity with no external K-theory and machine-checked; this is the general ring-theoretic lemma, which assumes the GE property and perfection instead of proving them.
  properly-infinite-unit-rank-two-normal-generator: that produces one normal generator of EL_2 from four splitting elements; this compares GL with EL and says nothing about normal generation.
  elementary-rank-descent-to-two: that places a higher rank inside rank two over a ring with properly infinite unit; this identifies GL with EL at a fixed rank and assumes neither proper infiniteness nor a descent.
artifacts:
  - research/artifacts/rank-one-headline-review-2026-09-07.md
---

Let `R` be a unital GE-ring, so every invertible matrix is a product of
elementary matrices and invertible diagonal matrices, and suppose `R^x` is
perfect.  Then

```text
GL_n(R) = EL_n(R)      for every n >= 2.
```

The proof needs only the Whitehead element `diag(a,a^(-1)) in EL_2(R)` and
the fact that diagonal matrices normalize the elementary subgroup.
