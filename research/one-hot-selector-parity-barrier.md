---
rg: 2
id: one-hot-selector-parity-barrier
kind: claim
title: Three-or-more one-hot selector branches cannot be enforced by parity equations alone
artifacts:
  - research/artifacts/compiler-lowering-hyperlinear-2026-08-18.md
distinct_from:
  controlled-linear-predication-normal-form: predication is a positive exact lowering theorem for branch equations; this claim identifies the non-affine selector invariant that the lowering leaves behind.
---

For every `m >= 3`, the one-hot subset

```text
H_m = {e_1,...,e_m} subset F_2^m
```

is not an affine subspace. Consequently there is no system of affine `F_2`
equations in `m` commuting selector bits whose solution set is exactly `H_m`.

In particular, after controlled equations are predicated into ordinary parity
operator equations, exact mutually-exclusive branch selection cannot be
recovered by merely adding more parity rows on the commuting selector bits.
