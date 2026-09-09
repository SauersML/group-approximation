---
rg: 2
id: cp-reflection-near-idempotents-round-to-pinchings
kind: claim
title: A completely positive reflection forces quantitative rounding to at most two matrix blocks
distinct_from:
  ucp-factorizations-round-to-matrix-expectations: That starts with an approximate factorization through a supplied finite-dimensional source algebra; this derives near-unitarity of the reflection directly from mixed-norm idempotence and the additional CP inequality P minus half the identity is CP.
  schur-near-idempotents-round-dimension-uniformly: That assumes a common matrix-unit eigenbasis for the channel; this permits an arbitrary channel whose reflection is CP, and constructs the pinching basis by Stinespring averaging and phase rounding.
artifacts:
  - research/artifacts/cp-reflection-near-idempotent-pinching-2026-09-08.md
---

Let `P:M_d(C)->M_d(C)` be self-adjoint on normalized `L^2`,
bistochastic, and UCP. Assume in addition that the map
`Q=2P-id` is completely positive, or equivalently that
`P-(1/2)id` is completely positive. Put

```text
delta=||P^2-P||_(infinity->2).
```

There is a self-adjoint unitary `V in M_d` such that

```text
E_V(x)=(x+VxV)/2,
||P-E_V||_(infinity->2)<=min{2,30sqrt(delta)}.
```

Writing `p=(I+V)/2`, the exact target algebra is
`pM_dp direct_sum (I-p)M_d(I-p)`. Zero corners are permitted,
so the identity expectation is included. The dimension is unchanged,
and no Kraus-rank bound is assumed.

For the stronger hypothesis `P-lambda id` completely positive with
`1/2<lambda<1`, one has the direct linear estimate

```text
||P-id||_(infinity->2)<=delta/(2lambda-1).
```

The threshold assumption is positivity in the CP order on maps. It
does not follow from nonnegative Hilbert-space spectrum. In particular
the native long-time Kazhdan heat estimates do not supply it. This
theorem excludes a class of candidate counterexamples; it establishes
neither general mixed-norm rounding nor nonhyperlinearity.

DERIVATION
stinespring-and-phase-rounding-repair-cp-reflections
