---
rg: 2
id: stw22-full-fundamental-group-trivial-bundles-finite-dimensional
kind: claim
title: Trivial bundles with a full-fundamental-group fibre have only uniform traces in every finite dimension
distinct_from:
  stw22-finite-dimensional-trivial-field-traces: that theorem treats the hyperfinite factor; the present theorem treats every fixed separable II1 factor with full fundamental group.
  stw22-dim3-trivial-factor-bundles-have-uniform-traces: that theorem treats every fixed separable II1 factor through dimension three; the present theorem reaches arbitrary finite covering dimension under a corner-isomorphism hypothesis.
artifacts:
  - research/artifacts/stw22-full-fundamental-group-all-degree-audit-2026-08-30.md
---

Let `(N,tau)` be a separable-predual `II_1` factor with full fundamental
group, and let `K` be a compact Hausdorff space of finite covering
dimension.  Every tracial state on the bounded `2`-norm-continuous trivial
bundle `C_sigma(K,N)` is uniquely

```text
a |-> integral_K tau(a(x)) dmu(x)
```

for a Radon probability measure `mu` on `K`.  Equivalently every trace is
continuous for the uniform `2`-norm.

In particular this applies whenever `N` is McDuff: if `N congruent
N tensor R`, cutting in the hyperfinite tensor factor handles amplifications
of trace at most one, while matrix amplification followed by such a cut
handles every trace greater than one.  Thus every amplification of `N` is
isomorphic to `N`.
