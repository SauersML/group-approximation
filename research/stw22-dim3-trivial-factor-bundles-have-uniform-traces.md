---
rg: 2
id: stw22-dim3-trivial-factor-bundles-have-uniform-traces
kind: claim
title: Trivial bundles with one separable II1 fibre have only uniform traces through dimension three
distinct_from:
  farah-vaccaro-one-dim-trivial-bundles-uniform-traces: that theorem treats arbitrary II1 fibres only over bases of dimension at most one; the present theorem reaches dimension three using Jekel contractibility and new quantitative sphere lifting.
  stw22-dim2-factor-bundles-have-uniform-traces: that theorem allows varying finite-factor fibres but stops at dimension two; the present theorem reaches dimension three under the fixed-fibre triviality hypothesis.
  stw22-finite-dimensional-trivial-field-traces: that theorem handles every finite dimension for the hyperfinite fibre; the present theorem allows any fixed separable II1 factor but only through dimension three.
artifacts:
  - research/artifacts/stw22-fixed-factor-s2-filling-audit-2026-08-30.md
---

Let `(N,tau)` be any `II_1` factor with separable predual, let `K` be a
compact Hausdorff space with covering dimension at most three, and let
`C_sigma(K,N)` be the bounded `2`-norm-continuous trivial W-star bundle.
Every tracial state on `C_sigma(K,N)` is uniquely of the form

```text
a |-> integral_K tau(a(x)) dmu(x)
```

for a Radon probability measure `mu` on `K`.  Equivalently, every trace is
continuous for the uniform `2`-norm.

No hyperfiniteness, property Gamma, or common quantitative modulus across
different factors is assumed.  The factor is fixed before the selection
modulus is chosen.
