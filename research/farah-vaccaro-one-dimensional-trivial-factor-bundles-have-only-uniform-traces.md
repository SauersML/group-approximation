---
rg: 2
id: farah-vaccaro-one-dimensional-trivial-factor-bundles-have-only-uniform-traces
kind: claim
title: One-dimensional trivial II1-factor bundles have only their canonical traces
distinct_from:
  stw22-dim1-factor-bundles-have-uniform-traces: that theorem permits nontrivial varying-factor bundles but assumes countable generation; this published theorem has one fixed factor fibre and no countable-generation hypothesis.
  stw22-zero-dimensional-factor-bundles-have-uniform-traces: that theorem permits arbitrary nontrivial factorial bundles but requires a zero-dimensional base; this theorem permits dimension one but requires a trivial bundle.
  stw22-finite-dimensional-trivial-field-traces: that theorem treats trivial hyperfinite fields over arbitrary finite-dimensional metrizable bases; this theorem treats every II1 factor, including free-group factors, but only bases of dimension at most one.
---

Let `(N,tau)` be a `II_1` factor and let `X` be a compact Hausdorff
space with covering dimension at most one. Then every tracial state on the
trivial W-star bundle `C_sigma(X,N)` is uniquely of the form

```text
rho_mu(a) = integral_X tau(a(x)) dmu(x)
```

for a Radon probability measure `mu` on `X`. Consequently

```text
T(C_sigma(X,N)) = {rho_mu : mu in Prob(X)}
```

and every trace is continuous for the uniform `2`-norm. In particular this
applies to `X=[0,1]` or the circle and `N=L(F_2)`.

**ESTABLISHED 2026-08-30** by
[[farah-vaccaro-one-dimensional-trivial-factor-bundles-literature-proof]].
