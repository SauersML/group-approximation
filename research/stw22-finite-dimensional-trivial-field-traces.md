---
rg: 2
id: stw22-finite-dimensional-trivial-field-traces
kind: claim
title: Trivial UHF fields over every finite-dimensional compact base have only uniform traces
distinct_from:
  stw22-two-dimensional-trivial-field-trace-continuity: that is the degree-one sphere case and stops at covering dimension two; the present theorem treats every finite covering dimension.
  stw22-finite-dimensional-colouring-from-local-lifts: that theorem is conditional on local weighted corner lifting; the present theorem proves that lifting for every finite-dimensional compact metrizable base.
  stw22-one-dimensional-trivial-field-trace-continuity: that uses only equi-LC0; the present theorem establishes all finite equi-connectivity degrees.
artifacts:
  - research/artifacts/stw22-all-degree-weighted-selection-audit-2026-08-30.md
---

Let `X` be compact and metrizable with finite covering dimension, let `U`
be an infinite-dimensional UHF algebra with unique trace, and let `M` be
the uniform tracial completion of

```text
C(X) tensor U.
```

Then every norm/`2`-norm fibre gap `K_x/J_x` has no nonzero bounded
positive trace.  Consequently every tracial state on `M` is uniquely

```text
a |-> integral_X tau(a(t)) dmu(t)
```

for a probability measure `mu` on `X`, and is continuous for the uniform
`2`-norm.

Equivalently, STW Problem XXII has a positive answer for all finite-
dimensional trivial hyperfinite bundles.  This supersedes the
dimension-at-most-two theorem but does not address infinite-dimensional
bases, nontrivial bundles, or arbitrary non-Bauer trace simplices.
