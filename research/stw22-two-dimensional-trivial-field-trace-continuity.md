---
rg: 2
id: stw22-two-dimensional-trivial-field-trace-continuity
kind: claim
title: Trivial UHF fields over two-dimensional compact bases have only uniform traces
distinct_from:
  stw22-one-dimensional-trivial-field-trace-continuity: that uses only uniform local path connectedness; this proves the new loop-filling input and crosses the dimension-two Michael-selection threshold.
  stw22-finite-dimensional-colouring-from-local-lifts: that is conditional in every finite dimension; this verifies its local weighted-lifting hypothesis unconditionally through dimension two.
artifacts:
  - research/artifacts/stw22-low-spectrum-boundary-extension-audit-2026-08-30.md
---

Let `X` be compact and metrizable with covering dimension at most two, let
`U` be an infinite-dimensional UHF algebra with unique trace, and let `M`
be the uniform tracial completion of

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

Equivalently, STW Problem XXII has a positive answer for these
two-dimensional trivial hyperfinite bundles.  No continuity of the support
projections of the positive fields is assumed.

