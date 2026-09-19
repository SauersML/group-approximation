---
rg: 2
id: stw26-finite-dimensional-tracial-boundary-cu-regularity-proof
kind: route
title: Extract strict comparison from Cu regularity and apply finite-boundary Toms--Winter
target: stw26-finite-trace-boundary-cu-z-stable
requires:
  - stw18-finite-trace-boundary-toms-winter
artifacts:
  - research/artifacts/stw18-23-26-finite-tracial-boundary-audit-2026-08-30.md
---

For a simple separable stably finite C-star algebra, the standard Cuntz-
semigroup regularity equivalences (STW Proposition `prop:cu-regular`) give

```text
Cu(A) isomorphic to Cu(A tensor Z)
    implies A is pure
    implies Cu(A) is almost unperforated
    implies A has strict comparison.
```

The remaining hypotheses on `A` and its trace boundary are exactly those of
`stw18-finite-trace-boundary-toms-winter`.
That established theorem turns strict comparison into `Z`-stability and
proves the target claim.
