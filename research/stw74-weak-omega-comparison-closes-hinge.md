---
rg: 2
id: stw74-weak-omega-comparison-closes-hinge
kind: claim
title: Weak omega-comparison closes the separable LXXIV hinge
distinct_from:
  stw74-unit-almost-unperforation-closes-hinge: that uses a single unit-level almost-unperforation inequality to collapse each finite root; weak omega-comparison instead turns a trace-free projectionless hereditary corner into a stable algebra.
artifacts:
  - research/artifacts/stw74-property-sp-cu-stability-audit-2026-08-30.md
---

Let `A` be separable, simple, and unital, and suppose every nonzero
projection in `A` is infinite.  If `Cu(A)` has weak omega-comparison, then
`A` is purely infinite.

Equivalently, every separable counterexample to Problem LXXIV has a failure
of weak omega-comparison witnessed by elements

```text
x' << x,                    x <_s y_j for every j,
y_j full for every j,       x' not <= y_0+...+y_n for every n.
```

The representatives of the `y_j` may be chosen pairwise orthogonal and
inside one full projectionless hereditary subalgebra of `A`.

This extends the existing almost-unperforation route: finite
`n`-comparison implies omega-comparison, while the proof only needs its weak
full-element version.
