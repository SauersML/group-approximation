---
rg: 2
id: padding-makes-local-hs-rigidity-global
kind: claim
title: Linear Hilbert-Schmidt rigidity near the trivial tuple is equivalent to the global inequality
distinct_from:
  adaptive-tensor-amplification: that pads and then takes a tensor power to convert operator separation into two-norm separation, paying a defect cost linear in the dimension; this pads only, uses the exact scaling of both sides of a linear estimate, and pays nothing.
  dimension-defect-controlled-mf-hyperlinear: that converts a dimension-sensitive operator-norm model into hyperlinearity; this compares two normalized Hilbert--Schmidt rigidity statements and mentions no model.
  saturated-group-hs-relator-defect-gap: that asks for the constant for one particular presentation; this is the presentation-independent statement that localizing the question near the trivial tuple does not weaken it.
artifacts:
  - research/artifacts/hs-defect-gap-and-padding-2026-09-07.md
---

Let `Gamma=<S|R>` be finitely presented and, in normalized Hilbert--Schmidt
norm, put `D_2(U)=max_(s in S)||U_s-I||_2` and
`d_2(U)=max_(r in R)||r(U)-I||_2`.

Suppose there are `a,C>0`, independent of dimension, such that every unitary
tuple with `D_2(U)<a` satisfies `D_2(U) <= C d_2(U)`.  Then

```text
D_2(U) <= C d_2(U)
```

for every dimension and every unitary tuple.

So a dimension-free linear rigidity theorem in any fixed neighbourhood of the
trivial tuple is already the global theorem, and for the saturated group it
already contains `(HSG)` with `eta=1/C`.
