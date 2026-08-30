---
rg: 2
id: complete-selflessness-tensor-permanence
kind: claim
title: Tensoring a completely selfless algebra with a simple uniquely tracial algebra preserves selflessness
distinct_from:
  stw99-problem-xcv-pure-tensor-permanence: that asks whether tensor products of arbitrary pure algebras are pure; this theorem uses the substantially stronger complete-selflessness hypothesis on one factor.
  stw99-problem-xc-cstar-simple-strict-comparison: this is a C*-probability-space tensor theorem that produces a class of positive group-algebra instances but does not settle arbitrary C*-simple groups.
artifacts:
  - research/artifacts/stw90-strict-comparison-group-frontier-2026-08-30.md
---

Let `(A,rho)` be a separable completely selfless tracial C*-probability
space, and let `B` be a separable simple unital C*-algebra with unique trace
`tau`.  Then

```text
(A tensor_min B, rho tensor tau)
```

is selfless.  No exactness assumption on `B` is required.

More generally, ordinary selflessness of `(A,rho)` suffices when `B` is
exact.

**Established (literature).**  This is the scalar-state specialization of
the cp-map tensor permanence theorem in Gao--Junge--Kunnawalkam
Elayavalli--Patchell--Robert, *Selfless C*-correspondences, operator valued
C*-probability spaces and completely positive maps*, arXiv:2607.20361
(22 July 2026).  It is imported here, not reproved.
