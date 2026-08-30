---
rg: 2
id: stw01-local-trace-rigid-models-force-linearity
kind: claim
title: Local approximation by quasitrace-rigid unital subalgebras forces every bounded quasitrace to be a trace
artifacts:
  - research/artifacts/stw01-quasitrace-status-and-local-permanence-audit-2026-08-30.md
---

Let `A` be a unital C*-algebra.  Suppose that for every finite subset
`F subset A` and every `epsilon>0` there is a unital C*-subalgebra `B subset
A` such that

```text
max_(x in F) dist(x,B)<epsilon                         (QL1)
```

and every bounded 2-quasitrace on `B` is a trace.  Then every bounded
2-quasitrace on `A` is a trace.

Neither `A` nor the local models are assumed separable.  The hypothesis is
strictly a norm-local one; replacing norm approximation by 2-norm
approximation is not justified by this result.
