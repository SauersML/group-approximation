---
rg: 2
id: stw01-sigma-unital-extensions-preserve-qt-linearity
kind: claim
title: Bounded-quasitrace linearity is closed under extensions with sigma-unital ideal
distinct_from:
  stw01-stable-ideal-extensions-force-qt-linearity: that theorem kills every bounded quasitrace on a stable ideal; here the sigma-unital ideal may carry arbitrary nonzero traces
  stw01-central-projection-ideal-extensions-preserve-qt-linearity: that theorem uses an approximate unit of ambient-central projections; here the ideal may be projectionless and no norm-quasicentral sequence is assumed
  stw01-asymptotic-quasitracial-cuts-promote-linearity: that is a criterion for one quasitrace along prescribed cuts; this theorem proves its hypotheses automatically from trace-linearity on a sigma-unital ideal
  stw99-problem-i-quasitraces-are-traces: this is an extension permanence theorem and assumes bounded-quasitrace linearity for both the ideal and quotient
artifacts:
  - research/artifacts/stw01-sigma-unital-extension-audit-2026-08-30.md
---

Let

```text
0 -> I -> A -> A/I -> 0
```

be an extension with `A` unital and `I` sigma-unital.  If every bounded
`2`-quasitrace on `I` is a trace and every bounded `2`-quasitrace on `A/I`
is a trace, then every bounded `2`-quasitrace on `A` is a trace.

In particular the conclusion holds whenever `I` is separable.  No
separability, exactness, nuclearity, projectional approximate unit,
norm-quasicentral sequence, or splitting assumption is imposed on `A`.
