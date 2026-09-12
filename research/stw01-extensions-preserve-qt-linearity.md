---
rg: 2
id: stw01-extensions-preserve-qt-linearity
kind: claim
title: Bounded-quasitrace linearity is closed under arbitrary unital extensions
distinct_from:
  stw01-stable-ideal-extensions-force-qt-linearity: that theorem annihilates every bounded quasitrace on a stable ideal; here the ideal may carry arbitrary nonzero traces and need not be stable or sigma-unital.
  stw01-central-projection-ideal-extensions-preserve-qt-linearity: that theorem splits by projections already central in the ambient algebra; here an arbitrary approximate-unit net becomes one central projection only in a quasitracial net quotient.
  stw01-asymptotic-quasitracial-cuts-promote-linearity: that is a sequential criterion for one quasitrace; this theorem removes all countability and cut hypotheses by using a cofinal ultrafilter on an arbitrary approximate-unit net.
  stw99-problem-i-quasitraces-are-traces: this is an extension permanence theorem and assumes bounded-quasitrace linearity for both the ideal and quotient.
artifacts:
  - research/artifacts/stw01-sigma-unital-extension-audit-2026-08-30.md
---

Let

```text
0 -> I -> A -> A/I -> 0
```

be an extension with `A` unital.  If every bounded `2`-quasitrace on `I`
is a trace and every bounded `2`-quasitrace on `A/I` is a trace, then every
bounded `2`-quasitrace on `A` is a trace.

No sigma-unitality, separability, exactness, nuclearity, projectional or
sequential approximate unit, norm-quasicentrality, or splitting hypothesis
is imposed on the ideal or ambient algebra.  Thus bounded-quasitrace
linearity is a three-space property for unital C-star extensions.
