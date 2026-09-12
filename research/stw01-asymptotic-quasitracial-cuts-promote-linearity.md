---
rg: 2
id: stw01-asymptotic-quasitracial-cuts-promote-linearity
kind: claim
title: Square-seminorm central approximate-unit cuts promote one bounded quasitrace to a trace
distinct_from:
  stw01-qt-idempotent-approximate-units-preserve-linearity: that theorem requires every idempotence defect and commutator to vanish exactly for every bounded quasitrace at every stage; this theorem fixes one quasitrace and only requires its square seminorms to tend to zero along the approximate unit
  stw01-qt-central-projection-extensions-preserve-linearity: that theorem uses genuine projections which become exactly central in each individual square-null quotient; this theorem permits positive contractions which become one central projection only after passage to a quasitracial sequence quotient
  stw01-qt-invisible-ideal-extension-principle: that requires the ambient quasitrace to vanish on the whole ideal and descend directly; here the ideal may carry nonzero traces and only the complementary tail descends
artifacts:
  - research/artifacts/stw01-asymptotic-quasitracial-cut-audit-2026-08-30.md
---

Let `A` be unital, let `I triangleleft A`, and let `(e_n)` be an increasing
positive-contractive approximate unit for `I`, and suppose every bounded
`2`-quasitrace on `A/I` is a trace.  Let `tau` be one bounded
`2`-quasitrace on `A`.  Assume only that the particular restriction
`tau|Her_A(e_n)` is a trace for every `n`.  If

```text
tau((e_n-e_n^2)^2) -> 0,                                      (AQC1)
tau([e_n,a]*[e_n,a]) -> 0                  for every a in A,   (AQC2)
```

then `tau` is a trace.

Thus no universal bounded-quasitrace radical is needed: idempotence and
centrality may hold only asymptotically, and only in the square seminorm of
the quasitrace being promoted.

Consequently, if all bounded quasitraces on the hereditary heads are traces,
then any nontracial bounded `2`-quasitrace `tau` must satisfy the sharp
escape alternative

```text
limsup_n tau((e_n-e_n^2)^2)>0
```

or there is `a in A` such that

```text
limsup_n tau([e_n,a]*[e_n,a])>0.
```

This is a necessary certificate for a counterexample to linearity along
such an extension.
