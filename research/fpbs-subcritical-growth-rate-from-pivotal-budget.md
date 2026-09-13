---
rg: 2
id: fpbs-subcritical-growth-rate-from-pivotal-budget
kind: route
title: A linear pivotal budget has zero exponential pivotal growth rate
target: fpbs-universal-subcritical-pivotal-growth-rate
requires:
  - fpbs-pivotal-budget-universal
artifacts:
  - research/artifacts/fpbs/docs/pivotal-kernel-ordering-2026-09-12.md
---

Conditional route recording Proposition 3.3 of the artifact. The budget is
OPEN.

Read PB with the lazy walk, as in
`fpbs-integrated-sensitivity-from-pivotal-budget`. Suppose
`E_p[N_(n,R)|E_(n,R)] <= Cn` for all `n>=1`, `R>=n` and `p in [c,p0]`. Then
`L_n(p0) <= C`, so `n^(-1) log(1+L_n(p0)) -> 0 < lambda_0/2`.

No converse is known. No implication in either direction is recorded between
this claim and IS or NC. Artifact Section 3 shows that each direction is
formally compatible with the other failing, but no percolation model is known
that separates them.
