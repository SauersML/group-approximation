---
rg: 2
id: lef-fp-completeness-from-rf-fp-completeness
kind: route
title: Finitely presented LEF groups are exactly the residually finite ones
target: lef-of-finite-presentations-is-pi2-complete
requires:
  - residual-finiteness-of-finite-presentations-is-pi2-complete
  - lef-recognition-has-a-pi2-upper-bound
artifacts:
  - research/artifacts/rf-fp-pumped-minsky-part3-2026-09-12.md
---

## Why sufficient

For finitely presented groups, LEF iff residually finite (Vershik--Gordon,
*Groups locally embeddable into finite groups*, St. Petersburg Math. J. 9
(1998), Theorem 2.2; the direction RF implies LEF is immediate).  So `LEF_fp`
and `RF_fp` are the same subset of codes.  The reduction
`INF <=_m RF_fp` of [[residual-finiteness-of-finite-presentations-is-pi2-complete]]
is therefore a reduction to `LEF_fp`.  Membership is
[[lef-recognition-has-a-pi2-upper-bound]].
