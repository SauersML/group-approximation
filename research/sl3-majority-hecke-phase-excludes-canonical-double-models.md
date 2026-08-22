---
rg: 2
id: sl3-majority-hecke-phase-excludes-canonical-double-models
kind: route
title: A majority common-phase sector contradicts the canonical fold trace
target: sl3-regular-arithmetic-double-fold-mark-collapse
requires:
  - sl3-joint-hecke-multiplicity-has-a-majority-phase-sector
artifacts:
  - research/artifacts/sl3-joint-determinant-index-audit-2026-08-21.md
---

Let `W_n=sigma_n(w)`.  From `(JHM1)` and Cauchy--Schwarz,

```text
|tr(W_n)|
 >= |tr(p_n W_n)|-|tr((1-p_n)W_n)|
 >= tr(p_n)-tr(1-p_n)-o(1)
 >= 2 kappa-o(1).
```

But `w` is nontrivial by amalgam normal form, so canonical character gives
`tr(W_n)->0`.  Hence no canonical microstate sequence exists.  In
particular the universal assertion defining
`sl3-regular-arithmetic-double-fold-mark-collapse` holds vacuously (and the
same contradiction already proves nonhyperlinearity of the double).
