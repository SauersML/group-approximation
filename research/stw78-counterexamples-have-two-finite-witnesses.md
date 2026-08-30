---
rg: 2
id: stw78-counterexamples-have-two-finite-witnesses
kind: claim
title: Every LXXVIII counterexample has finite central-defect and matrix-infiniteness witnesses
distinct_from:
  stw78-counterexamples-have-finite-obstruction-targets: that gives a finitely generated quasitrace obstruction; this theorem additionally turns it into a concrete nonunitary isometry at a least finite matrix level.
artifacts:
  - research/artifacts/stw78-finite-quasitrace-seed-audit-2026-08-30.md
---

Every counterexample `phi:A->B` to Problem LXXVIII corestricts to a
counterexample

```text
phi_0:A->B_0=C*(phi(A),b_1,...,b_m)
```

for which there are a finite set `F subset A`, a number `n>=1`, and a
nonunitary isometry `v in M_n(C)`, where

```text
C=C*(1,b_1,...,b_m) subset B_0,
kappa_(phi_0)(F)>0.
```

The integer `n` can be chosen least.  Then `M_j(C)` is finite for every
`j<n`, while `M_n(C)` is infinite.  Thus a hypothetical counterexample is
controlled by two finite witnesses even though the remaining problem is an
asymptotic centralization problem.
