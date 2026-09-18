---
rg: 2
id: deligne-triple-cover-via-sublinear-windings
kind: route
title: Exclude the full parameter circle by sublinear windings and the finite branch by period arithmetic
target: deligne-triple-cover-exact-mf-radical
requires:
  - sp4-quasirep-windings-are-sublinear
  - sp4-quasirep-windings-budget-and-saturation
  - deligne-finite-parameter-group-has-period-prime-to-three
  - deligne-sep7-all-cover-mf-radical-classification
---

By item 4 of `sp4-quasirep-windings-budget-and-saturation`, the first prerequisite gives `P_op = (1/m)Z/Z` for one
even `m`. The third prerequisite then gives `3 not | m`. So `P_op` meets `(1/3)Z/Z` only in `0`: neither `1/3` nor
`2/3` lies in `P_op`. The annihilator formula of `deligne-sep7-all-cover-mf-radical-classification`, specialized at
covering degree three as in `deligne-sep7-triple-radical-via-all-cover-formula`, then makes `Rad_MF(E_3)` the whole
order-three kernel `C_3`.

The split differs from `deligne-sep7-triple-radical-via-all-cover-formula`. That route needs the single statement
`1/3 not in P_op`. This one separates it into two independent statements:
- a statement about plain quasi-representations of `Sp_4(Z)`, which can fail through a saturating sequence;
- an arithmetic statement about the finite branch, which can fail through an MF model of `E_6`.

Dadarlat's nonzero windings refute neither.
