---
rg: 2
id: deligne-triple-cover-via-winding-deficit
kind: route
title: Exclude the full parameter circle by a winding-ratio deficit on one window and the finite branch by period arithmetic
target: deligne-triple-cover-exact-mf-radical
requires:
  - sp4-quasirep-winding-ratio-has-a-deficit
  - sp4-winding-ratio-sharp-constant-is-gromov-dual
  - deligne-finite-parameter-group-has-period-prime-to-three
  - deligne-sep7-all-cover-mf-radical-classification
---

The argument has three steps.
1. By item 7 of `sp4-winding-ratio-sharp-constant-is-gromov-dual`, the first prerequisite gives
   `P_op = (1/m)Z/Z` for one even `m`.
2. The third prerequisite gives `3 not | m`. So neither `1/3` nor `2/3` lies in `P_op`.
3. The annihilator formula of `deligne-sep7-all-cover-mf-radical-classification`, specialized at covering degree
   three as in `deligne-sep7-triple-radical-via-all-cover-formula`, makes `Rad_MF(E_3)` the whole order-three kernel.

**Difference from `deligne-triple-cover-via-sublinear-windings`.** That route needs the winding ratio to tend to
zero. This one needs only that, on one window, the ratio stays strictly below `|k|/(2 pi beta*_W)`. That is the exact
value the all-MF branch forces, by items 5 and 6 of the theorem node.

**Each prerequisite can fail on its own.**
- The deficit fails if quasi-representations of `Sp_4(Z)` reach the l1-dual ceiling, for example if `P_op = R/Z`.
- The period statement fails through an MF model of `E_6`.

Determinant and `K_1` arguments cannot supply the deficit (item 8 of the theorem node).
