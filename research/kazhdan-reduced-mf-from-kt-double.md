---
rg: 2
id: kazhdan-reduced-mf-from-kt-double
kind: route
title: Reduced MF of the Kun--Thom double restricts to its Kazhdan vertex subgroup
target: infinite-kazhdan-group-with-mf-reduced-cstar
requires: [kt-double-reduced-cstar-is-mf, reduced-mf-kazhdan-subgroup-gate]
---

The q=2 Kun--Thom double `D = G *_Gamma G` contains the infinite Kazhdan group
`Gamma = EL_r(F_2[x_1,...,x_d])`.  If `C*_r(D)` is MF, part 1 of
`reduced-mf-kazhdan-subgroup-gate` makes `C*_r(Gamma)` MF.

This route runs the gate in the useful direction for bookkeeping only: the
Kazhdan claim is the easier, necessary step, not a consequence one would prove
this way.
