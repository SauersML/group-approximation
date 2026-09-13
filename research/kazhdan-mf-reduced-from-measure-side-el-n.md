---
rg: 2
id: kazhdan-mf-reduced-from-measure-side-el-n
kind: route
title: The sufficiency half of the reduced-C* dichotomy, applied to a minimal subshift, gives an infinite Kazhdan group with MF reduced algebra
target: infinite-kazhdan-group-with-mf-reduced-cstar
requires:
  - free-group-cantor-el-n-reduced-cstar-mf-iff-invariant-measure
  - simple-kazhdan-lef-group-from-minimal-subshift
artifacts:
  - research/artifacts/un-reduced-cstar-2026-09-13-part1.md
---

Take `r = 1`: an infinite minimal subshift `X` over a finite alphabet. It is free, since there are no periodic
points, and `X` carries an invariant probability measure (Krylov–Bogolyubov). The ring `R = LC(X,F_q)⋊ℤ` is finitely
generated. The sufficiency half of `free-group-cantor-el-n-reduced-cstar-mf-iff-invariant-measure` makes
`C*_r(EL_N(R)/Z)` MF for large `N`.

For `N ≥ 3`, `EL_N(R)/Z` is infinite and Kazhdan. For `N = 3` that is `simple-kazhdan-lef-group-from-minimal-subshift`;
for larger `N` it follows from Ershov–Jaikin-Zapirain and simplicity mod centre. So some infinite Kazhdan group has
MF reduced C*-algebra.

This route does not fire while the equivalence is open.
