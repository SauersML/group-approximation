---
rg: 2
id: bc-counterexample-via-leavitt-compression-classes
kind: route
title: Dead - build K-theory classes of C*_r(L^x) outside assembly from Leavitt idempotents and compression isometries
target: baum-connes-counterexample-group-exists
requires: []
---

**Dead.**
- The idempotents `e_a = s_a t_a` and the compression isometries of
  `L = L_(F_2)(1,2)` are elements of the ring `L`, not of `C[L^x]`.
- The group enters `C*_r(L^x)` only through its unitaries `u_g`. The
  compression structure is visible there only through subgroup averaging
  projections, their conjugates, and the relations between them.
- `subgroup-average-projections-give-no-reduced-bc-obstruction` shows each
  such projection is an assembly image (finite subgroups) or zero (infinite
  Kazhdan subgroups). The faithful trace of `C*_r G` collapses every
  compression relation.

A witness would need a projection not built from subgroup averages. Its only
trace-level form is an irrational trace, recorded under Attempts on
`baum-connes-counterexample-group-exists`.
