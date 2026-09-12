---
rg: 2
id: commuting-lamp-quotient-via-exact-finite-models
kind: route
title: Exact finite models of the commuting-lamp quotient
target: commuting-lamp-quotient-mf
requires: []
artifacts:
  - notes/COMMUTING_LAMP_QUOTIENT_STRUCTURE_AND_MF_FORK_2026-08-14.md
---

Separate `W/<zeta>` by finite quotients, or locally embed it into finite
groups, and apply `isWeakMF_of_isLEF`.  The finite level orbits and finite
invariant lamp subgroups make each `F_2[X] semidirect Gbar_k` residually
finite, so the hope is to add the shift.

Dead: `marked-quotients-not-lef`.  Every local embedding into a finite group
uncompresses the represented base and kills the surviving defect, and the
finite residual of `W/<zeta>` is the whole level-even lamp subgroup
(`commuting-lamp-quotient-finite-residual`), which contains that defect.
