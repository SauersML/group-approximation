---
rg: 2
id: simple-group-rank-function-dichotomy-proof
kind: route
title: The rank-null group elements form a normal subgroup through which the rank function factors
target: simple-group-rank-functions-are-augmentation-or-detecting
requires: []
artifacts:
  - research/artifacts/binary-cyclic-corner-rank-function-dichotomy-2026-09-12.md
---

Section 1 of the artifact (Theorem 1.1).
- `1 - [xy] = (1 - [x]) + [x](1 - [y])` and subadditivity close `N_rk` under products. Inverses and
  conjugates do not increase `rk(1 - [x])`.
- The kernel of `K[Γ] -> K[Γ/N_rk]` is spanned by the elements `[y](1 - [n])`, all of rank zero, so two
  lifts of one matrix have equal rank and `rk` factors through the quotient.
- When `N_rk = Γ` the quotient is `K`, whose only Sylvester matrix rank function is the normalized rank.
- A simple group has no other normal subgroups.
