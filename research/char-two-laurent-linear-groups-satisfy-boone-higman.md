---
rg: 2
id: char-two-laurent-linear-groups-satisfy-boone-higman
kind: claim
title: Linear groups over F_q[t,1/t] and over free F_q-algebras satisfy Boone--Higman when q is a power of two
distinct_from:
  leavitt-subalgebra-linear-groups-satisfy-boone-higman: that is the general embedding for any subalgebra of the binary Leavitt algebra; this exhibits concrete coefficient rings inside it and states the resulting input classes.
  fp-residually-finite-boone-higman: that is the open problem for all finitely presented residually finite groups; this settles one explicit family of linear residually finite inputs, not all of them.
artifacts:
  - research/artifacts/boone-higman-self-similar-and-complexity-2026-09-11.md
---

**ESTABLISHED (conditional on the imported finite presentation of
`L_(F_2)(1,2)^x`).** Let `q = 2^k`, `n >= 1` and `m >= 1`. Every subgroup of

```text
GL_n(F_q[t, t^-1])      and of      GL_n(F_q<x_1, ..., x_m>)
```

embeds in the finitely presented simple group `L_(F_2)(1,2)^x`. So every
finitely generated such subgroup satisfies the Boone--Higman conjecture.
Examples: every finitely generated subgroup of `SL_n(F_q[t])` and
`SL_n(F_q[t,t^-1])`, and the lamplighter `C_2 wr Z <= GL_2(F_2[t,t^-1])`.

Belk--Bleak--Matucci--Zaremsky's list of known classes (Theorem 5.1 of
*Progress around the Boone--Higman conjecture*) contains `GL_n(Z)` and, by
Zaremsky, finitely generated subgroups of `GL_n(Q)`, but no
positive-characteristic linear groups. No further novelty search was done.

DERIVATION
char-two-laurent-linear-groups-proof
