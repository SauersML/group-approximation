---
rg: 2
id: lamp-telescope-base-lef-proof
kind: route
title: Directed union of finite-kernel residually finite pieces
target: lamp-telescope-base-is-lef
requires:
  - finite-telescope-level-coset-orbits
  - finite-site-orbits-invariant-clifford-kernel
  - lef-implies-operator-mf
artifacts:
  - notes/COMMUTING_LAMP_QUOTIENT_STRUCTURE_AND_MF_FORK_2026-08-14.md
---

## Direct proof

Every `Gbar_k`-orbit on `X` is finite, so every finite lamp window lies in a
finite `Gbar_k`-invariant subgroup `L'`, and `ClLamp(X) semidirect Gbar_k` is
the directed union of the groups `L' semidirect Gbar_k`.

Each `L' semidirect Gbar_k` is residually finite: `Aut(L')` is finite, so the
action kernel `N_0` has finite index; shrink to a finite-index normal
`N <= N_0` missing the finitely many `Gbar_k`-parts to be separated —
possible because `Gbar_k` is finitely generated linear — and map onto the
finite group `L' semidirect (Gbar_k/N)`, which is injective on `L'`.

Residual finiteness implies LEF, LEF passes to directed unions, and
`T = union_k Gbar_k` makes `ClLamp(X) semidirect T` a further directed union.
Replacing `ClLamp(X)` by `F_2[X]` changes nothing in the argument.  The
manuscript's reassociation `ClLamp(X) sd (T sd Z) = (ClLamp(X) sd T) sd Z`
gives the two displayed decompositions.  Section 5 of the cited note is the
complete argument.
