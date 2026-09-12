---
rg: 2
id: deligne-triple-cover-ternary-stable-finiteness-proof
kind: route
title: Lift stable finiteness from Sp4(Z) across the order-three center in characteristic three
target: deligne-triple-cover-ternary-group-algebras-are-stably-finite
requires:
  - finite-normal-p-subgroups-preserve-modular-stable-finiteness
  - lef-group-rings-over-stably-finite-rings-are-stably-finite
  - finitely-generated-linear-groups-are-residually-finite
artifacts:
  - research/artifacts/deligne-triple-cover-surjunctivity-2026-09-12.md
---

Section 2 of the artifact, Theorem 2.1.

1. `Sp_4(Z)` is a finitely generated subgroup of `GL_4(Q)`, so it is residually finite.
2. A residually finite group is LEF: a finite subset maps injectively into a finite quotient, preserving
   products. So `k[Sp_4(Z)]` is stably finite for every field `k`, by the LEF theorem with coefficient
   ring `k`.
3. The center `C_3` of `E_3` is a normal subgroup of order `3` with quotient `Sp_4(Z)`. For
   `char k = 3`, the modular transfer across finite normal `3`-subgroups gives that `k[E_3]` is stably
   finite.
