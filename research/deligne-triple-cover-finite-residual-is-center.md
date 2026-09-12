---
rg: 2
id: deligne-triple-cover-finite-residual-is-center
kind: claim
title: The finite residual of Deligne's triple cover of Sp4(Z) is exactly its order-three center
artifacts:
  - research/artifacts/deligne-maslov-hyperlinear-strategies-2026-08-21.md
distinct_from:
  deligne-triple-cover-fd-central-invisibility: that kills the central mark in every finite-dimensional unitary representation; this also proves that every element outside the center survives in a finite quotient and hence computes the full finite residual.
---

Let

```text
1 -> C_3=<z> -> E_3 -> Sp_4(Z) -> 1
```

be Deligne's connected triple cover.  Then

```text
Res_fin(E_3) = C_3.                                    (DFR1)
```

The inclusion `C_3 <= Res_fin(E_3)` is Deligne's finite-residual theorem.
The reverse inclusion uses only residual finiteness of `Sp_4(Z)`: reduction
modulo a suitable integer separates every nonidentity integral symplectic
matrix.  Thus every element of `E_3` outside the central fibre is separated
by a finite quotient pulled back from `Sp_4(Z)`.
