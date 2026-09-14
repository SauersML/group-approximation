---
rg: 2
id: thin-cylinder-sft-tiling-families-force-periodic-points-proof
kind: route
title: Column patterns commute on a thin cylinder, and an ordered product over a long run of columns kills every term
target: thin-cylinder-sft-tiling-families-force-periodic-points
requires: []
artifacts:
  - research/artifacts/sk-labbe-matricial-thin-cylinders-2026-09-13.md
---

This is a complete direct proof; details are in the artifact, §1.

1. **(⇐)** A point `x` with period `(0,L)` gives the one-dimensional family `E_a(z) = [x(z)=a]`.
2. **Columns.** By periodicity, any two sites in columns at horizontal distance `<= 2D` have representatives at vertical distance `<= ⌊L/2⌋ <= 2D`, so they commute by (Q2). The column products `E_β(c) = prod_j E_(β(j))(c,j)`, for `β ∈ A^(Z/L)`, are therefore orthogonal idempotents with sum `1`, and `E_β(c)` commutes with `E_(β')(c')` whenever `|c-c'| <= 2D`.
3. **Illegal windows.** A window `β_i ⋯ β_(i+2D)` containing an illegal `D`-ball has product `0` by (Q3), after commuting its factors.
4. **König.** If legal words of every length existed, a bi-infinite legal word would give a `(0,L)`-periodic point of `Ω` (using `D >= r`). So there is `W_0` with no legal word of length `W_0`.
5. **Ordered product.** Expanding `1 = prod_(c=0)^(W_0-1) sum_β E_β(c)`, with the factors taken in order, gives terms that each contain an illegal window of consecutive factors. So `1 = 0` and `W = 0`. ∎
