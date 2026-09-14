---
rg: 2
id: strip-commutative-tiling-families-force-periodic-points-proof
kind: route
title: Levels along a rational direction are commuting blocks, and an ordered product over a long run of levels kills every term
target: strip-commutative-tiling-families-force-periodic-points
requires: []
artifacts:
  - research/artifacts/sk-labbe-2d-strip-contextuality-2026-09-13.md
---

Complete direct proof. Details are in the artifact, §§1–2.

1. **Descent.** A scale-`D` family satisfies (Q3_r). Insert partitions of unity on `B_D \ B_r`; every extension of an illegal `r`-pattern is illegal, and the factors commute by (Q2).
2. **Coordinates.** Choose `w` with `ℓ_e(w) = 1`, so `z = c w + t e` with level `c = ℓ_e(z)`. Periodicity makes `E_a(c w + t e)` depend on `t mod L`, and each `r`-ball meets `2m_e + 1` consecutive levels.
3. **Blocks.** For `β ∈ A^(Z/L)`, put `E_β(c) = prod_t E_(β(t))(c w + t e)`. Under the hypothesis these are orthogonal idempotents summing to `1`, and blocks at level distance `<= 2m_e` commute.
4. **Illegal windows.** A window of `2m_e + 1` blocks containing an illegal `r`-ball has product `0`: regroup, then apply (Q3_r).
5. **König.** If legal words of every length exist, a bi-infinite legal word gives `x(c w + t e) = β_c(t mod L) ∈ Ω`, with period `Le`.
6. **Ordered product.** Expand `1 = prod_(c <= W_0 − 1) sum_β E_β(c)` in increasing `c`. Every term contains an illegal window of consecutive factors, so `1 = 0`.
7. **Run length.** In a legal word of length `>= |A|^(2m_e L) + 2m_e`, two blocks of `2m_e` letters coincide. Pumping between them keeps every window legal, and gives a point with independent periods `Le` and `(p' − p) w`.
8. **Converse.** A point with period `Le` gives the one-dimensional classical family.
