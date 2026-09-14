---
rg: 2
id: aperiodic-sft-torus-modules-contextual-every-direction-proof
kind: route
title: A torus module is a periodic family, so the directional strip theorem forces a noncommuting pair in a narrow strip along each direction
target: aperiodic-sft-torus-modules-are-contextual-in-every-direction
requires: [strip-commutative-tiling-families-force-periodic-points]
artifacts:
  - research/artifacts/sk-labbe-2d-strip-contextuality-2026-09-13.md
---

Details are in the artifact, §3.

1. **Torus modules as families.** For a module `V`, put `E_a(z) = e_a(z mod Λ)`. Relations (T1)–(T3) give (Q1)–(Q3), so this is a nonzero `Λ`-periodic scale-`D` family, and `Λ` contains `L_e e` with `L_e` the order of `e` in `Z^2/Λ`.
2. **A noncommuting pair.** Suppose all pairs at `ℓ_e`-distance `<= 2r(|p|+|q|)` commuted. Item 1 of `strip-commutative-tiling-families-force-periodic-points` would give a point with period `L_e e`, contradicting aperiodicity. So some such pair does not commute.
3. **Separation.** If some representative of `t' − t` lay in `B_(2D)`, relation (T2) would make the pair commute.
4. **Covariant families over a finite field.** `U^e` has finite order `L`, so the family is `Le`-periodic. Conjugation by `U^w` with `ℓ_e(w) = 1` maps each strip onto the next, so one commutative strip would make all strips commutative, and item 1 would apply.
