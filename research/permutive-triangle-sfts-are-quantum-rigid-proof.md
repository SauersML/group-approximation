---
rg: 2
id: permutive-triangle-sfts-are-quantum-rigid-proof
kind: route
title: Propagate commutation through the row above, and stack a returning periodic row
target: permutive-triangle-sfts-are-quantum-rigid
requires: [sft-crossed-product-fp-iff-quantum-rigid]
artifacts:
  - research/artifacts/free-minimal-crossed-product-rings-and-permutive-rigidity-2026-09-13.md
---

This is Propositions 4 and 5 of the artifact, Section 4. Fix a family `E` with (Q1)–(Q3), `D >= 1`.

1. **Operator determinism.** The operators on `z + B_1` commute, by (Q2). A product over a
   non-occurring `T`-pattern expands over `B_1` into forbidden `B_1`-patterns, so it vanishes. With
   `φ` the completion map,
   `E_a(z+e_2) = sum_(φ(b,c)=a) E_b(z) E_c(z+e_1)`,
   and symmetrically `E(z) ∈ 𝒜(z+e_1, z+e_2)` and `E(z+e_1) ∈ 𝒜(z, z+e_2)`.
2. **Rows commute.** Induction on `k`: `[𝒜(w), 𝒜(w + k e_1)] = 0`.
   - `𝒜(z) ⊆ 𝒜(z+e_2, z+e_1)`, and `𝒜(z+k e_1) ⊆ 𝒜(z+(k-1)e_1, z+(k-1)e_1+e_2)`.
   - The four generator pairs commute by induction: at distance `k-2` in the row; at distance `k-1`
     in the row above; and twice after expanding a row-above generator in the row below, at distances
     `k-1` and `k-2`.
3. **All pairs commute.** `𝒜(z+(j,m))` lies in the algebra of row `z_2` at positions `z_1 + j` to
   `z_1 + j + m`, for `m >= 0`.
4. **Finite presentation.** With `D = max(1, r)`, `sft-crossed-product-fp-iff-quantum-rigid` gives it.
5. **Periodicity.** `x(z+e_2) = φ(x(z), x(z+e_1))` is a sliding block code, so an `N`-periodic row
   has only `N`-periodic rows above it. Two of them coincide, and repeating the band between them
   gives a configuration whose `B_r`-patterns all occur. Columns: `x(z+e_1)` is a function of `x(z)`
   and `x(z+e_2)`.
