---
rg: 2
id: unit-type-rounding-via-laurent-vertex-rounding
kind: route
title: Round the Laurent vertex and restrict, since finite images of EL_r(F_q[x^±1]) invert every x_i
target: theorem-e-vertex-rounds-to-unit-type-representations
requires:
  - laurent-vertex-rounds-for-every-model
  - unit-type-vertex-rounding-forces-compressor-commutant-rigidity
artifacts:
  - research/artifacts/nh-h1-quantitative-2026-09-12.md
---

Full derivation in §6 of the artifact.

- **Rounding.** `laurent-vertex-rounds-for-every-model` gives genuine `ρ_n : Δ -> U(n')` close to `σ_n` on
  `F_Δ`. Every `s ∈ F_Γ` is a fixed word in `F_Δ`, so `π_n = ρ_n|Γ` is close to `σ_n` on `F_Γ`.
- **Root kernel.**
  - `ρ_n(e_12(L))` is an elementary abelian `p`-subgroup of `U(n')`, so its kernel `J_n` has finite index in `L`.
  - Signed permutation matrices lie in `Δ`, and `[e_13(g), e_32(f)] = e_12(gf)`. So `J_n` is an ideal, the root
    kernel of every root.
- **Factorization.** `I_n = J_n ∩ R_+` is the root kernel of `π_n`. Item 1 of
  `unit-type-vertex-rounding-forces-compressor-commutant-rigidity` factors `π_n` through `St_r(R_+/I_n)`.
- **Unit type.** `R_+/I_n` embeds in the finite ring `L/J_n`, where every `x_i` is a unit. The inverse of a unit
  in a finite ring is a positive power of it, so `x_i^(-1)` lies in `R_+/I_n`.
- That is the conclusion of `theorem-e-vertex-rounds-to-unit-type-representations`, with `P_n = 1`.

The route stays open while its first premise is open.
