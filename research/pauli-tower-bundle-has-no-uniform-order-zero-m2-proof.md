---
rg: 2
id: pauli-tower-bundle-has-no-uniform-order-zero-m2-proof
kind: route
title: The image of a minimal projection under a large order zero M_2 has variance at least 1/4 − ε everywhere
target: pauli-tower-bundle-has-no-uniform-order-zero-m2
requires: [pauli-tower-bundle-has-scalar-point-property]
artifacts:
  - research/artifacts/tw-pauli-tower-scalar-point-bundle-2026-09-13.md
---

Section 5, C2 of the artifact. Unreviewed.

1. **Setup.**
   - Let `φ: M_2 → M` be c.p.c. order zero, `c = φ(1)`, with `ε_λ = τ_λ(1 − c) < 1/4` for every `λ`.
   - In each fibre `R`, Winter–Zacharias gives `φ = c·π(·)`, with `π` a supporting homomorphism
     commuting with `c`.
2. **Traces.** Put `y = φ(e_{11}) = cπ(e_{11})`.
   - Conjugating by the partial isometry `π(e_{12})`, which commutes with `c`, gives
     `τ_λ(cπ(e_{11})) = τ_λ(cπ(e_{22}))`, so `τ_λ(y) = τ_λ(c)/2 ≤ 1/2`.
   - Likewise `τ_λ(y²) = τ_λ(c²)/2`.
3. **Estimate.** `c − c² ≤ 1 − c`, so `τ_λ(c²) ≥ τ_λ(c) − τ_λ(1 − c) = 1 − 2ε_λ`. Then
   `Var_λ(y) = τ_λ(y²) − τ_λ(y)² ≥ (1 − 2ε_λ)/2 − 1/4 = 1/4 − ε_λ > 0` at every `λ`.
4. **Contradiction.** `y` is self-adjoint and nowhere scalar, contradicting the prerequisite.
5. **Reduced power.** A unital `M_2 ⊂ M^U` lifts, by projectivity of the cone over `M_2`, to order
   zero maps `M_2 → M` with `‖E(1 − φ(1))‖ → 0`.
