---
rg: 2
id: pauli-tower-bundle-has-no-uniform-order-zero-m2-proof
kind: route
title: A scalar point of a − b kills one of two orthogonal positive elements, and equivalent pieces of an order zero map vanish together
target: pauli-tower-bundle-has-no-uniform-order-zero-m2
requires: [pauli-tower-bundle-has-scalar-point-property]
artifacts:
  - research/artifacts/tw-pauli-tower-scalar-point-bundle-2026-09-13.md
  - research/artifacts/tw-pauli-tower-scalar-point-bundle-part2-2026-09-13.md
---

Part 2, Section 1 (Theorem C, Corollaries C1–C2); the first-proved `1/4` bound is part 1, C2.
Review PASS (part 9 §9.6 of `research/artifacts/ex-review2-analysis-2026-09-13-part9.md`).

**Theorem C.** Let `a, b ≥ 0` with `ab = 0`, and take `λ` with `π_λ(a − b) = μ1` (prerequisite).
- `μ > 0`: `π_λ(a) ≥ μ1` is invertible, so `π_λ(b) = 0`.
- `μ < 0`: `π_λ(a) = 0`.
- `μ = 0`: `π_λ(a) = π_λ(b)` and `π_λ(a)² = π_λ(a)π_λ(b) = 0`.

**Corollary C1.** Apply Theorem C to `φ(e_{11}) ⊥ φ(e_{22})`. In the fibre,
`φ(e_{ii}) = π(e_{i1})φ(e_{11})π(e_{1i})` (Winter–Zacharias), so all pieces vanish together.

**Corollary C2.** Apply Theorem C to `p ⊥ 1 − p`.

**First-proved bound, kept for the record.**

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
