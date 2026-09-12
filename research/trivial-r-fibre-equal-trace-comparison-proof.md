---
rg: 2
id: trivial-r-fibre-equal-trace-comparison-proof
kind: route
title: Glue local partial isometries with central projections cut from a Lebesgue-distributed relative commutant element
target: trivial-r-fibre-bundles-compare-equal-trace-projections
requires: []
artifacts:
  - research/artifacts/tw-hilbert-cube-projection-invariant-2026-09-12.md
---

**Established by derivation**, Theorem 1 and Corollary 2 of the artifact.

1. **Local pieces.** At each `μ`, choose `v_μ` in `R` with `v_μ*v_μ = P(μ)` and
   `v_μ v_μ* = Q(μ)`. The constant section is an `ε_0`-good approximate
   equivalence on an open `U_μ`. Take finitely many `U_i` covering `K`.
2. **Finite-dimensional carrier.** The data `{P(λ), Q(λ)} ∪ {v_i, v_i*}` is
   `‖·‖_2`-compact. By Dini, one finite-dimensional unital subalgebra `D`
   approximates all of it within `ε_0`.
3. **Central partition of unity.** `h ∈ D' ∩ R` has Lebesgue distribution. The
   projections `p_i(λ) = χ_{[s_{i−1}(λ), s_i(λ))}(h)` are orthogonal, sum to `1`,
   commute with `D`, have `τ(p_i(λ) y) = f_i(λ) τ(y)` for `y ∈ D`, and are
   `‖·‖_2`-continuous in `λ`.
4. **Gluing.** `Z = Σ p_i E_D(v_i)` has `‖Z*Z − P‖_{2,u}, ‖ZZ* − Q‖_{2,u} < 5ε_0`,
   by orthogonality and the product rule.
5. **Corner.** `W = QZP` then has defects at most `4(5ε_0)^{1/2} + 5ε_0`.
6. **Criterion.** Bundle isomorphisms preserve `E` and `‖·‖_{2,u}`.
