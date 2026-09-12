---
rg: 2
id: hyperfinite-covariant-obstruction-lemma-proof
kind: route
title: The conditional expectation of ρ(g) onto the lamp closure intertwines id and α_g, so it vanishes
target: hyperfinite-covariant-obstruction-lemma
requires: []
artifacts:
  - research/artifacts/stw99-x2-unitary-subgroup-reduction-2026-08-30.md
---

Let `E : W → M` be the `τ_W`-preserving normal conditional expectation
(it exists because `W` is finite with faithful normal trace and `M` is a
von Neumann subalgebra).  Write `u_g = ρ(g)` for `g ∈ Σ` and
`x_g = E(u_g) ∈ M`.

1. **Intertwining.**  For `a ∈ M`, `u_g a = α_g(a) u_g` with `α_g(a) ∈ M`,
   so by `M`-bimodularity of `E`,
   `x_g a = E(u_g a) = E(α_g(a) u_g) = α_g(a) x_g`.
2. **Vanishing.**  By proper outerness, `x_g = 0` for `g ≠ e`.  Hence
   `τ_W(a u_g) = τ_W(E(a u_g)) = τ_W(a x_g) = 0` for all `a ∈ M`, `g ≠ e`;
   in particular `τ_W(u_g) = 0`.
3. **The group algebra.**  The character `g ↦ τ_W(u_g)` of `Σ` is `δ_e`, so
   the trace-preserving \*-homomorphism `C[Σ] → W`, `g ↦ u_g`, is
   injective with `τ_W` equal to the canonical trace of `C[Σ]`, and the
   von Neumann algebra `ρ(Σ)''` with the faithful normal trace `τ_W` is the
   completion of `(C[Σ], δ_e)`, i.e. `L(Σ)`.
4. **Injectivity.**  If `W` is injective, its von Neumann subalgebra
   `L(Σ) = ρ(Σ)''` is injective (finite case: the trace-preserving
   conditional expectation `W → ρ(Σ)''` transports injectivity), and
   `L(Σ)` is injective only for amenable `Σ` (Connes).

For the factor case: if `x a = α(a) x` for all `a ∈ M` then `x^*x` and
`xx^*` commute with `M`, hence are scalars, and a nonzero `x` normalises to
a unitary implementing `α`; so "outer" and "properly outer" agree when `M`
is a factor.  In general `x^*x, xx^* ∈ Z(M)`, so proper outerness fails
exactly when `α_g` is inner on some nonzero central piece of `M`.
