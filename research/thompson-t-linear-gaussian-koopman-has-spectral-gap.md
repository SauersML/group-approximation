---
rg: 2
id: thompson-t-linear-gaussian-koopman-has-spectral-gap
kind: claim
title: "Class kill for the linear Gaussian route: in the Dirichlet-space model of Thompson's T, PSL_2(Z) acts by Moebius maps, so the linear Gaussian Koopman representation is trivial plus tempered on PSL_2(Z), while every element with a breakpoint moves the vacuum; hence it has no almost invariant vectors, and part 3 of the symplectic Gaussian splitting never applies to T"
distinct_from:
  symplectic-gaussian-actions-split-area-cocycles: that proves the splitting and makes almost invariance of the linear Gaussian Koopman representation kappa_0 sufficient; this proves that for Thompson's T in the Dirichlet model kappa_0 has no almost invariant vectors, so that sufficient condition is false here
  thompson-t-dirichlet-space-restricted-symplectic-model: that builds the restricted symplectic model; this computes its Moebius part and the spectral gap it forces on the Gaussian Koopman representation
  thompson-t-bernoulli-euler-splittings-need-amenable-f: that kills Bernoulli and weakly mixing Gaussian pmp witnesses through spectral gap on F_A x F_B; this kills a nonsingular, non-measure-preserving Gaussian candidate through spectral gap on PSL_2(Z) and the Hellinger defect of one non-Moebius element, with no pmp assumption
  lifted-thompson-t-euler-class-in-kahler-subspace: its w13 spark asks whether M tensor M-bar has almost invariant vectors for T; this answers the Gaussian-Koopman form of that question negatively (the identification with M tensor M-bar is a remark, not established)
artifacts: []
---

**ESTABLISHED** by `thompson-t-linear-gaussian-koopman-has-spectral-gap-proof`.

Notation of `symplectic-gaussian-actions-split-area-cocycles`: `(H, ω, J)`, `ρ : Q → Sp_res`,
`γ` the standard Gaussian measure, `ρ(g)^` the measurable linear extension, and
`κ₀(g) = κ(ρ(g)^)` with `κ(A)f = (dA_*γ/dγ)^{1/2} f∘A^{-1}` on `L²(X, γ)`.

**Theorem A (general criterion).** Let `ρ : Q → Sp_res(H, ω, J)` and suppose:
1. there is a nonamenable subgroup `Γ ≤ Q` such that each `ρ(g)`, `g ∈ Γ`, is orthogonal and the
   complexification `ρ_C|_Γ` on `H_C` is unitarily equivalent to a subrepresentation of a
   multiple of the regular representation `λ_Γ`;
2. some `h ∈ Q` has `ρ(h)` not orthogonal.

Then there are a finite `F ⊆ Γ` and `ε > 0` with `max_{g ∈ F ∪ {h}} ‖κ₀(g)ξ − ξ‖ ≥ ε‖ξ‖` for
all `ξ ∈ L²(X, γ)`. In particular `κ₀` has no almost invariant vectors.

**Theorem B (Thompson's T).** In the smoothed model of
`thompson-t-dirichlet-space-restricted-symplectic-model`
(`H = H^{1/2}(R/Z)/R`, `ρ(g)φ = φ∘g^{-1}`, `c(g) = u_{g^{-1}}`):
1. The breakpoint-free elements `Γ = PSL_2(Z)` act on `R/Z ≅ ∂D` by disc automorphisms (`ψ₀`
   is a Cayley transform). For them `ρ(g)` is orthogonal and commutes with `J`.
2. `ρ_C|_Γ` is the sum of the weight-2 holomorphic discrete series (on the Bergman space) and its
   conjugate, restricted to `Γ`. It is contained in a multiple of `λ_Γ`.
3. `ρ(g)` is orthogonal only if `g ∈ PSL_2(Z)`. For example `g_0 ∈ PPSL_2(Z)`, equal to `x` on
   `[∞, 0]`, to `x/(x+1)` on `[0, 1]`, to `1/(3 − x)` on `[1, 2]` and to `x − 1` on `[2, ∞]`, has
   `ρ(g_0)` not orthogonal.
4. Hence Theorem A applies with `Γ = PSL_2(Z)` and `h = g_0`. **The linear Gaussian Koopman
   representation `κ₀` of `T` has no almost invariant vectors**, and part 3 of
   `symplectic-gaussian-actions-split-area-cocycles` gives nothing for `T` in this model.
5. The cocycle `c` is unbounded on the parabolic subgroup `⟨P⟩`, `P(x) = x + 1`:
   `‖c(P^n)‖ → ∞`. So the affine action `A^t` restricted to `PSL_2(Z)` has no fixed point, and it
   is not conjugate by a translation to the measure-preserving linear action. The argument of
   Theorem A therefore does **not** transfer to the affine Koopman representations `κ_t`, `t ≠ 0`.

## What is killed

- *Class.* Every witness for `thompson-t-euler-class-splits-over-almost-invariant-space` obtained
  from almost invariant vectors of `κ₀` of this model, by rescaling as in part 3 of the splitting
  lemma.
- *Invariant.* Spectral gap of `PSL_2(Z)` on the chaos part `1^⊥ ⊂ L²(γ)`, which is tempered.
- *Step where every member dies.* Almost invariant vectors must tend to the vacuum `1`. But the
  non-Moebius element `g_0` moves the vacuum by the fixed Hellinger amount
  `‖κ₀(g_0)1 − 1‖ > 0`.
- The residual hole is the affine one:
  `thompson-t-affine-dirichlet-koopman-almost-invariant`. Theorem B.5
  says why this argument does not close it.

## Remarks (not established)

- *`M ⊗ M̄`.* Let `L²(γ)` be the Fock space of `H_C = H_J ⊕ \bar{H_J}`. Then
  `κ₀(g)` implements the Bogoliubov map `ρ(g) ⊕ ρ(g)^{*-1}`. Via `(x, y) ↦ (x, J^{-1}y)` followed
  by a 45° rotation, this map is symplectically conjugate to `ρ(g) ⊕ ρ(g)` on
  `(H, −ω) ⊕ (H, ω)`. So `κ₀` and `M ⊗ M̄` implement the same Bogoliubov maps. Both are genuine
  representations, and `T` is perfect, so they should agree.
  - Independently of this identification, the proof of Theorem A runs verbatim for
    `M ⊗ M̄`. It needs only two standard facts, not re-read here:
    - `M(u) = phase · Γ(u)` for unitary `u`;
    - `M(S)Ω ∝ Ω` only when `[S, J] = 0`.
  - So the w13 spark's condition "M ⊗ M̄ has almost invariant vectors for T" fails in this model.
- *Other models.* Theorem A kills the linear Gaussian route in any restricted symplectic model of
  `T` that contains a nonamenable subgroup acting by Moebius maps (tempered weight-2 part). A
  model without such a subgroup, for instance a `C^∞` model of Ghys–Sergiescu type, is not
  covered.
