---
rg: 2
id: cantor-crossed-clopen-symbols-factor-through-coinvariants
kind: claim
title: In a ring over a Cantor Γ-system, the K_2 symbols of locally constant rational units factor through the dimension group tensor K_2(Q)
distinct_from:
  matricial-divisibility-kills-rational-k2-symbols: that kills the image of K_2(Q) at the unit class through a matrix decomposition; this treats every clopen corner at once, through the Γ-coinvariants of LC(X,Z).
  full-corners-must-kill-rational-k2-symbols: that is the necessary condition for a finitely presented E_N at each full corner; this computes, for clopen corners of any ring over a Cantor Γ-system, the group those corner images generate.
  infinitely-generated-symbols-block-fp-elementary-groups: that says an infinitely generated symbol group blocks finite presentation; this identifies the locally constant part of the symbol group as a quotient of H_0(Γ; LC(X,Z)) ⊗ K_2(Q).
artifacts:
  - research/artifacts/gq-gq-k2-q-toeplitz-k2.md
---

**ESTABLISHED (2026-09-18)** through
`cantor-crossed-clopen-symbols-factor-through-coinvariants-proof`. Lane proof (gq-k2-q), elementary,
not independently reviewed. Inputs are textbook facts listed in the route.

## Setting

- `Γ` acts by homeomorphisms on a compact totally disconnected space `X`.
- `R` is a unital ring with a unital ring map `j : LC(X,Q) -> R` and units `u_γ` (`γ ∈ Γ`) such that
  `u_γ j(φ) u_γ^(-1) = j(φ ∘ γ^(-1))`. Example: any subring of `C(X,Q) ⋊_alg Γ` containing `LC(X,Q)` and
  all `u_γ`, such as `R_T` of `sl3-toeplitz-harmonic-ring-is-simple-and-k1-rational`.
- `D_X = H_0(Γ; LC(X,Z))`, the coinvariants (the dimension group of the system).
- For a clopen `U` and `λ ∈ Q^x` put `e_U(λ) = 1 + (λ - 1)χ_U`. The *clopen symbol*
  `s_U(λ,μ) = {j e_U(λ), j e_U(μ)} ∈ K_2(R)` is a Steinberg symbol of commuting units.

## Statement

1. There is a homomorphism `σ : D_X ⊗ K_2(Q) -> K_2(R)` with `σ([χ_U] ⊗ {λ,μ}) = s_U(λ,μ)`. Its image is
   the image of `K_2(LC(X,Q)) -> K_2(R)`. That image contains every symbol `{a,b}` of units
   `a, b ∈ LC(X,Q)^x`, in particular every `{λ, a}` with `λ ∈ Q^x`.
2. If `[χ_U] ∈ D_X` is divisible by every positive integer, then `s_U(λ,μ) = 0` for all `λ, μ`. If `D_X`
   is divisible, `K_2(LC(X,Q)) -> K_2(R)` is zero.
3. **Odometer factors.** Let `π : X -> K = lim Γ/Γ_n` be a continuous surjective `Γ`-map onto an odometer
   of finite-index normal subgroups, and suppose every positive integer divides some `[Γ : Γ_n]`. Then the
   image of `H_0(Γ; LC(K,Z))` in `D_X` is divisible, and `σ` factors through an isomorphism
   `D_X ⊗ K_2(Q) ≅ H_0(Γ; Q_X) ⊗ K_2(Q)`, where `Q_X = LC(X,Z) / π^* LC(K,Z)` is the *hole module*. In
   particular `s_U = 0` whenever `U = π^(-1)(V)` for a clopen `V ⊆ K`.
4. **Instance.** For `R_T` (`Γ = SL_3(Z)`, `Γ_n = Γ((n+1)!)`) part 3 applies. The locally constant part
   of `Sym(R_T)`, and the image of `K_2(Q)` in every clopen corner `χ_U R_T χ_U`, are governed by
   `H_0(Γ; Q_X) ⊗ K_2(Q)` alone. This is R1 at clopen corners and the locally constant part of R2 in
   `sl3-toeplitz-harmonic-ring-meets-the-uhf-k-budget`.
