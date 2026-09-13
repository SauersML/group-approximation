---
rg: 2
id: one-compressor-actor-models-with-exact-origin-vertex-proof
kind: route
title: Stack the compressor pullbacks of one origin congruence quotient in cyclically shifted layers
target: one-compressor-actor-models-with-exact-origin-vertex
requires: [elementary-groups-over-fg-rings-have-property-t]
artifacts:
  - research/artifacts/hs-extension-one-compressor-origin-layers-2026-09-13.md
---

The full derivation is in §§0–4 of the artifact. Property (T) of `Γ` is used only for the uniqueness statement
in item 3.

1. **HNN.**
   - Normal forms `A^(-a)γA^b` map injectively into `G`. The `SL_d(Z)`-component `A^(b-a)` is trivial only if
     `a = b`.
   - If `a = b`, the element is the automorphism `A^(-a)` of `EL_r(F_q[x^(±1)])` applied to `γ`, which is trivial
     only if `γ = e`.
2. **Layers.** `ψ_(j+1) = ψ_j∘φ`, so `Sπ_N(γ)S^*` and `π_N(φ(γ))` agree on layers `0..N-1`, which gives the
   bound `2/√(N+1)`.
   - Moving `S`-powers through `π_N` a bounded number of times shows `σ_N` is an asymptotic homomorphism.
3. **Trace.**
   - Normal forms with `a ≠ b` shift the layers, so their trace is `0`.
   - For `a = b` and `γ ≠ e`, the trace is the fraction of `j <= N` with `ψ_j(γ) = 1`.
   - If `x^a` is a monomial of an entry of `γ - 1`, then `φ^j` of that entry contains `x^(A^j a)`, of degree
     `<= c_A^N |a| < k` once `N > |a|`. So `ψ_j(γ) ≠ 1` for every `j`.
4. **Origin type.**
   - `φ(m_0) ⊆ m_0`, so every `ψ_j` kills `Γ(m_0^k)`. The trivial constituents of `λ|ψ_j(Γ)` have trace
     `1/|ψ_j(Γ)|`.
   - `|ψ_N(Γ)| >= N`, because it contains `e_12(x^(m A^N e_1))` for `m < N`.
   - **Kazhdan uniqueness.** Take `ρ(g)X = π'(g)Xπ(g)^*` on `(M_D, ||·||_2)`. If two roundings are `ε`-close on
     `F_Γ`, the projection of `1` onto `Fix ρ` is an intertwiner `X_0` with `||1 - X_0||_2 <= ε/κ`.
   - Its polar part matches the two representations off trace `<= ε^2/κ^2`. Since unit type is a property of
     isomorphism classes, the non-unit masses of the two roundings agree up to `o(1)`.
5. **Commutant.**
   - Let `H_j = ψ_(j+1)(Γ)`. Multiplication by a sign constant on right `H_j`-cosets commutes with `λ(H_j)`.
   - Put `g_j = ψ_j(e_12(x_1)) = e_12(x^(A^j e_1))`. Then `g_j ∉ H_j`: `e_1 = Ab` has no solution `b ∈ N^d` when
     every entry of `A` is `>= 1` and `d >= 2`, and monomials of degree `< k` are independent mod `m_0^k`.
   - `H_j g_j y ≠ H_j y` for every `y`. So random signs give each average `avg_y f_j(g_j y)f_j(y)` expectation `0`;
     fix signs making them all `<= 0`.
   - Then `||[z_N, π_N(e_12(x_1))]||_2^2 >= 2`, while `z_N` commutes exactly with `π_N(φ(Γ))`.
   - Since `σ(A)σ(γ)σ(A)^* = σ(φ(γ))` in `M`, `σ(A)Rσ(A)^* = σ(φ(Γ))' ∩ M ∋ z`, and `z ∉ R`.
