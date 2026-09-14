---
rg: 2
id: periodic-word-model-representations-no-strong-convergence-proof
kind: route
title: Congruence representations on an embedded SL_4 over Laurent polynomials carry Magee-de la Salle invariant vectors, which give a norm-4 outlier
target: periodic-word-model-representations-never-converge-strongly
requires:
  - lef-models-are-congruence-representations-on-laurent-lattices
  - sl4-over-finite-chain-rings-has-sl2-invariant-vectors
  - ring-model-permutation-vectors-block-strong-convergence
artifacts:
  - research/artifacts/sk-cstar-mf-firewall-2026-09-13.md
---

1. **Embedded lattice.** Tower of height `k = 2`: `V ∩ TV = ∅`. By
   `subshift-elementary-groups-contain-laurent-sl-n-lattices` (required by
   `lef-models-are-congruence-representations-on-laurent-lattices`), `Λ = SL_6(F_q[u_V^{±1}]) ≤ G`. Its upper-left
   `SL_4` contains an upper-left `SL_2(F_q[u_V^{±1}])`.
2. **Free pair.** `SL_2(F_q[u])` contains a free group of rank 2. This is item 3 of
   `ring-model-permutation-vectors-block-strong-convergence`, reviewed PASS, Nagao. Take free generators `S,T`.
   Their images under the injective ring map `u ↦ u_V` still generate a free group. Put `z = S+S^{-1}+T+T^{-1}`.
   - `λ_G` restricted to `⟨S,T⟩` is a multiple of `λ_{F_2}`, so `‖λ_G(z)‖ = 2√3 < 4` (Kesten).
3. **Congruence on Λ.** By `lef-models-are-congruence-representations-on-laurent-lattices`, for large `ℓ`,
   `φ_ℓ = Ψ_ℓ` on `{S^{±1}, T^{±1}}`. Here `Ψ_ℓ : Λ → GL_{3m_ℓ}(F_q)` is a genuine homomorphism through `SL_6(A_ℓ)`,
   with `A_ℓ = F_q[Q_ℓ] ≅ F_q[t]/(minimal polynomial of Q_ℓ)`, a finite principal ideal ring.
4. **Invariant vectors.** `ρ_ℓ∘Ψ_ℓ` restricted to the upper-left `SL_4(A_ℓ)` is a unitary representation. By
   `sl4-over-finite-chain-rings-has-sl2-invariant-vectors` it has a unit vector `ξ_ℓ` fixed by `SL_2(A_ℓ)`, which
   contains `Ψ_ℓ(S), Ψ_ℓ(T)`. So `ρ_ℓφ_ℓ(z)ξ_ℓ = 4ξ_ℓ`, and `‖ρ_ℓφ_ℓ(z)‖ = 4` for large `ℓ`.
   - Strong convergence would require `lim ‖ρ_ℓφ_ℓ(z)‖ = 2√3`. It fails.
5. **General exactly matricial models (item 2).** Replace `φ_ℓ` by `σ_ℓ`.
   - Multiplicativity on windows makes `σ_ℓ(e_V)`, `σ_ℓ(ε_ij)` and `σ_ℓ(u_V^{±1})` satisfy the matrix-unit and
     inverse relations exactly for large `ℓ`, with `σ_ℓ(u_V^a) = σ_ℓ(u_V)^a` for bounded `|a|`.
   - `A_ℓ = F_ℓ[σ_ℓ(u_V)]`, on the `σ_ℓ(e_V)`-corner, is a quotient of `F_ℓ[t]`, hence a finite principal ideal ring.
   - `Ψ_ℓ` is defined by `t ↦ σ_ℓ(u_V)` and the matrix units, and steps 2–4 apply unchanged.
