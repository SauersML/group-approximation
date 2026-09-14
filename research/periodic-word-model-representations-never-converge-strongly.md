---
rg: 2
id: periodic-word-model-representations-never-converge-strongly
kind: claim
title: No unitary representations of the finite models of EL_3 over a minimal subshift converge strongly to the regular representation, cuspidal and Steinberg ones included
distinct_from:
  ring-model-permutation-vectors-block-strong-convergence: that excludes model representations containing the column permutation module; this excludes EVERY unitary representation of the models, through Magee-de la Salle invariant vectors on an embedded SL_4 over Laurent polynomials.
  minimally-almost-periodic-groups-are-not-pmf: that excludes genuine representations of G_X; this excludes the non-genuine asymptotic representations induced from the exact finite ring models.
---

**ESTABLISHED (unreviewed).** Let `X` be an infinite minimal subshift, `q` a prime power, `R = LC(X,F_q)⋊_T Z`
and `G = EL_3(R)`.

1. **Periodic-word models.** Let `φ_ℓ` be the note's periodic-word models of `R`, extended entrywise, and `ρ_ℓ` any
   unitary representations of `GL_{3m_ℓ}(F_q)` (irreducible cuspidal, Steinberg, regular, anything). Then
   `ρ_ℓ∘φ_ℓ` does not converge strongly to `λ_G`.
2. **Every exactly matricial model.** The same holds for any maps `σ_ℓ : R → M_{N_ℓ}(F_ℓ)` over finite fields that
   are unital, additive and multiplicative on exhausting windows, and any unitary representations `ρ_ℓ` of any
   finite groups containing `σ_ℓ(window)` in `GL_3(M_{N_ℓ}(F_ℓ))`.

**Witness.** Take a tower `V ⊔ TV`, the first-return unit `u_V`, and the copy `SL_4(F_q[u_V^{±1}]) ≤ G`. Let `S,T`
generate a free group in `SL_2(F_q[u])`, placed in the upper-left block through `u ↦ u_V`, and put
`z = S + S^{-1} + T + T^{-1}`.
- `‖λ_G(z)‖ = 2√3`, the Kesten norm of `F_2`.
- For large `ℓ`, `‖ρ_ℓφ_ℓ(z)‖ = 4`: on the embedded lattice the models are genuine representations of
  `SL_4(A_ℓ)` over a finite principal ideal ring, which have `SL_2(A_ℓ)`-invariant vectors.

**Consequence.** An MF embedding of `C*_r(G)`, if one exists, needs asymptotic representations that are not genuine
on any embedded `SL_4(F_q[t^{±1}])`. In particular they do not come from any representation of any exact ring model.
This closes the heuristic route "cuspidal-type irreducibles of the finite models" recorded in
`directly-finite-subshift-el-n-reduced-cstar-is-mf`.

Proof: route `periodic-word-model-representations-no-strong-convergence-proof`.
