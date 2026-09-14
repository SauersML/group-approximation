---
rg: 2
id: laurent-elements-of-cantor-crossed-products-are-suitable-proof
kind: route
title: A Chinese-remainder projection on each tower block, glued by translation covariance of the residues, gives the exchange idempotent
target: laurent-elements-of-cantor-crossed-products-are-suitable
requires: [laurent-right-ideals-of-cantor-crossed-products-columnwise]
artifacts:
  - research/artifacts/sk-algebraic-putnam-2026-09-13-part1.md
---

Notation as in `laurent-right-ideals-of-cantor-crossed-products-columnwise`, including the residue maps `ρ_q : V → F[u]/(q_0)`, `δ_t ↦ ū^t`.

1. **Trivial cases.** If `p = 0` take `e = 0`; if `p = 1` take `e = 1`.
2. **Normalize.** Otherwise write `p = u^αp_0` and `1−p = u^βr_0` with `p_0(0), r_0(0) ≠ 0`. `p_0` and `r_0` are coprime, since a common factor divides `p` and `1−p`. Put `A_p = F[u]/(p_0)`, `A_{1−p} = F[u]/(r_0)`, `D = deg p_0 + deg r_0`.
3. **Towers.** Choose a Kakutani–Rokhlin partition `𝒫` with bases `B_a` and heights `h_a ≥ D`. This is possible for a minimal Cantor system, by Herman–Putnam–Skau.
   - The block-diagonal operators with a matrix `G_a ∈ M_{h_a}(F)` on each occurrence of type `a` form `A_𝒫 = span{e_{T^{i′}B_a}u^{i′−i}} ⊆ R`.
   - `e_{T^{i′}B_a}u^{i′−i}` sends `δ_{b+i} ↦ δ_{b+i′}` for base positions `b` of type `a` and kills the other basis vectors.
4. **One block.** On `F^h`, `ρ^0 = (ρ_p, ρ_{1−p})`, `δ_i ↦ (ū^i, ū^i)`, is the quotient map onto `F[u]/(p_0r_0) ≅ A_p × A_{1−p}` (Chinese remainder theorem). It is onto, since `h ≥ D` consecutive powers of the unit `ū` span `F[u]/(p_0r_0)`.
   - Let `K = ker ρ^0`, and choose subspaces `C_p` and `C_{1−p}` mapped by `ρ^0` isomorphically onto `A_p × 0` and `0 × A_{1−p}`. So `F^h = K ⊕ C_p ⊕ C_{1−p}`.
   - Let `E_h` be the projection onto `C_{1−p}` along `K ⊕ C_p`. Then `ρ_p∘E_h = 0` and `ρ_{1−p}∘(1−E_h) = 0`.
5. **Glue.** Put `e = Σ_a Σ_{i,i′}E_{h_a}(i′,i) e_{T^{i′}B_a}u^{i′−i} ∈ A_𝒫`. It is idempotent.
   - For `t = b+i` in an occurrence, `ρ_p(eδ_t) = Σ_{i′}E_h(i′,i)ū^{b+i′} = ū^b ρ_p(E_hδ_i) = 0`.
   - Likewise `ρ_{1−p}((1−e)δ_t) = ū^b ρ_{1−p}((1−E_h)δ_i) = 0`.
6. **Conclude.** By the lemma, `e ∈ p_0R = pR` and `1 − e ∈ r_0R = (1−p)R`. ∎

**Model test.** For the one-point system `R = F[u^{±1}]`, the argument dies at step 3: there are no towers. Indeed `u+u² ∈ F_2[u^{±1}]` is not suitable.
