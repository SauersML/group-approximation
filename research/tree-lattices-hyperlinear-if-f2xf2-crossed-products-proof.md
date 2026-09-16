---
rg: 2
id: tree-lattices-hyperlinear-if-f2xf2-crossed-products-proof
kind: route
title: Corner of the Coxeter complement's crossed product, then restriction to a free subgroup and induction to F2 x F2
target: tree-lattices-hyperlinear-if-f2xf2-crossed-products-ce
requires:
  - torsion-free-lattice-embeds-in-complement-crossed-product
  - hyperlinear-iff-group-factor-embeds-in-hyperfinite-ultrapower
artifacts:
  - research/artifacts/fournier-facio-simple-factor-corner-2026-09-16.md
---

Artifact Sections 2 and 3. "CE" means Connes-embeddable. CE passes to trace-preserving
subalgebras, to corners and to `M_n(·)`.

1. **Complement.** `W_a = C_2^{*a}` with involutions `s_1, ..., s_a`. Its Cayley graph is the
   `a`-regular tree: reduced words do not backtrack, so there are no cycles. Identify
   `T_a = Cay(W_a)` and `T_b = Cay(W_b)`. Then `Λ = W_a × W_b` acts on `T_a × T_b` by left
   multiplication, simply transitively on vertices.
2. **Hypotheses of the corner theorem.** Let `K = Stab(v_0) × Stab(w_0)`, which is compact open.
   - For `h ∈ H`, choose `λ ∈ Λ` with `λ(v_0,w_0) = h(v_0,w_0)`. Then `λ^{-1}h ∈ K`, so `H = ΛK`.
   - `Λ ∩ K = 1`, because `Λ` acts freely on vertices.
   - `S ∩ K = 1`, because `S` is torsion-free.
   By `torsion-free-lattice-embeds-in-complement-crossed-product`, `L(S)` is CE if
   `M = L^∞(H/S) ⋊ Λ` is CE.
3. **Free subgroup of finite index.** Let `K_a = ker(W_a → C_2^a)`, `s_i ↦ e_i`, of index `2^a`.
   - A finite-order element of a free product is conjugate into a factor. Every conjugate of `s_i`
     maps to `e_i ≠ 0`. So `K_a` is torsion-free, hence free by Kurosh.
   - Its rank `r_a` is at least `2`, because `W_a` is not virtually cyclic.
   - Put `Λ_0 = K_a × K_b`.
4. **Restriction.** With `Λ = ⊔_i Λ_0 g_i`, the map `π(x)_{ij} = E_0(v_{g_i} x v_{g_j}^*)`
   (`E_0` onto `M_0 = L^∞(H/S) ⋊ Λ_0`) is a unital trace-preserving *-embedding
   `M → M_{[Λ:Λ_0]}(M_0)`. The proof is artifact Lemma 2, from `z = Σ_j v_{g_j}^* E_0(v_{g_j} z)`.
   So `M` is CE if `M_0` is.
5. **Induction.** `F_r` is isomorphic to a subgroup of index `r − 1` of `F_2`. So `Λ_0` is
   isomorphic to a finite-index subgroup `Γ_0` of `Γ = F_2 × F_2`.
   - Let `Y = Γ ×_{Γ_0} (H/S)` be the induced p.m.p. action, and `q = 1_{[e, H/S]}`.
   - Then `a v_h ↦ ã v_h q` embeds `M_0` trace-preservingly into `q(L^∞(Y) ⋊ Γ)q` (artifact
     Lemma 3).
   - So `M_0` is CE if `L^∞(Y) ⋊ Γ` is CE, which holds by hypothesis.
6. **Conclusion.** By steps 5, 4 and 2, `L(S)` is CE. By
   `hyperlinear-iff-group-factor-embeds-in-hyperfinite-ultrapower`, `S` is hyperlinear.
7. **Contrapositive.** `L^∞(Y) ⋊ Γ ⊂ L^∞(Y × {0,1}^Γ) ⋊ Γ` is trace-preserving, and the
   diagonal action with the Bernoulli shift is essentially free. So a non-CE crossed product
   stays non-CE after this upgrade. ∎
