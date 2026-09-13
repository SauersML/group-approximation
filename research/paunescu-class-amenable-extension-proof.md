---
rg: 2
id: paunescu-class-amenable-extension-proof
kind: route
title: Induce the sofic embedding of the kernel over Folner windows of the amenable quotient and complete the block partial permutations
target: paunescu-class-closed-under-amenable-extensions
requires: []
artifacts:
  - research/artifacts/paunescu-class-amenable-extensions-2026-09-12.md
---

# Proof

Full text: artifact Section 1. `α_g(f) = f∘g^{-1}`, `τ(f u_g) = δ_(g,1)∫f dμ`, `Q = G/N`,
`s : Q → G` a section with `s(1) = 1`, `h(g,q) = s(gq)^{-1} g s(q) ∈ N`. Then
`h(gg',q) = h(g,g'q)h(g',q)` and `h(g^{-1},gq) = h(g,q)^{-1}`.

1. **Window map.** For finite `F ⊆ Q` put
   `ψ_F(f) = Σ_(q∈F) e_(q,q) ⊗ α_(s(q)^{-1})(f)` and
   `ψ_F(u_g) = Σ_(q ∈ F ∩ g^{-1}F) e_(gq,q) ⊗ u_(h(g,q))`, and `ψ_F(f u_g) = ψ_F(f)ψ_F(u_g)`.
   * `ψ_F(u_g)^* = ψ_F(u_(g^{-1}))`; `ψ_F` is a ∗-homomorphism on `L^∞(X)`.
   * Covariance holds exactly: `u_(h(g,q)) α_(s(q)^{-1})(f) = α_(s(gq)^{-1}g)(f) u_(h(g,q))`, so
     `ψ_F(u_g)ψ_F(f) = ψ_F(α_g(f))ψ_F(u_g)`.
   * `ψ_F(u_g)ψ_F(u_(g')) − ψ_F(u_(gg'))` is a partial isometry supported on at most
     `|F ∖ g'^{-1}F|` of the `|F|` blocks.
   * Trace: `(tr_F ⊗ τ)(ψ_F(f)ψ_F(u_g))` averages `τ(α_(s(q)^{-1})(f) u_(h(g,q)))` over `q ∈ F`
     with `gq = q`. Freeness of `Q ↷ Q` forces `g ∈ N`, and then `h(g,q) = s(q)^{-1}gs(q) = 1`
     iff `g = 1`. So the trace equals `δ_(g,1) τ(f)` exactly.
2. **Permutations.** Compose with `id ⊗ Θ_N` for a sofic embedding `Θ_N` of `L^∞(X) ⋊ N`. Each
   `f` goes to a diagonal matrix. Each `u_g` goes to a block partial permutation with permutation
   blocks, missing `|F ∖ g^{-1}F|` blocks; completing it to a permutation moves it by at most
   `(2|F ∖ g^{-1}F|/|F|)^(1/2)` in `‖·‖_2` and moves the fixed-point fraction by at most
   `|F ∖ g^{-1}F|/|F|`.
3. **Limit.** Take a Følner sequence `F_m` of `Q`. For each `m` choose a finite stage of `Θ_N`
   accurate to `1/m` on the finitely many elements used by the first `m` words. The maps are
   asymptotically multiplicative and trace preserving on `L^∞(X) ⋊_alg G`, send the base into
   diagonal matrices and each `u_g` to a permutation. The ultraproduct over `m` is a
   trace-preserving ∗-homomorphism of the algebraic crossed product of the required shape, and it
   extends to the von Neumann crossed product (GNS for the trace). So `G ↷ X` is sofic.

**Class statement.** If `N ∈ 𝒮`, every restriction `N ↷ X` is sofic, so every `G ↷ X` is sofic.
