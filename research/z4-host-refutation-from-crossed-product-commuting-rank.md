---
rg: 2
id: z4-host-refutation-from-crossed-product-commuting-rank
kind: route
title: B_Ω ⊗ L_∂ is a Cantor crossed product by Z^2 × F_d, of cohomological dimension three, and Z^4 needs four independent commuting elements
target: f2-z4-has-no-embedding-in-z2-sft-boundary-product-hosts
requires: [cantor-crossed-products-bound-commuting-rank-by-cd]
---

1. **The host is a crossed product.** For compact totally disconnected `X, Y`, the map
   `f ⊗ g ↦ ((x, y) ↦ f(x) g(y))` is an isomorphism `LC(X, k) ⊗ LC(Y, k) -> LC(X × Y, k)`.
   - It is surjective, because clopen rectangles form a basis of `X × Y`, and a clopen set of the compact space
     `X × Y` is a finite disjoint union of clopen rectangles.
   - It is injective, as one sees by writing `f` and `g` on finite clopen partitions.

   So `(LC(X) ⋊ Γ_1) ⊗ (LC(Y) ⋊ Γ_2) ≅ LC(X × Y) ⋊ (Γ_1 × Γ_2)`, with the product action. The multiplication
   rules agree on the spanning elements `f u_g ⊗ h u_(g')`. Hence
   `B_Ω ⊗ L_∂ ≅ LC(Ω × ∂F_d, k) ⋊ (Z^2 × F_d)`, and `Ω × ∂F_d` is compact and totally disconnected.

2. **Cohomological dimension.** By Section 5 of `crossed-product-commuting-rank-via-diagonal-induction`, the
   trivial `k[Z^2 × F_d]`-module has a projective resolution of length `3`.

3. **The bound.** By `cantor-crossed-products-bound-commuting-rank-by-cd` with `s = 3`,
   `M_r(B_Ω ⊗ L_∂)` has no commuting independent family of size `4`.

4. **Laurent rings.** Let `φ : k[Z^4] -> M_r(B_Ω ⊗ L_∂)` be injective. Its restriction to
   `k[x_1, ..., x_4] ⊆ k[Z^4]` is injective, so by Section 4 of
   `polynomial-subring-flat-dimension-via-fraction-field-koszul`, `φ(x_1), ..., φ(x_4)` is a commuting
   independent family of size `4`. That contradicts step 3. ∎

**Remark on the corner reduction.** `f2-z4-embeds-in-z2-sft-boundary-product-hosts` allows embeddings into
corners `e(B_Ω ⊗ L_∂)e`. Such an embedding is a non-unital injective map into the host itself, so step 4
already covers it.
