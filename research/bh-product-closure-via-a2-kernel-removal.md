---
rg: 2
id: bh-product-closure-via-a2-kernel-removal
kind: route
title: Put both simple envelopes in relative actors, multiply the actors, remove the product kernel and quotient
target: boone-higman-closed-under-finite-direct-products
requires:
  - boone-higman-implies-relative-permutational-bh
  - relative-pbh-closed-under-finite-direct-products
  - a2-pairs-embed-in-a2-pairs-with-fng-kernels
  - type-a-action-gives-boone-higman-for-subgroups
artifacts:
  - research/artifacts/bh-product-closure-2026-09-12.md
---

Let G ≤ S_1 and H ≤ S_2 with S_1, S_2 finitely presented simple. Since G x H ≤
S_1 x S_2, it suffices to embed S_1 x S_2 in a finitely presented simple group.

1. **Relative actors.** Each S_i is finitely generated, has solvable word problem
   (Kuznetsov) and satisfies Boone--Higman trivially. By FFWZ Theorem C,
   `boone-higman-implies-relative-permutational-bh`, S_i sharply embeds in
   (G_i, K_i) for some type [A_2] action G_i ↷ X_i with kernel K_i.
2. **Product actor.** By `relative-pbh-closed-under-finite-direct-products`, S_1 x S_2
   sharply embeds in (G, K) with G = G_1 x G_2 acting on X_1 ⊔ X_2 with type [A_2]
   and kernel K = K_1 x K_2.
3. **Kernel removal.** By `a2-pairs-embed-in-a2-pairs-with-fng-kernels`, the first
   part of FFWZ Question 5.9, (G, K) sharply embeds in a type [A_2] pair (G′, K′)
   with G′ ↷ X′ and K′ = ker(G′ ↷ X′) finitely normally generated. Let
   j: G → G′ be the embedding, so j(G) ∩ K′ = j(K). Then
   j(S_1 x S_2) ∩ K′ = j(S_1 x S_2) ∩ j(G) ∩ K′ = j((S_1 x S_2) ∩ K) = {1},
   so S_1 x S_2 embeds in Λ = G′/K′.
4. **Faithful type (A).** Λ acts faithfully on X′.
   - Λ is finitely presented, as G′ is finitely presented and K′ is finitely
     normally generated.
   - Point stabilizers of Λ are images of point stabilizers of G′, hence finitely
     generated.
   - Finitely many orbits on X′ x X′ give finitely many orbits of two-element
     subsets.
   So Λ ↷ X′ is of type (A).
5. **Envelope.** By Zaremsky's Corollary B,
   `type-a-action-gives-boone-higman-for-subgroups`, every subgroup of Λ, in
   particular S_1 x S_2 and hence G x H, embeds in a finitely presented simple
   group.

**What this route shows.** Closure under direct products is no harder than the
kernel-removal question for type [A_2] pairs. Applying step 3 to each factor
separately would already give PBH for S_i, and then the known closure
`boone-higman-type-a-class-closed-under-finite-extensions` also gives the product.
This route uses only the product pair.
