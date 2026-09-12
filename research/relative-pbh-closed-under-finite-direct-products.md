---
rg: 2
id: relative-pbh-closed-under-finite-direct-products
kind: claim
title: Sharp embeddings in type [A_2] pairs, and removability of their kernels, pass to finite direct products
distinct_from:
  boone-higman-type-a-class-closed-under-finite-extensions: that is closure of the faithful permutational class B_A under products and finite-index overgroups; this is closure of the RELATIVE form, where the actors may have kernels that the embedded groups meet trivially, together with closure of kernel removability.
  boone-higman-implies-relative-permutational-bh: that places one Boone--Higman group sharply inside one type [A_2] actor; this combines two such actors into one for the product group.
  a2-pairs-embed-in-a2-pairs-with-fng-kernels: that asks that every type [A_2] pair admit a kernel-removing sharp embedding; this shows that removability, when it holds for two pairs, holds for their product pair.
artifacts:
  - research/artifacts/bh-product-closure-2026-09-12.md
---

**ESTABLISHED** by `relative-pbh-finite-direct-products-proof` (elementary).

Terminology is that of Fournier-Facio--Wu--Zaremsky, arXiv:2603.24687v2, read from
the PDF text on MSI:
- **Definition 1.6.** "(G,N) embeds in (G′,N′) if there exists an injective
  homomorphism ι: G ֒→ G′ such that ι(G) ∩ N′ = ι(N). We say a group Γ sharply
  embeds in a normal pair (G,N) if the normal pair (Γ,{1}) embeds in (G,N)."
- **Type [A_2]** (as recorded in `boone-higman-implies-relative-permutational-bh`):
  G finitely presented, point stabilizers finitely generated, finitely many
  G-orbits on S x S. The action need not be faithful.

**Statement.** For i = 1, 2 let G_i act on a nonempty set S_i with type [A_2] and
kernel K_i. Let G = G_1 x G_2 act on S = S_1 ⊔ S_2 coordinatewise.
1. The action of G on S is of type [A_2], its kernel is K_1 x K_2, and its action
   image G/K is (G_1/K_1) x (G_2/K_2) acting on S_1 ⊔ S_2.
2. If Γ_i sharply embeds in (G_i, K_i) for i = 1, 2, then Γ_1 x Γ_2 sharply
   embeds in (G, K_1 x K_2).
3. If each (G_i, K_i) embeds in a type [A_2] pair (G_i′, K_i′) with K_i′ finitely
   normally generated in G_i′, then (G, K_1 x K_2) embeds in the type [A_2] pair
   (G_1′ x G_2′, K_1′ x K_2′), whose kernel is finitely normally generated.

**Consequences.**
- The relative permutational Boone--Higman property (FFWZ Conjecture 1.8) is
  closed under finite direct products.
- For products, the whole gap between the relative and the faithful form is the
  gap for each factor: the product action image is finitely presented exactly
  when both factor images are.

**Not claimed.** Closure of the Boone--Higman class itself under direct products.
That is the open claim `boone-higman-closed-under-finite-direct-products`, and
this lemma is the input to its route `bh-product-closure-via-a2-kernel-removal`.

**Credit.** No novelty is claimed. The disjoint-union construction is the same
one used for faithful type (A) actions in Zaremsky, arXiv:2405.18354,
Proposition 5.6, which BFFHZ cite for stability of PBH under direct products.
