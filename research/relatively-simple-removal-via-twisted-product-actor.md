---
rg: 2
id: relatively-simple-removal-via-twisted-product-actor
kind: route
title: Let G x Λ act through Λ, pass to its abstract twisted Brin--Thompson group, and embed G along the graph of G → Λ
target: relatively-simple-removal-between-pbh-and-bh-of-quotient
requires:
  - a2-kernel-removal-via-product-with-image-actor
  - abstract-btb-pairs-fp-and-relatively-simple
  - abstract-btb-simple-quotient-fp-gate
  - fp-quotient-iff-kernel-finitely-normally-generated
  - simple-envelope-forces-solvable-word-problem
---

Notation as in the target.

**(a).** Let `j: G/N → Λ` be injective, where `Λ ↷ Ω` is of type (A_2), and let
`π: G → G/N` be the quotient map.
1. **The product actor.** Let `H = G x Λ` act on `Ω` through `Λ`, and put
   `ι_0(g) = (g, jπ(g))`. The computation in part (2 ⇒ 1) of
   `a2-kernel-removal-via-product-with-image-actor` applies verbatim with `N` in
   place of `K`:
   - `H ↷ Ω` is of type [A_2], with kernel `K_H = G x {1}`;
   - `ι_0` is injective and `ι_0(G) ∩ K_H = ι_0(N)`.

   That computation uses only that `G` is finitely presented, that `j` is
   injective and that `Λ` acts faithfully.
2. **The twisted group.** By `abstract-btb-pairs-fp-and-relatively-simple`
   (FFWZ Theorem 4.1(ii), Theorem 3.6, Lemma 5.2):
   - `SV_H` is finitely presented;
   - `(SV_H, SK_H)` is relatively simple;
   - `λ: H → SV_H` is injective with `λ(H) ∩ SK_H = λ(K_H)`.
3. **`SK_H` is finitely normally generated.** By definition `SK_H` is the kernel
   of `SV_H → SV_(H/K_H)`, whose target FFWZ call the simple quotient of `SV_H`
   (lines 67–72 and 114). Since `SV_H` is finitely presented and `H/K_H ≅ Λ` is
   finitely presented, `SV_(H/K_H)` is finitely presented by FFWZ Corollary 4.2
   (`abstract-btb-simple-quotient-fp-gate`). So `SK_H` is finitely normally
   generated in `SV_H` (`fp-quotient-iff-kernel-finitely-normally-generated`).
4. **The embedding.** Put `G′ = SV_H`, `N′ = SK_H` and `ι = λ ∘ ι_0`, which is
   injective. Then

   ```text
   ι(G) ∩ N′ = λ(ι_0(G)) ∩ λ(H) ∩ SK_H = λ(ι_0(G)) ∩ λ(K_H)
             = λ(ι_0(G) ∩ K_H) = λ(ι_0(N)) = ι(N),
   ```

   using injectivity of `λ` in the third equality.

**(b).** Let `(G′,N′)` and `ι` be as in the target.
- **Envelope.** `G′/N′` is finitely presented by
  `fp-quotient-iff-kernel-finitely-normally-generated`. It is simple, since
  `(G′,N′)` is relatively simple (FFWZ, after Definition 1.2).
- **Embedding.** `gN ↦ ι(g)N′` is well defined since `ι(N) ⊆ N′`. It is injective:
  `ι(g) ∈ N′` gives `ι(g) ∈ ι(G) ∩ N′ = ι(N)`, so `g ∈ N`.
- **Word problem.** By `simple-envelope-forces-solvable-word-problem`, the finitely
  generated subgroup `G/N` of `G′/N′` has solvable word problem. The words in a
  finite generating set of `G` that lie in `N` are exactly those trivial in `G/N`,
  so `N` is recursive. `∎`
