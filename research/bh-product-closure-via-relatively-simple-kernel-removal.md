---
rg: 2
id: bh-product-closure-via-relatively-simple-kernel-removal
kind: route
title: Put the product in a relatively simple twisted Brin--Thompson group, remove its largest normal subgroup and quotient
target: boone-higman-closed-under-finite-direct-products
requires:
  - boone-higman-implies-relative-permutational-bh
  - relative-pbh-closed-under-finite-direct-products
  - abstract-btb-pairs-fp-and-relatively-simple
  - fp-relatively-simple-pairs-embed-with-fng-kernels
artifacts:
  - research/artifacts/bh-simple-products-embed-2026-09-12.md
---

Let `G ≤ S_1` and `H ≤ S_2` with `S_1`, `S_2` finitely presented simple. Since
`G x H ≤ S_1 x S_2`, it suffices to embed `S_1 x S_2` in a finitely presented
simple group.

1. **Relative actors.** By FFWZ Theorem C
   (`boone-higman-implies-relative-permutational-bh`), `S_i` sharply embeds in
   `(A_i, K_i)` for a type [A_2] action `A_i ↷ X_i` with kernel `K_i`.
2. **Product actor.** By `relative-pbh-closed-under-finite-direct-products`,
   `S_1 x S_2` sharply embeds in `(A, K)`. Here `A = A_1 x A_2` acts on
   `X_1 ⊔ X_2` with type [A_2] and kernel `K = K_1 x K_2`.
3. **Relatively simple group.** By `abstract-btb-pairs-fp-and-relatively-simple`,
   `SV_A` is finitely presented and `(SV_A, SK_A)` is relatively simple. The image
   `P` of `S_1 x S_2` in `SV_A` satisfies `P ∩ SK_A = 1`.
4. **Removal.** By `fp-relatively-simple-pairs-embed-with-fng-kernels`, the second
   part of FFWZ Question 5.9, there are:
   - a finitely presented relatively simple `(G′, N′)` with `N′` finitely normally
     generated;
   - an injective `ι: SV_A → G′` with `ι(SV_A) ∩ N′ = ι(SK_A)`.

   Then `ι(P) ∩ N′ = ι(P) ∩ ι(SV_A) ∩ N′ = ι(P ∩ SK_A) = 1`.
5. **Envelope.** `G′/N′` is finitely presented, since `G′` is and `N′` is finitely
   normally generated. It is simple, since `(G′,N′)` is relatively simple. By
   step 4 it contains `S_1 x S_2`, hence `G x H`.

**How this differs from `bh-product-closure-via-a2-kernel-removal`.**
- That route removes the kernel of the product action with the first part of
  Question 5.9, and ends with Zaremsky's Corollary B.
- This one removes the largest normal subgroup of a relatively simple group with
  the second part, and the quotient is already simple.
- Neither premise is known to imply the other
  (`fp-relatively-simple-pairs-embed-with-fng-kernels`, Attempt 2).
