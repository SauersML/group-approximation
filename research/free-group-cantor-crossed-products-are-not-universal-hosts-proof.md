---
rg: 2
id: free-group-cantor-crossed-products-are-not-universal-hosts-proof
kind: route
title: Finite presentation makes the space an SFT, tree SFT hosts have doubly exponential unit word problems, and complexity-bounded classes miss a decidable group
target: free-group-cantor-crossed-products-are-not-universal-hosts
requires:
  - fp-crossed-products-force-sft-over-any-group
  - free-group-sft-host-units-have-doubly-exponential-wp
  - complexity-bounded-host-classes-are-not-universal
artifacts:
  - research/artifacts/fp-crossed-product-shape-free-group-kill-2026-09-17.md
  - research/artifacts/fjc-crossed-product-leavitt-hosts-2026-09-16.md
---

This is Corollary D of the 2026-09-17 artifact (Section 5).

1. **The class.** Let `K` be the class of finitely generated subgroups of unit groups
   `(LC(X,k) ⋊ F_d)^x`, over all `d >= 0`, nonempty SFTs `X` and finite fields `k`. By
   `free-group-sft-host-units-have-doubly-exponential-wp`, every member has a
   word-problem algorithm in time `C * T(C l)` with `T(l) = 2^(2^l)`. By
   `complexity-bounded-host-classes-are-not-universal`, some two-generated decidable `H` embeds in
   no member of `K`.
2. **Reduction to SFTs.** Suppose `B = LC(X,k) ⋊ F_d` is finitely presented and `k[H] -> B` is a
   unital embedding. `B` is finitely generated. By Lemma 6.1 of
   `fjc-crossed-product-leavitt-hosts-2026-09-16`, `X` is conjugate to an `F_d`-subshift. The
   conjugacy induces an isomorphism of crossed products, which is still finitely presented. By
   `fp-crossed-products-force-sft-over-any-group`, the subshift is an SFT.
3. **Contradiction.** The embedding restricts to an injective homomorphism `H -> B^x`, since distinct
   group elements are distinct basis vectors of `k[H]`. The image is a finitely generated subgroup
   of `B^x`, a member of `K`, which contradicts step 1. `∎`
