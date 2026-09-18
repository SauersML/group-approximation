---
rg: 2
id: cantor-crossed-hosts-via-boundary-products-of-z2-sft-hosts
kind: route
title: Take a finitely presented free minimal Z^2-SFT host and tensor it with the free-group boundary algebra
target: decidable-group-algebras-have-fp-cantor-crossed-hosts
requires:
  - decidable-algebras-embed-in-z2-sft-boundary-product-hosts
  - free-minimal-crossed-products-are-simple-with-rank-models
  - cantor-crossed-hosts-are-closed-under-boundary-products
artifacts:
  - research/artifacts/cantor-crossed-host-boundary-products-2026-09-17.md
---

Let `G` be finitely generated with solvable word problem.

1. `decidable-algebras-embed-in-z2-sft-boundary-product-hosts`
   gives `Ω`, `d` and a unital embedding `F_2[G] -> B_Ω ⊗ L_∂`, with `B_Ω`
   finitely presented.
2. `free-minimal-crossed-products-are-simple-with-rank-models`(1) makes `B_Ω`
   simple with centre `F_2`.
3. `Z^2` is torsion-free and satisfies FJCw: it is a CAT(0)-group (Wegner,
   arXiv:1308.2432, quoted in Section 2 of the artifact). So `(Z^2, Ω)` is a
   valid host.
4. `cantor-crossed-hosts-are-closed-under-boundary-products`(1, 2) makes
   `(Z^2 × F_d, Ω × ∂F_d)` a valid host with algebra `B_Ω ⊗ L_∂`. FJCw implies
   the target's Farrell–Jones hypothesis.

That is the target's statement, with `P = Z^2 × F_d` and `X = Ω × ∂F_d`.
