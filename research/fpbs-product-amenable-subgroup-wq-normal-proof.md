---
rg: 2
id: fpbs-product-amenable-subgroup-wq-normal-proof
kind: route
title: Centralize the amenable subgroup by the first factor or absorb the normal first factor
target: fpbs-product-amenable-subgroup-wq-normal
requires: []
---

Complete direct proof. By Popa's definition, as recalled in Hutchcroft--Pan
arXiv:2409.12283v1 Section 1.1, an infinite subgroup `B <= G` is wq-normal when
every intermediate subgroup `B <= I < G` admits some `g` outside `I` with
`g I g^(-1) ∩ I` infinite.

Put `B = {1} x A` and fix `I` with `B <= I < G`.

* If `H x {1}` is not contained in `I`, choose `g in H x {1}` with `g` not in
  `I`. Then `g` commutes with every element of `B`, so
  `g I g^(-1) ∩ I ⊇ g B g^(-1) = B`, which is infinite.
* If `H x {1} <= I`, choose any `g` not in `I`. Since `H x {1}` is normal in `G`,
  `g I g^(-1) ⊇ H x {1}`, so `g I g^(-1) ∩ I ⊇ H x {1}`, which is infinite
  because `H` is.

Hence `B` is wq-normal. It is amenable and infinite because `A` is.

Equivalently, in the ascending-chain form of the same reference:
`{1} x A` is normal in `H x A`, and `H x A` is s-normal in `H x K`, because for
`s = (x,y)` the intersection `s(H x A) ∩ (H x A)s = H x (yA ∩ Ay)` contains
`H x {y}`.
