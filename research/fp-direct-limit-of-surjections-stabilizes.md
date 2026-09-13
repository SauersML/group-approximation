---
rg: 2
id: fp-direct-limit-of-surjections-stabilizes
kind: claim
title: A finitely presented direct limit of surjections from a finitely generated group is isomorphic to a finite stage
---

Let `H_0` be a finitely generated group and `H_0 -> H_1 -> H_2 -> ...`
surjective homomorphisms with direct limit `G`. Equivalently `G = H_0/K`,
where `K` is the union of the increasing chain `K_i = ker(H_0 -> H_i)`.

If `G` is finitely presented, there is `i_0` with `K_i = K` for all
`i >= i_0`. Equivalently, the canonical maps `H_i -> G` are isomorphisms for
all `i >= i_0`.

This is the finite-presentation half of the fence
`fp-torsion-group-is-no-limit-of-non-torsion-groups` for Zaremsky
Problem 1.11.

Proof: `fp-direct-limit-of-surjections-stabilizes-proof`.
