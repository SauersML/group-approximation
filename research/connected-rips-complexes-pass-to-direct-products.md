---
rg: 2
id: connected-rips-complexes-pass-to-direct-products
kind: claim
title: If G and H have (n-1)-connected Rips complexes then so does G x H
---

Let `G` and `H` be finitely generated groups with finite symmetric sets
`T_G ⊆ G \ {1}` and `T_H ⊆ H \ {1}`, and put
`T = ((T_G ∪ {1}) × (T_H ∪ {1})) \ {(1,1)}`. Then
`Flag(Cay(G × H, T)) ≃ Flag(Cay(G,T_G)) × Flag(Cay(H,T_H))`.

Consequently (`group-rips-complexes-are-cayley-graph-flag-complexes`): if `G`
and `H` both admit (n−1)-connected Rips complexes, so does `G × H`, since a
product of (n−1)-connected spaces is (n−1)-connected. The class of groups for
which Zaremsky Problem 4.4 has a positive answer is closed under finite direct
products.

This is the group form of the homotopy equivalence between the clique complex
of a strong product of graphs and the product of the clique complexes
(equivalently, between Vietoris–Rips complexes of an `l^∞`-product and the
product of Vietoris–Rips complexes; prior literature exists for the metric
form). Proof: `connected-rips-complexes-pass-to-direct-products-proof`.
