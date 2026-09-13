---
rg: 2
id: connected-rips-complexes-pass-to-direct-products
kind: claim
title: If G and H have (n-1)-connected Rips complexes then so does G x H
distinct_from:
  contractible-rips-groups-closed-under-direct-products: that is the product formula itself (for the l-infinity generating set the Rips complex of G x H is a categorical product, homotopy equivalent to the product of the factors' Rips complexes) with its contractibility consequences; this is only its (n-1)-connectivity consequence, the form Zaremsky Problem 4.4 needs
---

Let `n >= 1`. If the finitely generated groups `G` and `H` both admit
(n−1)-connected Rips complexes, so does `G × H`.

Explicitly, let `T_G` and `T_H` be finite symmetric generating sets of `G` and
`H` not containing `1`, with `Flag(Cay(G,T_G))` and `Flag(Cay(H,T_H))`
(n−1)-connected. Put `T = T_G ⊠ T_H = ((T_G ∪ {1}) × (T_H ∪ {1})) \ {(1,1)}`.
Then `R_1(G × H, T) = Flag(Cay(G × H, T))` is (n−1)-connected.

So the class of groups for which Zaremsky Problem 4.4 has a positive answer is
closed under finite direct products.

Credit: the homotopy equivalence
`R_1(G × H, T) ≃ R_1(G,T_G) × R_1(H,T_H)` is item 3 of
`contractible-rips-groups-closed-under-direct-products`. The first version of
this node's proof route (d140b64ad0: strong product plus Quillen's fiber lemma)
repeated that argument. The route now requires that claim.

Proof: `connected-rips-complexes-pass-to-direct-products-proof`.
