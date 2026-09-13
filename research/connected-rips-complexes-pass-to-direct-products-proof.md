---
rg: 2
id: connected-rips-complexes-pass-to-direct-products-proof
kind: route
title: Rescale both factors to scale 1, apply the l-infinity product formula, and multiply connectivity
target: connected-rips-complexes-pass-to-direct-products
requires:
  - contractible-rips-groups-closed-under-direct-products
  - group-rips-complexes-are-cayley-graph-flag-complexes
---

**Scale 1.** Let `R_t(G,S)` and `R_{t'}(H,S')` be (n−1)-connected with `n >= 1`.
By item 2 of `group-rips-complexes-are-cayley-graph-flag-complexes` ((a) ⇒ (b),
and the proof of (b) ⇒ (a)), `T_G = B_S(t) \ {1}` and `T_H = B_{S'}(t') \ {1}`
are finite symmetric generating sets not containing `1` (a connected clique
complex forces generation), and `R_1(G,T_G) = Flag(Cay(G,T_G)) = R_t(G,S)` and
`R_1(H,T_H) = R_{t'}(H,S')`. Both are (n−1)-connected.

**Product formula.** Item 3 of
`contractible-rips-groups-closed-under-direct-products`, applied with
`r = 1` to `(G,T_G)` and `(H,T_H)`, gives
`|R_1(G × H, T_G ⊠ T_H)| ≃ |R_1(G,T_G)| × |R_1(H,T_H)|`.

**Connectivity.** `π_k(X × Y) ≅ π_k(X) × π_k(Y)` for `k >= 1`, and a product of
nonempty path-connected spaces is path-connected. So the product of two
(n−1)-connected spaces is (n−1)-connected, and `R_1(G × H, T_G ⊠ T_H)` is an
(n−1)-connected Rips complex of `G × H`. ∎
