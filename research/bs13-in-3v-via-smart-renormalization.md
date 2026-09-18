---
rg: 2
id: bs13-in-3v-via-smart-renormalization
kind: route
title: A height-3 renormalization of an infinite-order element of 2V gives BS(1,3) in 3V
target: bs13-embeds-in-brin-thompson-3v
requires:
  - smart-induced-map-has-brick-local-height-3-renormalization
  - renormalizable-thompson-elements-give-baumslag-solitar
---

`U ∈ 2V` has infinite order, since it has no periodic points: it factors onto `Z_3`
(`smart-level-zero-return-map-factors-onto-3-adic-odometer`). The pair `(A, φ)` is a height-3
renormalization in the sense of items 1–3 of
`renormalizable-thompson-elements-give-baumslag-solitar`. That node, with `k = 2` and `m = 3`, gives
`s = U × id ∈ 3V` and `u ∈ 3V` with `u s u^-1 = s^3`, so `BS(1,3) ≅ ⟨s, u⟩ ≤ 3V`.
