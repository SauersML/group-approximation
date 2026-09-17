---
rg: 2
id: decidable-simple-fa-hosts-via-kazhdan-lamplighter-proof
kind: route
title: Take the simple Kazhdan lamplighter host of the same word problem degree, which has property FA
target: decidable-groups-embed-in-decidable-simple-fa-groups
requires: [fg-groups-have-simple-kazhdan-hosts-of-same-wp-degree, property-t-implies-property-fa]
artifacts: [research/artifacts/lamplighter-kazhdan-host-without-lef-2026-09-17.md]
---

Let `G` be finitely generated with solvable word problem. By
`fg-groups-have-simple-kazhdan-hosts-of-same-wp-degree`, `G` embeds in an
infinite finitely generated simple group `H = EL_3(LC(2^Δ,F_2) ⋊ (Z/2 ≀ Δ))`,
`Δ = G × Z`, with property (T) and `WP(H) ≤_T WP(G)`, so `WP(H)` is solvable.
By `property-t-implies-property-fa`, `H` has property FA.
