---
rg: 2
id: closed-mcg-bh-via-edge-split-operad
kind: route
title: If the edge-split operad in rank 6g-6 has Ore's condition and finite type, closed mapping class groups of genus g at least three satisfy Boone-Higman
target: closed-surface-mapping-class-groups-satisfy-boone-higman
requires:
  - edge-split-operad-satisfies-ore
  - ore-operad-groups-contain-the-derived-full-group
  - ore-operad-groups-have-type-a-clopen-actions
  - closed-mcg-embeds-in-rational-projective-full-group
  - transvections-are-single-carets-of-the-edge-split-operad
  - non-lcm-dissection-operad-groups-are-f-infinity
  - type-a-action-gives-boone-higman-for-subgroups
---

Lane bh-free-54, 2026-09-18. Let `g ≥ 3` and `m = 6g − 7`.

1. **The embedding.** `closed-mcg-embeds-in-rational-projective-full-group` embeds
   `Mod(S_g)` in `𝒯_m = [[GL_{m+1}(Z) ⋉ Ŝ_m]]`.
2. **The host.** Assume `edge-split-operad-satisfies-ore` in rank `m + 1`: Ore's
   condition and a finite spine. Then the edge-split group `G_E` is `F_∞`
   (`non-lcm-dissection-operad-groups-are-f-infinity`).
3. **The mapping class group lies in the host.**
   - `GL_{m+1}(Z) ≤ G_E` (`transvections-are-single-carets-of-the-edge-split-operad`),
     and it is germ-generating.
   - So `ore-operad-groups-contain-the-derived-full-group` gives `G_E ⊇ D(𝒯_m)`.
   - `Mod(S_g)` is perfect for `g ≥ 3` (Powell; recalled). Hence `Mod(S_g) ≤ G_E`.
4. **The type (A) action.** By `ore-operad-groups-have-type-a-clopen-actions`, `G_E`
   acts with type (A) on its accessible clopen sets.
5. **Conclusion.** By `type-a-action-gives-boone-higman-for-subgroups`, `Mod(S_g)`
   (as a subgroup of `G_E`) embeds in a finitely presented simple group.

This route replaces the finite-presentation gate
`rational-projective-full-groups-are-finitely-presented` of the full host by the
edge-split gate. It never needs `G_E = 𝒯_m`, a coding of Dehn twists, or finite
generation of the canonical operad `𝒪_m`, whose prime dissections look unbounded.
