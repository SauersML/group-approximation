---
rg: 2
id: ghb7-stability-via-one-edge-holonomy
kind: route
title: One-edge holonomy absorption for GHB_2(7) gives edge matching, hence flexible HS stability
target: ghb7-flexibly-hs-stable
requires:
  - ghb7-one-edge-holonomy-absorption
  - triangle-edge-matching-reduces-to-one-edge-holonomy
  - ghb7-triangle-vertex-groups-split-abelianizations
  - cckw-ghb2-kms-group-structure
---

1. **The triangle.** By item 2 of `cckw-ghb2-kms-group-structure`, `G = G_{HB_2}(7)` is the colimit
   of a triangle of finite groups with vertex groups `⟨a,b⟩, ⟨c,b⟩, ⟨c,a⟩` and cyclic edge groups
   `⟨a⟩, ⟨b⟩, ⟨c⟩` of prime order 7.
2. **(SPLIT).** Item 1 of `ghb7-triangle-vertex-groups-split-abelianizations`: each vertex
   abelianization is `(Z/7)^2` with its two edge generators as a basis.
3. **Reduction.** `triangle-edge-matching-reduces-to-one-edge-holonomy` applies. Its (HA) for this
   triangle is exactly `ghb7-one-edge-holonomy-absorption`, and it gives that `G` is flexibly HS
   stable, which is `ghb7-flexibly-hs-stable`. ∎
