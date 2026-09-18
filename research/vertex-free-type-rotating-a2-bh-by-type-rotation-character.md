---
rg: 2
id: vertex-free-type-rotating-a2-bh-by-type-rotation-character
kind: route
title: Split vertex-free type rotating Ã₂ groups by their type-rotation character and use the type-transitive and type-preserving theorems
target: vertex-free-type-rotating-a2-groups-satisfy-boone-higman
requires:
  - type-transitive-vertex-free-a2-groups-embed-in-fp-simple-groups
  - type-preserving-vertex-free-a2-groups-embed-in-fp-simple-groups
---

Let `Γ` act freely on the vertices of a locally finite thick Ã₂ building by type rotating
automorphisms, with finitely many orbits. Its type-rotation character `θ : Γ -> Z/3` is
either nonzero or zero.

1. If `θ ≠ 0`, then `Γ` embeds in a finitely presented simple group by
   `type-transitive-vertex-free-a2-groups-embed-in-fp-simple-groups`.
2. If `θ = 0`, then `Γ` embeds in a finitely presented simple group by
   `type-preserving-vertex-free-a2-groups-embed-in-fp-simple-groups`.

This is the case distinction of the "Final update" on the target, recorded as a route by
bh-integrate (2026-09-18). It adds no mathematics. The first route,
`a2-boone-higman-via-rs-two-graph-full-groups`, is dead: its primitivity premise is refuted.
