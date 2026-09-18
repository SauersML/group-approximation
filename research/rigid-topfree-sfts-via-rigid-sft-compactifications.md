---
rg: 2
id: rigid-topfree-sfts-via-rigid-sft-compactifications
kind: route
title: Embed the group in a finitely presented group with a rigid SFT compactification, then take the free product with Z to get a rigid minimal topologically free SFT
target: decidable-groups-lie-in-fp-groups-with-rigid-topfree-sfts
requires:
  - decidable-groups-embed-in-rigid-sft-compactification-groups
  - tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts
---

**Route** (lane bh-g2-buildings, 2026-09-18).

Let `G` be finitely generated with solvable word problem.

1. By (★𝒞) (`decidable-groups-embed-in-rigid-sft-compactification-groups`), choose a finitely presented
   `Λ_0 ≥ G` with a rigid SFT compactification `(Y, π)`.
2. `Λ = Λ_0 * Z` is finitely presented and contains `G`.
3. `tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts`, parts 1–3 with `Y_1 = C_Z`, gives
   an SFT `X` over `Λ`. It is minimal, topologically free, and `D`-quantum rigid over every field for all
   large `D`.

This is the target. ∎

## Status

**OPEN** through (★𝒞) alone. Step 3 is a lane proof (unreviewed).

- **Group side.** Feeding this into `boone-higman-via-v-times-rigid-topfree-sft-full-groups` leaves
  E3′ (`v-times-rigid-topologically-free-sft-full-groups-are-fp`) as the only other premise.
- **Ring side.** `boone-higman-via-leavitt-units-of-rigid-topologically-free-sfts` also needs
  torsion-free isotropy. Here that means that finite subgroups of `Λ_0` act freely on `∂Y`. It also
  needs the K-gate for `Λ_0 * Z`, which is a Farrell–Jones instance.

## Lesson for general BH

On this route the minimality gap of gate E1 does not arise. The tree of the free product makes a
non-minimal, deterministic object minimal and topologically free. So the existence side of the master
route asks for one kind of object, a rigid coordinate system on an overgroup.
