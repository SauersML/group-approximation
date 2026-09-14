---
rg: 2
id: countable-lef-groups-embed-in-simple-kazhdan-lef-groups-proof
kind: route
title: Add a Z factor, embed in a 2-generated LEF group, then use the lamplighter host
target: countable-lef-groups-embed-in-simple-kazhdan-lef-groups
requires:
  - countable-lef-groups-embed-in-two-generator-lef-groups
  - lef-groups-embed-in-simple-kazhdan-lef-groups
artifacts:
  - research/artifacts/sk-universal-lef-host-b-2026-09-13.md
---

Artifact §2.

1. **⇐.** If `Γ ≤ S` and `S` is LEF, then an injective partial homomorphism of a finite subset of `S` restricts to one
   of any finite subset of `Γ`.
2. **⇒, infinite and LEF.** Let `Γ` be countable and LEF. `Γ × Z` is LEF: given partial models `φ: Γ -> Q` on a finite
   set `A` and `ψ: Z -> Z/N` injective on the finite set of second coordinates, `φ × ψ` is injective and multiplicative
   on `A × B`. It is countable and infinite.
3. **2-generated.** By `countable-lef-groups-embed-in-two-generator-lef-groups`, `Γ × Z ≤ Δ` with `Δ` 2-generated,
   infinite and LEF.
4. **Host.** By `lef-groups-embed-in-simple-kazhdan-lef-groups`, `Δ ≤ S` with `S` infinite, finitely generated, simple,
   Kazhdan and LEF. So `Γ ≤ Γ × Z ≤ S`. ∎
