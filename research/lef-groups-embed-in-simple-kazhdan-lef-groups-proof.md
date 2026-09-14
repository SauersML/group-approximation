---
rg: 2
id: lef-groups-embed-in-simple-kazhdan-lef-groups-proof
kind: route
title: A finitely generated LEF group lies in a derived subgroup of a f.g. infinite LEF group, whose lamplighter crossed product has a simple Kazhdan LEF elementary group containing it
target: lef-groups-embed-in-simple-kazhdan-lef-groups
requires: [rf-groups-lie-in-derived-subgroups-of-rf-groups, lamplighter-bernoulli-crossed-products-simple-kazhdan-lef]
artifacts:
  - research/artifacts/sk-universal-embedding-b-lamplighter-2026-09-13.md
---

Let `Γ` be finitely generated and LEF.
1. **Overgroup.** `rf-groups-lie-in-derived-subgroups-of-rf-groups` (2) gives a finitely generated LEF `Δ` with
   `Γ ≤ [Δ, Δ]`. Replacing `Δ` by `Δ × Z` keeps it finitely generated, LEF and infinite, and the derived subgroup is
   unchanged.
2. **Host.** With `L = Z/2 ≀ Δ` acting on `2^Δ`, `lamplighter-bernoulli-crossed-products-simple-kazhdan-lef` (3)-(4)
   gives an infinite, finitely generated, simple group `G = EL_3(LC(2^Δ,F_2) ⋊ L)` with property (T) that is LEF.
   `ℓ ↦ diag(u_ℓ,1,1)` embeds `[L,L]` in `G`.
3. **Conclusion.** `Γ ≤ [Δ,Δ] ≤ [L,L] ↪ G`.

Converse: subgroups of LEF groups are LEF. So a finitely generated group is LEF if and only if it is a subgroup of an
infinite, finitely generated, simple Kazhdan LEF group. Artifact §3, Corollary 6.
