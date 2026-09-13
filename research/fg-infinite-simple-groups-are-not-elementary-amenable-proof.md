---
rg: 2
id: fg-infinite-simple-groups-are-not-elementary-amenable-proof
kind: route
title: Finitely generated simple sections stay finite or abelian throughout the elementary amenable class
target: fg-infinite-simple-groups-are-not-elementary-amenable
requires: []
artifacts:
  - research/artifacts/zp-fp-simple-amenable-obstructions-2026-09-13-part1.md
---

## Why sufficient

Full proof in the artifact, Section 2.

1. **The auxiliary class.** A *section* of `G` is `H/K` with `K ◁ H ≤ G`. Let `𝒞`
   be the class of groups whose finitely generated simple sections are all finite
   or abelian.
2. **Base.** Finite and abelian groups lie in `𝒞`.
3. **Subgroups and quotients.** Sections of subgroups and of quotients of `G` are
   sections of `G`.
4. **Extensions.** Let `N ◁ G` with `N, G/N ∈ 𝒞`, and `S = H/K` finitely generated
   and simple. The normal subgroup `(H ∩ N)K/K` of `S` is trivial or everything.
   - If trivial, `S` is a quotient of `HN/N ≤ G/N`.
   - If everything, `S ≅ (H ∩ N)/(H ∩ N ∩ K)` is a section of `N`.
5. **Directed unions.** Finitely many elements of `H` whose images generate `S` lie
   in one `G_i`. They generate `H_0` with `H_0 K = H`, so `S ≅ H_0/(H_0 ∩ K)` is a
   section of `G_i`.
6. **Conclusion.** `EG ⊆ 𝒞`. A finitely generated infinite simple group is a
   finitely generated simple section of itself that is neither finite nor abelian,
   so it is not in `EG`.
