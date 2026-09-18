---
rg: 2
id: cocompact-fuchsian-groups-embed-in-v-all-or-none
kind: claim
title: The subgroups of Thompson's group V are closed under abstract commensurability, so either every cocompact Fuchsian group embeds in V or none does
distinct_from:
  virtually-special-groups-embed-in-brin-thompson-citation: that imports Belk--Bleak--Matucci's remark that groups virtually embedding in nV embed in nV; this gives a self-contained proof for V and applies it to the Fuchsian commensurability class.
  closed-hyperbolic-surface-groups-embed-in-thompson-v: that is the open survey Question 4.7; this shows its surface-group form is a single question for the whole commensurability class of the genus-2 surface group.
artifacts:
  - research/artifacts/gq-bh-bh-bbmz-problems-status.md
---

**ESTABLISHED** by `cocompact-fuchsian-groups-v-all-or-none-proof` (lane proof,
elementary, not reviewed; no priority claimed). Part 1 is a remark in
Belk--Bleak--Matucci arXiv:1602.08635 after Corollary 1.3, as quoted in
`virtually-special-groups-embed-in-brin-thompson-citation`, where it is stated for every nV.

1. **Commensurability closure.** Let `H ≤ G` have finite index. If `H` embeds in
   `V`, so does `G`. Subgroups of subgroups of `V` embed in `V`, so the class of
   groups embeddable in `V` is closed under abstract commensurability.
2. **The Fuchsian class.** The following groups are pairwise abstractly
   commensurable:
   - every cocompact Fuchsian group (a cocompact lattice in `PSL_2(R)`, torsion
     allowed, e.g. the triangle groups `Δ(p,q,r)` with `1/p + 1/q + 1/r < 1`);
   - every closed hyperbolic surface group, orientable or not;
   - `π_1(Σ_2)`.

   So either all of them embed in `V` or none does.
