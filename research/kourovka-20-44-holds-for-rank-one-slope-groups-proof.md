---
rg: 2
id: kourovka-20-44-holds-for-rank-one-slope-groups-proof
kind: route
title: "Case split on the slope group: V and the positive ray by frozen-tail invariants, the mixed-sign ray by trapped tails, rank two by Kohl's 3x+1 correspondence"
target: kourovka-20-44-holds-for-rank-one-slope-groups
requires:
  - ct-empty-z-subgroups-satisfy-the-orbit-transversal-dichotomy
  - ct-p-z-ray-cocycle-subgroups-satisfy-kourovka-20-44
  - ct-p-z-mixed-ray-frozen-tails-force-finite-orbits
  - ct-z-orbit-transversal-dichotomy-is-collatz-hard
---

Lane proof (bh-free-58, 2026-09-19). This route only assembles the cases.
- **Setup.** A finitely generated `G ≤ CT(Z)` lies in some `CT_P(Z)` with `P` finite. Its slope
  group `Γ` is a finitely generated subgroup of `Q_{>0}`, hence free abelian.
- **Rank one.** If rank `Γ ≤ 1`, then `Γ ≤ γ^Z` for a rational `γ > 1`. Either `γ` can be taken
  to be an integer (the positive-ray node, with the V node as its refereed special case), or
  `γ` and `1/γ` are both non-integral (the mixed-ray node, items 1–2).
- **Rank two.** The rank-two row is the Collatz-hardness node for Kohl's `G_T`.
