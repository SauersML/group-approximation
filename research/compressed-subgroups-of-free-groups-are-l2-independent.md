---
rg: 2
id: compressed-subgroups-of-free-groups-are-l2-independent
kind: claim
title: A finitely generated subgroup of a free group is compressed iff it is inert iff it is L2-independent
artifacts:
  - research/artifacts/fpbs-locally-free-fixed-pseudocost-2026-09-17.md
---

**ESTABLISHED (literature import).** Let `F` be a free group and `H` a
finitely generated subgroup. The following are equivalent:
- `H` is *compressed* in `F`: `rk H ≤ rk L` for every finitely generated
  `L ≤ F` containing `H`;
- `H` is *inert* in `F`: `rk(H ∩ L) ≤ rk L` for every finitely generated
  `L ≤ F`;
- `H` is *`L²`-independent* in `F`: the canonical map
  `D(F) ⊗_(Q[H]) I_(Q[H]) → D(F) ⊗_(Q[F]) I_(Q[F])` is injective. Here `D(F)`
  is the division closure of `Q[F]` in `U(F)`, which is a division ring by
  Linnell's theorem.

This confirms the Dicks–Ventura inert-versus-compressed problem.

Route: `compressed-subgroups-of-free-groups-are-l2-independent-citation`.
Downstream use: `locally-free-groups-first-l2-betti-equals-c-star-minus-one`.
