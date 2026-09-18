---
rg: 2
id: graph-houghton-bh-via-eventually-rigid-g-automorphisms
kind: route
title: Graph Houghton groups satisfy permutational Boone–Higman if one eventually rigid G-automorphism group P_G(r) is finitely presented
target: graph-houghton-groups-satisfy-boone-higman
requires:
  - graph-houghton-groups-embed-in-eventually-rigid-g-automorphisms
  - eventually-rigid-g-automorphism-groups-act-with-type-a-except-fp
  - eventually-rigid-g-automorphism-groups-are-finitely-presented
  - type-a-action-gives-boone-higman-for-subgroups
  - boone-higman-type-a-class-closed-under-finite-extensions
artifacts:
  - research/artifacts/gq-bh-bh-graph-houghton-reduction.md
---

Deduction, for r ≥ 3 with P_G(r) finitely presented, and G finitely presented, simple and MIF (for example Thompson's V):
1. P_G(r) acts on the finitely supported G-homomorphisms Φ. The action is faithful and highly transitive, and has
   finitely generated point stabilizers (`eventually-rigid-g-automorphism-groups-act-with-type-a-except-fp`).
   Together with finite presentation (the open gate) the action is of type (A).
2. PB_r ≤ P_G(r) (`graph-houghton-groups-embed-in-eventually-rigid-g-automorphisms`), so PB_r embeds in a
   finitely presented simple group (`type-a-action-gives-boone-higman-for-subgroups`).
3. B_r contains PB_r with index r!, so B_r also lies in the permutational class
   (`boone-higman-type-a-class-closed-under-finite-extensions`).

This would answer the printed question of Hill–Kwak–Udall–West positively. It would also put every Aut(F_n) inside one actor, but its proof uses BFFHZ's finite-rank lemmas, so it is not independent
of BFFHZ. Modulo the cited faithfulness, it would cover the surface and braided Houghton groups too.
