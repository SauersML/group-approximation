---
rg: 2
id: binary-leavitt-unit-irrational-l2-betti-proof
kind: route
title: Kernel dimensions are unchanged by induction from the lamplighter cube inside V
target: binary-leavitt-unit-group-has-irrational-l2-betti-numbers
requires: [lamplighter-cube-embeds-in-binary-leavitt-unit-group, lamplighter-groups-have-irrational-l2-betti-numbers, lueck-dimension-additivity-cofinality-and-induction]
---

- Let `H = (Z/2 ≀ Z)^3 <= G` and `T in M_k(Q[H])` with irrational kernel dimension over `N(H)`.
- As an operator on `N(G)^k`, `T` is `N(G) ⊗_(N(H)) T`.
- Induction is exact, so its kernel is `N(G) ⊗_(N(H)) ker_(N(H)) T`.
- Induction preserves dimension, so `dim_(N(G)) ker T = dim_(N(H)) ker T`.
- Clearing denominators puts `T` over `Z[H] ⊆ Z[G]` without changing the kernel.
