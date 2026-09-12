---
rg: 2
id: redundant-intersection-edges-proof
kind: route
title: The deleted identifications already hold through the third subgroup, and forests have virtually free amalgams
target: intersection-edges-inside-a-third-subgroup-are-redundant
requires:
  - sofic-amalgam-finite-subgroup-idempotent-traces-are-strict
artifacts:
  - research/artifacts/laminar-cycle-overfilled-stars-2026-09-12.md
---

Proof: Section 2 of the artifact (Lemma 2.1, Corollaries 2.2 and 2.3).

1. **One edge.** If `g in D_ij <= H_l`, then `g in D_il n D_lj`, so `iota_i(g) = iota_l(g) = iota_j(g)` in
   the colimit without the edge `{i, j}`. The universal properties give inverse isomorphisms.
2. **Iteration.** An edge `{i, j}` with `D_ij != 1` and `D_ij <= H_l` has nontrivial `D_il` and `D_lj`. So
   the procedure's condition, that `{i, l}` and `{l, j}` are still present, is exactly what step 1 uses.
3. **Forests.** A tree of finite groups has a virtually free fundamental group (Corollary 2.4 of the
   `w4-kap-join` artifact), and Theorem 2.1 there gives positivity.
4. **Three subgroups.** `D_ij <= H_l` means `D_ij` equals the triple intersection. Deleting that edge
   leaves a path.
