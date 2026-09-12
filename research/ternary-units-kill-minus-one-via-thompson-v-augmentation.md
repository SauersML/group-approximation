---
rg: 2
id: ternary-units-kill-minus-one-via-thompson-v-augmentation
kind: route
title: A z-moving rank function on the ternary unit group restricts to the signed Thompson group and then to a non-augmentation rank function of V
target: sylvester-rank-functions-on-ternary-leavitt-units-kill-minus-one
requires: [thompson-v-ternary-rank-functions-are-augmentation, signed-thompson-z-moving-rank-functions-match-v-rank-functions]
artifacts:
  - research/artifacts/signed-thompson-minus-one-gate-is-v-rank-gate-2026-09-12.md
---

Artifact Section 4.3.
1. Let `rk` be a Sylvester matrix rank function on `F_3[G_3]` with `rk(1 - [z]) > 0`.
2. Its restriction to `F_3[E ⋊ V]` still moves `z`, since `z in E ⋊ V`.
3. By direction (1) ⟹ (2) of `signed-thompson-z-moving-rank-functions-match-v-rank-functions`, the restriction to
   `F_3[V]` is not the augmentation rank.
4. That contradicts `thompson-v-ternary-rank-functions-are-augmentation`.

The prerequisite is sufficient but not known to be necessary, and it is at least as strong as `V` failing to be
sofic. A proof of the target that avoids settling `V` must use elements of `G_3` outside `E ⋊ V`.
