---
rg: 2
id: elementary-group-normal-subgroups-are-subsystem-kernels-via-k2
kind: route
title: The subsystem sandwich plus vanishing unstable K_2 gives the exact normal-subgroup dictionary
target: elementary-group-normal-subgroups-are-subsystem-kernels
requires: [aperiodic-subshift-el-normal-subgroups-are-sandwiched, aperiodic-subshift-ring-unstable-k2-vanishes]
artifacts:
  - research/artifacts/sk-open-1-subsystem-normal-subgroups-2026-09-13-part1.md
---

By the sandwich, every N ⊴ G_X has a unique Y with E_Y ≤ N ≤ ker π_Y, and ker π_Y / E_Y is the image of K_2(n, R_Y).

If K_2(n, R_Y) = 0 for all Y, then N = ker π_Y:
- N determines Y through I_N, so Y ↦ ker π_Y is injective;
- it is surjective by the sandwich, and it reverses inclusion;
- G_X / ker π_Y ≅ EL_n(R_Y), because π_Y is onto (elementary generators lift).
