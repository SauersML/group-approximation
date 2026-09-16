---
rg: 2
id: binary-power-witness-from-upward-closed-sizes
kind: route
title: Push a failing size up to a power of two inside the same group
target: some-nonsurjunctive-group-gives-a-binary-power-one
requires:
  - nonsurjunctive-alphabet-sizes-are-upward-closed
---

Let `k ∈ NS_all`, witnessed by a group `G`, so `k ∈ NS(G)` and `k >= 2`. Choose `j >= 1` with `2^j >= k`. The
prerequisite gives `2^j ∈ NS(G) ⊆ NS_all`.
