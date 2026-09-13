---
rg: 2
id: quasi-linear-pbh-via-coordinate-projections
kind: route
title: Project to each field, put each projection in B_A through self-similar hosts of its characteristic, and use permanence of B_A under products
target: quasi-linear-groups-satisfy-permutational-boone-higman
requires:
  - char-zero-linear-groups-satisfy-permutational-boone-higman
  - char-p-linear-groups-satisfy-permutational-boone-higman
  - boone-higman-type-a-class-closed-under-finite-extensions
---

Direct proof (2026-09-13, lane `bh-metabelian`). Let `π_i` be the coordinate
projections and `G_i = π_i(G) <= GL_(n_i)(K_i)`.

1. **The factors.** Each `G_i` is finitely generated, as a quotient of `G`.
   - If `char K_i = 0`, then `G_i` is in `B_A` by
     `char-zero-linear-groups-satisfy-permutational-boone-higman`.
   - If `char K_i = p > 0`, then `G_i` is in `B_A` by
     `char-p-linear-groups-satisfy-permutational-boone-higman`.
2. **The product.** `g -> (π_1(g), ..., π_r(g))` embeds `G` in
   `G_1 x ... x G_r`. By part 1 of
   `boone-higman-type-a-class-closed-under-finite-extensions`, `B_A` is closed under
   finite direct products and subgroups. So `G` is in `B_A`.
3. **Conclusion.** By part 3 of the same claim, `G` has solvable word problem and
   embeds in a finitely presented simple group. ∎

**What this avoids.** No step takes a product of simple envelopes. The product is
taken of groups that act, and the open `boone-higman-closed-under-finite-direct-products`
is never used.
