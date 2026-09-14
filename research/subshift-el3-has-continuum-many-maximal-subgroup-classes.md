---
rg: 2
id: subshift-el3-has-continuum-many-maximal-subgroup-classes
kind: claim
title: EL_3(LC(X,F_2)⋊Z) has continuum many conjugacy classes of maximal subgroups of infinite index, the point stabilizers of its orbit-module actions
artifacts:
  - research/artifacts/sk-free-2-maximal-subgroups-2026-09-13-part1.md
  - research/artifacts/sk-free-2-maximal-subgroups-2026-09-13-part2.md
---

**ESTABLISHED (unreviewed)** via `subshift-el3-has-continuum-many-maximal-subgroup-classes-proof`.

Let `X` be an infinite minimal subshift and `G = EL_3(LC(X,F_2) ⋊ Z)`. For `x ∈ X` let `H_x` be the stabilizer of `δ_0 e_1` in the orbit module `V_x^3`.
- Each `H_x` is a maximal subgroup of infinite index.
- `H_x ∩ e_21(LC(X,F_2)) = e_21(𝔪_x)`, so `x ↦ H_x` is injective.

Consequences:
- `G` has continuum many conjugacy classes of maximal subgroups;
- `G` has continuum many pairwise non-isomorphic faithful 2-transitive actions on countable sets.

The conjugacy classes are classified by `subshift-el3-orbit-stabilizers-conjugate-iff-same-orbit`: `H_x ∼ H_y` iff `x` and `y` lie in one `T`-orbit.
