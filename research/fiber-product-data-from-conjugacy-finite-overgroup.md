---
rg: 2
id: fiber-product-data-from-conjugacy-finite-overgroup
kind: route
title: Take the normal subgroup to be the whole group
target: universal-fiber-product-data-for-word-problem-groups
requires: [every-wp-group-embeds-in-fp-conjugacy-finite-group]
artifacts:
  - research/artifacts/boone-higman-fiber-product-and-shift-compiler-2026-08-24.md
---

Given `T` finitely presented with `G <= T`, `Z(T) = 1` and finitely many
conjugacy classes, set `N = T` and `Q = 1`.  Then:

* `T` is finitely presented -- hypothesis;
* `N = T` is finitely generated -- a finitely presented group is;
* `Q = 1` is of type `F_infinity`, hence of type `F_3`;
* `C_T(N) = C_T(T) = Z(T) = 1` -- hypothesis;
* the `T`-conjugacy classes of `N` are the conjugacy classes of `T`, finitely
  many -- hypothesis.

So the fiber-product data holds.  `∎`

## Why this is a specialization and not a restatement

The prerequisite is strictly stronger than the target: it forces the normal
subgroup to be everything, which the target allows but does not require.  The
route is here so the stronger, shorter statement is a node someone can attack
directly, without a second route into `boone-higman-conjecture` that would
duplicate `boone-higman-via-fiber-product-criterion`.

One thing the specialization buys back: with `Q = 1` the fibre product is
`T x T`, finitely presented outright, so this branch does not use
`one-two-three-fibre-product-theorem` at all.  A reader who distrusts the
1-2-3 citation -- which was located through secondary sources and not read
from the primary -- can take this branch and lose nothing but generality.
