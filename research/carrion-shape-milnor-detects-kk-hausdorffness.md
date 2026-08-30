---
rg: 2
id: carrion-shape-milnor-detects-kk-hausdorffness
kind: claim
title: A shape-system derived limit exactly detects Hausdorffness of KK
distinct_from:
  stw99-problem-v-kk-hausdorff-q-stable: that asks whether Q-stability of the target always kills the closure of zero; this theorem identifies that closure with a derived limit but does not prove its vanishing for Q-stable targets.
artifacts:
  - research/artifacts/stw-operator-literature-exact-imports-2026-08-30.md
---

Let `A` and `B` be separable C-star algebras, with `A` nuclear, and let
`(C_n,gamma_n)` be a shape system for `SA tensor K`.  There is a natural
short exact sequence

```text
0 -> lim^1 [C_n,S^2 B tensor K]
  -> KK(A,B)
  -> lim [C_n,SB tensor K]
  -> 0,
```

and the image of the left map is exactly the closure of zero in the natural
topology on `KK(A,B)`.  Consequently,

```text
KK(A,B) is Hausdorff  iff  lim^1 [C_n,S^2 B tensor K] = 0.
```

In particular, Hausdorffness holds if the tower
`([C_n,S^2 B tensor K])_n` is Mittag--Leffler.

This is an exact obstruction theorem.  It does not assert that separable
`Q`-stability of `B` makes the displayed derived limit vanish.
