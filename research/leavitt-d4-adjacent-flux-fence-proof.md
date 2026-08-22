---
rg: 2
id: leavitt-d4-adjacent-flux-fence-proof
kind: route
title: Retract the adjacent source equations onto all four coefficient copies
target: leavitt-d4-adjacent-flux-fence
requires: []
---

Label the ten coefficient slots `g0,...,g9` and set

```text
U=g7 g3,  V=g8 g2 g4,  W=g9 g1 g5,  X=g0 g6.
```

The exact derivation of all twelve retractions is recorded in
`research/artifacts/derive-degree4-adjacent-projections.py`.  Take the
adjacent source pair `R0=R1=1`.  Four of its retractions are

```text
(R0)_0 = g6 U^-1 g0,
(R1)_0 = g5 U^-1 g9 g1,
(R1)_1 = g6 V^-1 g0.
```

They give, by cyclic rearrangement,

```text
X=U,  W=U,  X=V,
```

and hence `U=V=W=X`.  The four retractions of the remaining residual are

```text
(R2)_0 = g4 U^-1 g8 g2,
(R2)_1 = g5 V^-1 g9 g1,
(R2)_2 = g6 W^-1 g0,
(R2)_3 = X g3 X^-1 g7 X^-1.
```

The first three vanish from `U=V`, `V=W`, and `W=X`.  The last vanishes
after `X=U=g7g3`:

```text
U g3 U^-1 g7 U^-1 = 1.
```

Thus all free-copy retractions of `R2` are trivial.  If `R2` were the
reduced one-copy word `h_j` for `h!=1`, its retraction to copy `j` would be
`h`, a contradiction.  Cyclic rotation gives the other adjacent source
pairs.  No relation in the coefficient group was used.

