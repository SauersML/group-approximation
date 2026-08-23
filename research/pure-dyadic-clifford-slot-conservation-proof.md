---
rg: 2
id: pure-dyadic-clifford-slot-conservation-proof
kind: route
title: Charge diagonal and adjacent matches to the same higher-end root slots
target: pure-dyadic-clifford-slots-have-a-uniform-one-third-gap
requires:
  - adjacent-clifford-orbit-transition-graph
  - pure-dyadic-regular-iwahori-mixtures-have-a-uniform-half-loss
---

Fix an exact-conductor irreducible of `G_a`, with `a>=2`.  Its restriction to the normal
newest layer `L_a` is supported on one nonzero Clifford orbit.  Since
`L_a=N_(a-1)/N_a` is contained in the upper Iwahori, every upper edge
constituent is nontrivial on `N_(a-1)` and trivial on `N_a`; its upper
conductor is exactly `a`.  The opposite statement is identical.  The joint
conductor table `(DRI4)` has support only on `(n,m)` with `|n-m|<=1`.
Therefore common constituents from vertex depths `a,b` require

```text
|a-b|<=1.                                                (DSP1)
```

This also explains why `O_0` is not a loophole: an `O_0` summand factors
through `G_(a-1)` and belongs to the lower exact-conductor band instead.

At equal depth, the common quotient kills the upper-root class on the plus
side and the lower-root class on the minus side.  Thus a plus newest-layer
character `(alpha,beta,gamma)` must have `beta=0`, a minus character must
have `gamma=0`, and their surviving `alpha` coordinates must agree.  In

```text
O_F={(1,1,1)},
O_A={(1,0,0),(1,0,1),(1,1,0)},
O_B={(0,1,0),(0,1,1),(0,0,1)},                         (DSP2)
```

this gives no fixed-orbit cell, two of three character spaces on each side
for `O_A`, and one of three on each side for `O_B`.  Equal Clifford
multiplicities therefore bound all same-depth `O_A` matches by

```text
(2/3)min(x_A,y_A).                                      (DSP3)
```

It remains to count every cell incident to `O_B`.  For a lower-plus to
higher-minus adjacent match, the higher endpoint is the character
`(0,1,0)` in the minus `O_B` orbit.  For the reverse orientation, the
higher-plus endpoint is `(0,0,1)`.  These are exactly the minus and plus
character spaces used by a same-depth `O_B` match: respectively
`gamma=0` and `beta=0`.  Hence, at each higher endpoint, the adjacent and
diagonal cells compete for one and the same physical eigenspace.  Its
dimension is one third of that endpoint's `O_B` mass.

Charge each adjacent match to its higher endpoint and charge each diagonal
`O_B` match to either of its two endpoint slots.  Orthogonality of distinct
common summands gives the aggregate bound

```text
C_B <= x_B/3+y_B/3.                                    (DSP4)
```

All adjacent arrows, including those sourced in `O_F` or `O_A`, land in
one of these charged `O_B` slots by `(COT2)`.  Equations
`(DSP1)--(DSP4)` exhaust every possible common constituent and prove the
first inequality in `(DCS2)`.

Finally `x_A+x_B<=d` and `y_A+y_B<=d`.  If, say,
`x_A<=y_A`, then

```text
(x_B+y_B)/3+(2/3)x_A
 <= (2d-x_A-y_A)/3+(2/3)x_A
 = 2d/3-(y_A-x_A)/3 <= 2d/3,                           (DSP5)
```

and the other case is symmetric.  This proves `(DCS1)`.  Projecting a
unitary onto the exact intertwiner space leaves squared normalized
Hilbert--Schmidt norm at most `2/3`, so its distance from that space is at
least `1/sqrt(3)`.  The uniform Iwahori Poincare constant `kappa_B` gives
`(DCS3)`.
