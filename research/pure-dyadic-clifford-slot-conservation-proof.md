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

Let `U,D,S_B` be as in `(DCS2a)`. The lower-plus/higher-minus cells and the
diagonal cell compete in the minus `gamma=0` slot, while the reverse cells
and the same diagonal cell compete in the plus `beta=0` slot. Orthogonality
therefore gives

```text
U+S_B<=y_B/3,                 D+S_B<=x_B/3.             (DSP4a)
```

Adding and subtracting the once-double-counted diagonal cell gives

```text
C_B=U+D+S_B <= (x_B+y_B)/3-S_B
               <=x_B/3+y_B/3.                          (DSP4)
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

For `(DCS4)`, cells with both endpoints of conductor at most one contribute
at most `min(b_+,b_-)`. By `(DSP1)`, a bottom band can meet the deep tower
only across conductors one and two, and this adjacent cell is already
charged to the conductor-two `O_B` root slot in `(DSP4)`. Hence

```text
C <= min(b_+,b_-)+(x_B+y_B)/3+(2/3)min(x_A,y_A).        (DSP6)
```

Now `x_A+x_B<=d-b_+` and `y_A+y_B<=d-b_-`. Repeating the
two-case estimate `(DSP5)` bounds `(DSP6)` by
`2d/3+min(b_+,b_-)/3`, proving `(DCS4)`.
