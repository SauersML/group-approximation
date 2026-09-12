---
rg: 2
id: full-hecke-quarter-moving-gauge-fence-proof
kind: route
title: Tensor the exact four-sector source with two drifting seven-cycle reservoirs
target: full-hecke-quarter-source-does-not-lock-moving-gauges
requires:
  - b2-b3-pair-full-hecke-four-native-sectors
  - order-seven-moving-cuts-realize-both-affine-profiles
---

We give the finite model explicitly.  Let

```text
H_sign=C^2 tensor C^2,
r=Z tensor 1,          t=1 tensor Z,
B_2=X tensor 1,        B_3=1 tensor X.                (1)
```

Take `Q` to be the identity on this factor.  Equations `(HQF1)` follow
from `XZX=-Z`, and the four joint sign projections are the four coordinate
lines.  After tensoring with any common auxiliary space they retain equal
rank, proving `(HQF2)`.

For a common reservoir use

```text
K=C^(12*7),
```

with basis indexed by `(c,j) in {0,...,11} x Z/7`, and let `U` increment
`j`.  Define diagonal involutions as follows.

* `D_1` is negative at `j=0,1,2,3` for `c=0,...,8`, at
  `j=0,...,5` for `c=9`, and nowhere for `c=10,11`.
* `D_2` is negative at `j=0,1` for `c=0,...,6`, and nowhere for
  `c=7,...,11`.

Thus `D_1` has `42` negative and `42` positive coordinates, whereas `D_2`
has `14` negative and `70` positive coordinates.  This proves `(HQF3)`.
Put

```text
D_(i,k)=U^k D_i U^(-k).                              (2)
```

Every seven-cycle contains an even number of negative entries for either
`D_i`.  The seven conjugates in `(2)` are diagonal and their product on
each cycle is therefore `+1`.  This proves the product identity in
`(HQF4)`.  The negative sets are not invariant under `U`, so the stage
copies are nonconstant.

To realize the moving systems literally, take seven equal stage spaces and
let the row-`i` head carry stage `k` to `k+1` by

```text
M_i tensor D_(i,k),                                   (3)
```

acting trivially on `H_sign`, where `M_i` is any fixed order-seven label
unitary.  Equations `(2)--(3)` make all stage boundaries zero and make the
seventh power the identity.  The plus-plus sign line is invariant under
`(3)`, so tensoring it with the stage source and `K` gives the literal
common quarter carrier `F` without altering either `D_i`.

Finally take label reflections `C_(1/4),C_(1/8)` on an eight-dimensional
label factor.  For an involution with positive fraction `theta`, the
negative fraction of `C_q tensor D` is

```text
Phi_q(theta)=1-q+(2q-1)theta.                         (4)
```

Substitution gives

```text
Phi_(1/4)(1/2)=1/2,          Phi_(1/8)(5/6)=1/4.     (5)
```

Reflections of equal positive and negative ranks are unitarily conjugate,
so `(5)` supplies the two exact source/output affine rows.  If the maps in
`(3)` are also used as the parallel bridges, their source and range Grams
are full and their mixed squares are identities, while the nonconstant
`D_(i,k)` remain.  This proves every assertion of the fence.

The construction tensors two already established interfaces but adds no
mixed occurrence between them.  That is precisely its scope: it proves
that such a mixed ordinary-word row is an indispensable new input.
