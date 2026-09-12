---
rg: 2
id: mixed-completeness-braid-gauge-proof
kind: route
title: Multiply the mixed three-coordinate nilpotents and exhibit the independent spectator
target: mixed-completeness-braid-retains-s3-square-gauge
requires:
  - stabilized-cross-braid-has-s3-square-gauge-fence
  - aggregate-cross-commutator-sum-has-finite-s6-gauge
  - cross-whitehead-sandwiches-branch-roots-into-signed-normalizer
---

The same-row arms in `X` and same-column arms in `Y` give `X^2=Y^2=0`.
The two forward paths are

```text
(7,8)(8,7)       and       (7,9)(9,7),                 (MCBP1)
```

with coefficients `pr=q_0` and `q_1`.  This gives the forward row in
`(MCB3)`.  The reverse paths give `rp=q_1` on `(8,8)`, `r` on `(8,9)`,
`q_1p=0` on `(9,8)`, and `q_1` on `(9,9)`.  Hence the stated formula for
`YX` is exact.

Because `XY=E_77`, left multiplication by `XY` fixes `X`, while right
multiplication by `XY` fixes `Y`.  Expanding in characteristic two gives

```text
ABA=1+Y+XY+YX+XYX=1+X+Y+XY+YX,
BAB=1+X+XY+YX+YXY=1+X+Y+XY+YX,                       (MCBP2)
```

which proves `(MCB4)`.  The path `(8,7)(7,9)` proves `(MCB5)`; the only
reverse candidate for `[U,V']` has coefficient `q_1p=0`.

Finally, in each copy of `S_3`, adjacent reflections satisfy
`aba=bab=c`.  Equations `(MCB7)--(MCB8)` follow componentwise.  The second
component of `(c,c)` is absent from `(c,1)`, providing the explicit
nontrivial spectator retained by the mixed completeness braid.
