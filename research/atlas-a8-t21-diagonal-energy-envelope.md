---
rg: 2
id: atlas-a8-t21-diagonal-energy-envelope
kind: claim
title: The exact t21 word admits precisely the reciprocal family of diagonal energy weights
distinct_from:
  atlas-a8-four-cycle-controls-raw-s3-energy: that theorem records the symmetric coefficient 24; this claim identifies the full sharp family of diagonal weights available from the same exact word estimate.
---

Let nonnegative numbers `x_01,x_23,x_30` satisfy the commutator bound coming
from the exact word for `t21`,

```text
a <= 2 x_01 + 2 x_23 + 4 x_30.                        (1)
```

For positive coefficients `c_01,c_23,c_30`, the diagonal quadratic estimate

```text
a^2 <= c_01 x_01^2 + c_23 x_23^2 + c_30 x_30^2       (2)
```

holds for every nonnegative triple obeying `(1)` whenever

```text
4/c_01 + 4/c_23 + 16/c_30 <= 1.                       (3)
```

Moreover `(3)` is necessary for `(2)` to dominate the linear functional in
`(1)` for all triples.  Hence this reciprocal surface is the sharp diagonal
energy envelope of the eight-letter `t21` certificate.

In the atlas application `x_ij=||[U,lambda(tij)]||_2`; therefore any point on
this weight surface may replace the symmetric coefficient `24`.  In
particular `(24,24,24)` is the minimax choice when all three directions must be
charged equally, but it is not privileged when the upstream packet controls
the directions anisotropically.