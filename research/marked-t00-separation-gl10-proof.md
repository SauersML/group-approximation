---
rg: 2
id: marked-t00-separation-gl10-proof
kind: route
title: Store the paid t00 discrepancy in two transverse finite root vertices
target: marked-t00-separation-has-gl10-model
requires:
  - native-t00-y1-collision-pays-marked-opnorm
  - row2-parallel-a2-return-diamond-has-gl8-model
  - outer-root-leavitt-table
---

The global distinction and operator-norm floor are supplied by
`native-t00-y1-collision-pays-marked-opnorm`; they are not reproved here.
The extra exact coefficient identities used in the finite occurrence table
are

```text
t_0s_0t_00=t_00,
q(1+s_0)t_00s_00=q.                                   (1)
```

The second follows from `qs_0=s_1t_1s_0=0` and
`t_00s_00=1`.  Ordinary nonopposite root commutators turn `(1)` into
`(MTS4)` and `(MTS7)`.

On the ten vertices

```text
(7_0,9,8_0,7_1,10,8_1,6,u,b,c)
```

use `(MTS3)--(MTS8)`.  Every multiplication row is a length-two or
length-three transvection path.  The two summands of `D` commute and are
distinct; the marked saturation sees the new `T` summand and returns the old
marked transvection.  The MSI-only audit checks the exact separation,
marked saturation, both order-seven heads, the adjacent braid, the
marked-center cell and all three native `A_2`/return paths.

