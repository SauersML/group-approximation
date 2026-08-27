---
rg: 2
id: atlas-a8-minimal-four-transvection-cycle-proof
kind: route
title: Hyperplane intersection gives the lower bound and exact BFS certifies the directed four-cycle
target: atlas-a8-minimal-four-transvection-cycle
requires:
  - atlas-a4-19243-parabolic-normal-closure
artifacts:
  - experiments/atlas_a8_minimal_transvection_cycle.py
---

For the lower bound, write any transvection of `F_2^4` as

```text
tau(x)=x+phi(x)v,       phi(v)=0.
```

It fixes `ker(phi)` pointwise.  For three transvections `tau_1,tau_2,tau_3`,

```text
dim(ker(phi_1) intersect ker(phi_2) intersect ker(phi_3))
 >= 4-3=1.
```

Hence their generated subgroup fixes a nonzero vector.  `GL_4(F2)` is
transitive on the fifteen nonzero vectors and therefore has no common nonzero
fixed vector, so three transvections cannot generate it.

For sufficiency, the exact standard-library audit performs breadth-first search
from the identity with

```text
t01,t12,t23,t30.
```

It visits exactly `20160` matrices, so the subgroup is all of `GL_4(F2)=A8`.
The same BFS gives directed diameter `17`.  Exhaustively scanning the resulting
table for `a t23 a^-1=tij` gives shortest conjugator length eight for each of
the three other cycle transvections, and exact matrix multiplication rechecks
all three identities.

Finally `atlas-a4-19243-parabolic-normal-closure` identifies the collision
involution with the nonzero translation `t23` in these chart coordinates.
