---
rg: 2
id: atlas-a10-next-core-edge-double-coset-proof
kind: route
title: Gauge two regular chart extensions down to one product of subgroup centralizers
target: atlas-first-post-a10-core-edge-is-a-centralizer-double-coset
requires:
  - atlas-forward-collision-a10-absorbs-both-full-charts
  - atlas-a4-rank-three-core
---

Put `N=|A10|=1814400` and fix its left regular permutation action `rho`.
Choose reference extensions

```text
alpha_0 ~= 90 Reg(A8),       alpha_0|_F=rho|_F,
alpha_1 ~= 90 Reg(A8),       alpha_1|_K=rho|_K.       (DC2)
```

Any other labeled regular permutation extension of the first chart with the
same literal `F` restriction is

```text
U_0 alpha_0 U_0^-1,       U_0 in C_(S_N)(F).          (DC3)
```

Indeed an isomorphism between it and the reference regular A8 action is an
`F`-intertwiner, hence commutes with the common labeled `F` action.  The same
argument gives

```text
U_1 alpha_1 U_1^-1,       U_1 in C_(S_N)(K)           (DC4)
```

for the second chart.

Conjugate the entire tuple by `U_0^-1`.  This fixes the reference first chart
and replaces the second by

```text
W alpha_1 W^-1,       W=U_0^-1 U_1
                       in C_(S_N)(F) C_(S_N)(K).       (DC5)
```

The A10 carrier is conjugated at the same time, so its collision and forward
relations remain exact.  Equations `(DC3)--(DC5)` also show the converse:
every `W` in the displayed centralizer product splits as such a pair of
allowed chart gauges.

The canonical fourteen-core dictionary has the already imposed pair

```text
first r^-1 -> second b=s t,
```

and the next distinct pair may be chosen as

```text
first s -> second r^-1.                               (DC6)
```

The exact hexadecimal labels in the artifact are those reconstructed by the
rank-three packet audit.  An involution and an order-three element close the
required A4 context precisely when their product has cube one.  Substituting
`(DC5)` into `(DC6)` is exactly `(DC1)`, proving necessity and sufficiency.
