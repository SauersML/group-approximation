---
rg: 2
id: two-c-conjugate-g2-mixed-carriers-collapse-to-one-orientation
kind: claim
title: Two C-conjugate g2 mixed carriers collapse to one raw orientation
artifacts:
  - research/two-c-conjugate-g2-mixed-carrier-collapse-proof.md
distinct_from:
  fixed-g2-mixed-pair-has-all-length-d8-normal-form: that repeats one shifted pair; this introduces a second C-conjugate T-root and an independent hidden sign.
  first-uncancelled-g2-mixed-carrier-has-no-hall-deficit: that computes one hidden sign; this gives the complete two-carrier polar table.
---

Let `k` generate the active quotient `C/<h>`. On its two-dimensional
module choose

```text
r=[[0,1],[1,1]],              v=(1,0)^t,
phi_0=(1,0),                  phi_1=phi_0 r^(-1)=(1,1).
```

Keep `V=x_(c_0,c_3)(S)` and define two inequivalent shifted negative
roots

```text
U_i=I+T E_(c_3,phi_i),       Y_i=VU_i,                 i=0,1.
                                                               (TCC1)
```

Here `U_0=g_2^2Ug_2^(-2)` and `U_1=kU_0k^(-1)`. Put

```text
P_i=[V,U_i]=I+(ST)E_(c_0,phi_i),
Z_i=(P_iA)^2=I+(qT)E_(v,phi_i).                         (TCC2)
```

Then `Z_0,Z_1` are commuting independent involutions. Each single
carrier has the familiar hidden-sign transport

```text
Y_i^(-1)AY_i=AWZ_i,              Y_i^(-1)WY_i=WZ_i.    (TCC3)
```

The four smallest two-carrier words have only two polar types:

| carrier | initial projection after `G_(sigma,tau)` compression |
|---|---|
| `Y_0Y_1` or `Y_0^(-1)Y_1^(-1)` | `G_(sigma,tau)(1+Z_0)(1+Z_1)/4` |
| `Y_0Y_1^(-1)` or `Y_0^(-1)Y_1` | `G_(sigma,tau)(1+Z_0Z_1)/2` |

After the qutrit cut `R=e_0+e_1` the exact ranks are

| carrier type | `(+,+)` | every other `(sigma,tau)` |
|---|---:|---:|
| both hidden signs | `23/1152` | `5/256` |
| product hidden sign | `43/1152` | `7/192` |

All four numbers are strictly below `1/18`. Prepending any target
contraction `Ee_b g_2^j` can only decrease them.

More decisively, every two-carrier product has already lost the positive
raw orientation. If `U_Delta=U_0U_1` and
`P_Delta=P_0P_1`, then

```text
Y_0Y_1=P_0U_Delta,
Y_0Y_1^(-1)=P_Delta U_Delta,                            (TCC4)
```

and the two other orders have the same form up to inversion. Their
coefficients lie in `B_-=F_2<q,T>`. Thus the full two-carrier packet,
including arbitrary `g_2` conditioning, has the established residually
finite one-orientation models.

Hence independent signs `Z_0,Z_1` do not produce a two-carrier escape.
Equal orientations select both hidden signs; opposite orientations
select their product. Any apparent cancellation of the signs is
accompanied by literal cancellation of the two `S` occurrences. The
next threshold must change both raw root positions, or use a linear
interference operator rather than a single product word.
