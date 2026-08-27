---
rg: 2
id: leavitt-d4-l14-fifteen-i4115-carriers-proof
kind: route
title: Compile and split inverse fifteen-winner 4;115
target: leavitt-d4-l14-fifteen-i4115-carriers-are-explicit
requires:
  - leavitt-d4-l14-fifteen-winner-profile-has-five-classes
  - maximal-noncrossing-forest-criterion
---

The actual atom start `5` represents cyclic key `4;115`.  Use

```text
T5=id0, T6 T0 T1 T2 T3=id5^-1, T4=id4.
```

The inverse triangle orientations give

```text
R0=H^-1B0 H E6, R2=H^-1C0 H A1, R4=H^-1B1 H^-1E5,
K=A0^-1H^-1C1^-1H E4^-1H E3^-1H^-1 E2^-1H
  E1^-1H^-1 E7^-1H.
```

The copy retractions reduce to `s,t,u,v,w` and an involution `c`.  The common
carrier becomes

```text
u_3 v_2 w_3 v^-1_2 (w^-1u^-1)_3,
```

whose two exhaustive maximal branches are `I: v=1` and `II: w=1`.  In each
branch the two remaining carriers have lengths `16,14`, the boundary has
length `17`, and the all-maximal state semiring gives sixteen joint coordinate
states.  MSI array `16683118` performs the Q-first cyclic boundary census.
