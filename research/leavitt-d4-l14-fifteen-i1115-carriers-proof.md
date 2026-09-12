---
rg: 2
id: leavitt-d4-l14-fifteen-i1115-carriers-proof
kind: route
title: Compile and split inverse fifteen-winner 1;115
target: leavitt-d4-l14-fifteen-i1115-carriers-are-explicit
requires:
  - leavitt-d4-l14-fifteen-winner-profile-has-five-classes
  - maximal-noncrossing-forest-criterion
---

The actual atom start `2` represents cyclic key `1;115`.  The assignment is

```text
T2=id0, T3 T4 T5 T6 T0=id5^-1, T1=id4.
```

The inverse orientations give

```text
R0=H^-1B0 H E3, R2=H^-1C0 H A1, R4=H^-1B1 H^-1E2,
K=A0^-1H^-1C1^-1H E1^-1H^-1 E7^-1H E6^-1H^-1
  E5^-1H E4^-1H.
```

After the copy retractions the common carrier is

```text
u_3 s_2 (cst)_3 s^-1_2 (t^-1s^-1c u^-1)_3,
```

where `c^2=1`.  Its two exhaustive maximal branches are

```text
I:  s=1;
II: t=s^-1c.
```

Branch I has carrier lengths `14,14`, boundary length `29`, and fifteen joint
states.  Branch II has lengths `16,14,38` and eleven states.  MSI array
`16683427` performs the exact Q-first cyclic boundary census.
