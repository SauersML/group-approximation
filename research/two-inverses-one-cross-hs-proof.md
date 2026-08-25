---
rg: 2
id: two-inverses-one-cross-hs-proof
kind: route
title: Compare the two almost-surjective contractions through the crossed product
target: two-inverses-one-cross-have-quadratic-hs-floor
requires: []
---

Write `r=sqrt(q)`.  If `epsilon_0>=r` or `epsilon_1>=r`, then `(TIC3)` is
immediate.  Otherwise, contraction of the Hilbert--Schmidt norm gives

```text
||t_0||_2 >=||t_0s_0||_2>=r-epsilon_0,
||s_1||_2 >=||t_1s_1||_2>=r-epsilon_1.                (TIP1)
```

Since all four operators are contractions in `PMP`, both
`P-t_0^*t_0` and `P-s_1^*s_1` are positive.  Squaring `(TIP1)` yields

```text
tau(P-t_0^*t_0)<=2r epsilon_0,
tau(P-s_1^*s_1)<=2r epsilon_1.                         (TIP2)
```

Now

```text
eta^2
 =tau(s_1^*t_0^*t_0s_1)
 =tau(s_1^*s_1)-tau(s_1^*(P-t_0^*t_0)s_1).            (TIP3)
```

For a positive `D` and a contraction `s_1`,
`tau(s_1^*Ds_1)=tau(D^(1/2)s_1s_1^*D^(1/2))<=tau(D)`.
Applying this to `(TIP3)` and then `(TIP2)` gives

```text
eta^2>=q-2r(epsilon_0+epsilon_1),                      (TIP4)
```

which is `(TIC2)`.  Solving the quadratic
`r^2-2Er-eta^2<=0` gives the first inequality in `(TIC3)`; the second follows
from `sqrt(E^2+eta^2)<=E+eta`.  Squaring proves `(TIC4)--(TIC5)`.

For the exact minimality statement, a finite-dimensional unital algebra is
Dedekind finite: `ab=1` implies `ba=1`.  Hence `t_0s_0=1` makes `t_0`
invertible with inverse `s_0`; multiplying `t_0s_1=0` by that inverse gives
`s_1=0`, contrary to `t_1s_1=1`.  The three deleted-row scalar assignments
listed in the claim prove support minimality.
