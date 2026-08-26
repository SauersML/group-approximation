---
rg: 2
id: one-root-mixed-braid-return-proof
kind: route
title: Track the two complementary entries under one elementary conjugation
target: one-elementary-root-cannot-return-mixed-braid-chart
requires:
  - mixed-braid-gauge-cancellation-misses-signed-hecke-targets
---

Equation `(ORB2)` follows by multiplying column seven and row nine of the
involutive block `(ORB1)`.  Now write `R=1+C`, where `C=cE_ab` and
`C^2=0`; characteristic two gives `R^(-1)=R`.  Then

```text
RNR=N+CN+NC+CNC.                                      (1)
```

The term `CN` can change row `a`, while `NC` can change column `b`.
Neither changes an original entry of `N`: changing `(7,9)` through `CN`
would require `a=b=7`, and changing it through `NC` would require
`a=b=9`; the reverse entry is analogous.  These cases are forbidden by
`a!=b`.

The quadratic term `CNC` is nonzero in an original position only in the
two opposite-root cases.  If `(a,b)=(7,9)`, it lies at `(7,9)`, so the
reverse `(9,7)` coefficient remains `q_1`.  If `(a,b)=(9,7)`, it lies at
`(9,7)`, so the forward `(7,9)` coefficient remains `q_0`.  For every
other pair both original coefficients remain unchanged.  This proves
`(ORB3)` without any assumption on `c`.

Since `q_0=s_0t_0` and `q_1=s_1t_1` are nonconstant reduced Leavitt
matrix units, `(1)` cannot be a constant binary matrix.  Hence the
conjugate of the signed generator `n` does not belong to `L_0`, proving
`(ORB4)`.  Equality in `(ORB5)` would equate the finite supports and force
`RP L_0 (RP)^(-1)=L_0`, contradicting `(ORB4)`.
