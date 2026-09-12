---
rg: 2
id: common-source-binary-marginal-proof
kind: route
title: Pull each endpoint projection back to the common source and apply Cauchy--Schwarz
target: common-source-covariance-locks-binary-marginals
requires: []
---

Multiplying `(CSM1)` on the left by `V_c^*` gives

```text
V_c^*D_(c,x)=V_c^*A_(c,x)V_c-QZ_x.                     (1)
```

The constant terms in the two projections agree because `V_c^*V_c=Q`.
Taking traces in `(1)` therefore gives the difference in `(CSM2)`.  By
Cauchy--Schwarz,

```text
|tau(V_c^*D_(c,x))|
 <=||V_c||_2||D_(c,x)||_2
 =sqrt(tau(Q))||D_(c,x)||_2
 <=||D_(c,x)||_2.
```

The factor `1/2` comes from `P(U)=(1+U)/2`.  Apply the triangle inequality
through the common scalar `tau(QP(Z_x))` to obtain `(CSM3)`.

For `(CSM4)`, the commuting rounded target tuple makes `F_c(A_c)` a
projection, so

```text
||F_c(A_c)V_c||_2^2
=tau(V_c^*F_c(A_c)^2V_c)
=tau(V_c^*F_c(A_c)V_c).
```

Approximate Gram and rounding versions follow by the same fixed-length
telescoping estimates.  Summing the two instances of `(CSM3)` and the three
instances of `(CSM4)` proves the final assertion.

