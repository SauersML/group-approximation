---
rg: 2
id: three-parahoric-affine-gauge-countermodel-proof
kind: route
title: Let the three correctors be translations of the natural GL_3(F_2)-module
target: three-parahoric-weyl-triangle-has-affine-gauge-countermodel
requires: []
---

In the affine group `L rtimes F`, multiplication and conjugation are

```text
t_lambda t_mu=t_(lambda+mu),
u t_lambda u^(-1)=t_(u lambda),
t_lambda u t_lambda^(-1)=t_(lambda+u lambda) u.         (TPP1)
```

The first equation and
`lambda_0+lambda_2=lambda_1` prove the triangle.  The second proves Weyl
covariance.  If `u` stabilizes `lambda_i`, the translation in the last
equation vanishes, proving exact covariance on `P_i`; otherwise it is the
announced transverse-root tail.

The origin is fixed by the linear `F`-action, so `c_0` commutes with `F`.
Affine translation sends it to `c_lambda`.  In the regular character of the
finite group `H`, each of

```text
1, c_0, c_(lambda_i), c_0 c_(lambda_i)
```

is distinct.  Expanding `(1-c_0)(1-c_(lambda_i))/4` therefore gives trace
`1/4`, while the single projections have trace `1/2`.  All identities are
exact and no approximation or dimension limit is used.
