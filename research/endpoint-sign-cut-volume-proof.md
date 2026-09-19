---
rg: 2
id: endpoint-sign-cut-volume-proof
kind: route
title: Apply exact same-core gauge coercivity to a spectral sign
target: endpoint-triangle-charges-bs-sign-cut-volume
requires:
  - same-core-involution-cubic-gauge-coercivity
  - bs-core-coarea-cuts-have-full-legalization-cost
---

Since `P` is spectral for `S`, `D=1-2P` commutes with `T=S^2`.
Apply `(SCG2')` with `x_1=X`, `x_0=X_0`, `c=D`, and `t=T` to obtain
`(ETC2)`.  The elementary inequality `a^2+b^2>=(a+b)^2/2` and

```text
||D-1||_F^2=||-2P||_F^2=4 rank(P)
```

give `(ETC3)`.  If `X^2=1`, the square term in `(ETC2)` vanishes and gives
`(ETC4)` directly.

For `(ETC5)`, conjugating `P_A` by the cyclic shift translates its support.
The difference of the two diagonal sign matrices has entries `+-2` exactly
on the symmetric difference `A triangle (A+1)`.  Squaring and summing gives
the formula.

