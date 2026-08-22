---
rg: 2
id: iwahori-projection-spherical-coefficient-proof
kind: route
title: Center the projection and expand its Hecke compression norm
target: iwahori-projection-overlap-is-a-spherical-coefficient
requires: []
artifacts:
  - research/artifacts/canonical-iwahori-one-overlap-audit-2026-08-21.md
---

Since `P` and `UPU^*` are equal-trace projections,

```text
||[P,U]||_2^2
 =||P-UPU^*||_2^2
 =2t-2tau(PUPU^*).                                          (IOS5)
```

The last trace is real and nonnegative because it equals
`||PUP||_2^2`.  Also `||P-t1||_2^2=t(1-t)`, and expansion gives

```text
<P-t1,U(P-t1)U^*>_2=alpha_g-t^2.                            (IOS6)
```

Equations `(IOS5)--(IOS6)` prove `(IOS3)`.  The function in `(IOS2)` is a
unit-vector coefficient of the conjugation representation, hence positive
definite.  Since `Z` is fixed by `Ad rho(C_+)`, moving a `C_+` element from
either side of `g` onto `Z` proves bi-invariance.  Finally `(IOS4)` follows
from `2t(1-t)<=1/2`.
