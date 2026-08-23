---
rg: 2
id: finite-dyadic-square-function-proof
kind: route
title: Evaluate the dyadic powers on each 2-power root of unity
target: finite-dyadic-square-function-detects-deep-root-mass
requires: []
---

Diagonalize `P`. Every eigenvalue `lambda` has order `2^k` for some
`0<=k<=N`. If `k<=1`, then `lambda^(2^j)=1` for every `j>=1`, so both sides
of `(DSF2)` vanish on that eigenspace.

If `k>=2`, take `j=k-1`. Then

```text
lambda^(2^j)=-1,
(1/4)|lambda^(2^j)-1|^2=1.                              (DSP1)
```

Hence the scalar value of `S_N(P)` is at least one on every deep
eigenspace. Each of its `N-1` summands is at most one, because
`|z-1|<=2` on the unit circle. This proves `(DSF2)` eigenvalue by
eigenvalue, and taking normalized trace proves `(DSF3)`.

Finally `P^2-I` vanishes on `E_<=1`, while its operator norm is at most two.
Therefore

```text
(P^2-I)^*(P^2-I)<=4D_>1,
```

and normalized trace gives `(DSF4)`.

