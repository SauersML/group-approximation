---
rg: 2
id: finite-packet-covariance-polar-correction-proof
kind: route
title: Average the intertwiner over the finite group and take its polar unitary
target: finite-packet-covariance-polar-correction
requires: []
artifacts:
  - notes/FINITE_PACKET_SELF_COPY_COLLAPSE.md
---

Set

```text
T = |F|^(-1) sum_f psi(f) phi(f)*.
```

Changing variables in the finite sum gives `T phi(g)=psi(g) T`.  Also
`||T-1||<=epsilon`, so `T` is invertible.  Its polar unitary
`z=T(T*T)^(-1/2)` still intertwines because `T*T` commutes with `phi(F)`.
The spectrum of `|T|` lies in `[1-epsilon,1+epsilon]`, hence
`|| |T|^(-1)-1 ||<=epsilon/(1-epsilon)` and
`||z-1||<=2epsilon/(1-epsilon)`.
