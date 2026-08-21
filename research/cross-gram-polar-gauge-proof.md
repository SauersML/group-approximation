---
rg: 2
id: cross-gram-polar-gauge-proof
kind: route
title: Extend the polar part of the cross-Gram contraction
target: one-cross-gram-moment-extracts-the-common-polar-gauge
requires: []
---

For intertwiners `T_i in qMp`, put `R=T_2^*T_1` and
`Delta=tau(p)-tau(R^*R)`.  The intertwining equations place `R` in the
finite algebra `N=alpha(G)' cap pMp`.  Extend its polar partial isometry to a
unitary `V in N`.  On singular values, `(1-s)^2<=1-s^2`, hence

```text
||R-V||_2^2<=tau(p-|R|^2)=Delta.
```

Using `R^*V=|R|` and contractivity,

```text
||T_1-T_2V||_2^2
 <=2tau(p)-2tau(|R|)
 <=2[tau(p)-tau(|R|^2)]=2Delta.
```

Also `tau(T_i^*T_i)>=tau(R^*R)`, so no separate self-Gram hypothesis is
needed.  Orthogonal coordinate embeddings into `alpha direct_sum alpha`
have `R=0`, proving the overlap assumption is load-bearing.
