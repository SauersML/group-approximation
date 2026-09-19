---
rg: 2
id: iwahori-nielsen-hs-bilipschitz
kind: claim
title: The Iwahori Nielsen involution is uniformly bi-Lipschitz on HS representation coordinates
---

Let `Bbar=<u,e | e^2=1> ~= Z*C_2`, and for two `d`-dimensional unitary
representations `pi,rho` put

```text
d_B(pi,rho)
 = max(d_2(pi(u),rho(u)), d_2(pi(e),rho(e))).
```

For the involution

```text
alpha(u)=u^(-1)e,
alpha(e)=u^(-1)e u
```

from `iwahori-commensurator-nielsen-involution`, pullback satisfies the
dimension-free estimates

```text
d_B(alpha^*pi,alpha^*rho) <= 3 d_B(pi,rho),
d_B(pi,rho) <= 3 d_B(alpha^*pi,alpha^*rho).
```

Thus the two opposite Iwahori extension loci have quantitatively equivalent
normalized-HS geometry after the inner-conjugacy normalization.  In
particular, an edge mismatch which is small in one commensuration direction
is automatically small in the involuted direction, up to the absolute
factor `3`.
