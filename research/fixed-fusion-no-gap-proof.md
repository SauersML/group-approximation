---
rg: 2
id: fixed-fusion-no-gap-proof
kind: route
title: Concentrate central vectors near the compact identity
target: fixed-tensor-fusion-types-have-no-spectral-gap
requires: []
---

The normalized characters `a_i=chi_(sigma_i)/dim(sigma_i)` have modulus at
most one and equal one at the identity, so multiplication by each `a_i` is
an `L^2` contraction.  Infinite compact groups have nonatomic Haar measure.
Uniform continuity of conjugation over compact `K` therefore gives
conjugation-invariant identity neighborhoods `U` of arbitrarily small measure
on which every `|a_i-1|` is arbitrarily small.

The central unit vector `g_U=1_U/sqrt(mu(U))` has
`||(T_i-1)g_U||_2<=sup_U|a_i-1|`.  If
`E=span{chi_(theta_1),...,chi_(theta_s)}`, then

```text
|<g_U,chi_(theta_j)>|<=dim(theta_j)sqrt(mu(U)),
```

so `||P_Eg_U||` tends to zero.  Normalize `(1-P_E)g_U`; the defects remain
arbitrarily small because `||T_i-1||<=2`.  Finally truncate its central
Peter--Weyl expansion outside `E` and renormalize.  This yields a finitely
supported unit vector exactly orthogonal to `E` with all requested defects
below `epsilon`.
