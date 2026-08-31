---
rg: 2
id: diluted-subgroup-indicator-proof
kind: route
title: Dilute a two-dimensional subgroup test by trivial spectators
target: subgroup-indicators-are-diluted-hs-coefficients
requires: []
---

Let

```text
s = [[0,1],[1,0]],
u_H(g) = I_2  if g in H, and  s  otherwise,
beta_n(g)=u_H(g) direct_sum I_n,   xi_n=e_1 direct_sum 0.
```

Since `e in H`, `beta_n(e)=I`. The selected coefficient is `1` on
`H` and `0` off `H`, exactly. For any `g,h`, both `u_H(gh)` and
`u_H(g)u_H(h)` lie in `{I_2,s}`. Hence their difference is zero or has
ordinary Hilbert--Schmidt square `||I_2-s||_HS^2=4`, and therefore

```text
sup_(g,h) ||beta_n(gh)-beta_n(g)beta_n(h)||_(2,n+2)
    <= 2/sqrt(n+2) -> 0.
```

Also `g in H` iff `g^(-1) in H`, so
`beta_n(g^(-1))=beta_n(g)^*` exactly. This proves the claim. QED
