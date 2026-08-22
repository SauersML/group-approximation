---
rg: 2
id: leavitt-affine-omega-candidate-is-injective
kind: claim
title: The affine Omega Leavitt candidate satisfies coefficient injectivity
artifacts:
  - research/leavitt-affine-omega-global-injectivity-proof.md
  - research/artifacts/verify-leavitt-affine-omega-corner-nielsen.py
distinct_from:
  leavitt-affine-omega-one-copy-picture-area-at-least-eight: that excludes bounded-area kernel pictures; this proves that no coefficient-kernel picture exists at any area.
  leavitt-revised-degree4-candidate-is-injective: that fences the composite-involution word with slots (r,e,a,c,1,b,d,p); this fences the distinct affine word with slots (r,1,a,c,1,e,q,p).
---

For

```text
W_8=r t^2 a t^(-1)c t^2 e t^(-1)q t p t,
```

the coefficient map

```text
EL_20(L_(F_2)(1,2)) -> <G,t | W_8=1>
```

is injective.  Hence the affine Omega system does not kill
`Omega(c,p)=x_15(s_0^2)` and cannot witness nonhyperlinearity through
Kervaire--Laudenbach.
