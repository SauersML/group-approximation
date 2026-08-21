---
rg: 2
id: affine-active-elementary-conjugacy-proof
kind: route
title: Write the relative Leavitt equivalence as a Whitehead elementary word
target: affine-active-doubling-is-elementary-matrix-conjugacy
requires:
  - affine-active-head-central-leavitt-envelope
---

The support and inverse relations in `(ACL1)` give `EX=X=XF`, `FY=Y=YE`,
`XY=E`, and `YX=F`. Multiplying the three elementary block matrices in
`(AEC4)` therefore gives `(AEC3)`, and multiplying by the displayed inverse
gives the identity.

For `a in AS`, every `s_i,t_i` commutes with `a`, so the `(i,j)` entry of
`Y a_hat X` is

```text
t_i a s_j=a t_i s_j=delta_(ij)a.
```

This is `(AEC5)`. The standard equivalent-idempotent calculation

```text
[[1-E,X],[-Y,1-F]] [[a_hat,0],[0,0]]
[[1-E,-X],[Y,1-F]]
  =[[0,0],[0,Y a_hat X]]
```

then proves `(AEC6)`.
