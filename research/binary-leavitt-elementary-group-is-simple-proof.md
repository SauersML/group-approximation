---
rg: 2
id: binary-leavitt-elementary-group-is-simple-proof
kind: route
title: Collapse the normal-subgroup sandwich to its two extreme levels
target: binary-leavitt-elementary-group-is-simple
requires:
  - leavitt-gl-equals-el-and-perfect-unit-group
  - leavitt-center-is-coefficient-field
---

The binary Leavitt algebra `R` is purely infinite simple.  In particular it
is a simple exchange ring.  The normal-subgroup theorem for general linear
groups over exchange rings says that, for `n>=3`, every subgroup `N` of
`GL_n(R)` normalized by `EL_n(R)` has a uniquely determined two-sided ideal
`I` with

```text
EL_n(R,I) <= N <= C_n(R,I).
```

Here `C_n(R,I)` is the inverse image of the center of `GL_n(R/I)`.

Now let `N` be normal in `EL_n(R)`.  The identity
`EL_n(R)=GL_n(R)` lets us apply the sandwich theorem to `N`.  Simplicity of
`R` leaves only `I=0` and `I=R`.

If `I=R`, then `EL_n(R,I)=EL_n(R)`, so `N=EL_n(R)`.  If `I=0`, then
`N<=C_n(R,0)=Z(GL_n(R))`.  A matrix commuting with all elementary
transvections is a scalar matrix whose scalar belongs to `Z(R)^x`; this is a
direct matrix-entry calculation for `n>=2`.  Since `Z(R)=F_2`, its only
central unit is `1`.  Thus `Z(GL_n(R))={1}` and `N={1}`.

Both levels have therefore collapsed to the trivial and whole subgroups,
which proves simplicity.

