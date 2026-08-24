---
rg: 2
id: corona-representations-have-an-ideal-valued-support-length-proof
kind: route
title: Expand group words modulo principal C-star ideals
target: corona-representations-have-an-ideal-valued-support-length
requires:
  - matrix-corona-projection-ideal-and-corner-calculus
---

Put `u=rho(g)` and `v=rho(h)`.  The identities

```text
u^(-1)-1=-u^(-1)(u-1),
vuv^(-1)-1=v(u-1)v^(-1),
uv-1=(u-1)v+(v-1)
```

give inversion invariance, conjugacy invariance, and the product inequality.
The commutator becomes one after quotienting by either `I(u-1)` or
`I(v-1)`.  Hence its difference from one lies in both ideals, proving the
meet inequality in `(IS1)`.

The image of `rho(g)` in `Q_d/J` equals one exactly when `rho(g)-1` lies in
`J`, equivalently when its generated ideal is contained in `J`.  This proves
the kernel formula and normality of `N_J`.  If two support ideals have zero
intersection, the commutator support is zero, so the commutator itself is one.

For finite-order `u`, the active projection `p_g` is a polynomial in `u` that
vanishes at `1`.  Hence `p_g` lies in `I(u-1)`.  Conversely
`u-1=(u-1)p_g`, so `u-1` lies in `I(p_g)`.  This proves `(IS2)`.  The
rank-growth description follows from the projection-ideal calculus.
