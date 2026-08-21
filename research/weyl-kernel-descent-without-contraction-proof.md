---
rg: 2
id: weyl-kernel-descent-without-contraction-proof
kind: route
title: Weyl-conjugate the shallow root packet and intersect the Schur supports
target: weyl-kernel-joins-descend-two-levels-without-mass-contraction
requires:
  - depth-shifted-regular-overlap-is-exactly-one-sixteenth
  - fixed-shift-invariance-does-not-force-flat-profile
---

The long entry `e_13(2^(a-2))` lies in `U_0`.  The three positive Weyl
directions give the three positive ordered roots, and the Weyl inversion
relation gives their inverse directions and hence the three negative roots.
Together they supply `(WKD1)`; the rank-three relative elementary generation
theorem identifies their generated subgroup with the depth-`a-2` congruence
layer.

For one direction, the orthogonal projection of a unitary `V` onto the exact
intertwiner space is supported on `S_i`.  Hence

```text
dist_2(V,Hom_i)^2 >= 1-tr(S_i).
```

The Kazhdan estimate bounds the left side by
`(eta/epsilon_0)^2`, proving `(WKD2)`.  Weyl covariance puts the three
supports on one source space.  The codimension of an intersection of finite
dimensional subspaces is at most the sum of their codimensions, even when
their orthogonal projections do not commute, which proves `(WKD3)`.  Repeat
at the descended conductor for fixed `N`.

Finally, an inflated regular representation from level `b_m` has regular
character on every fixed nonidentity integral matrix once `b_m` is large,
so it is canonical as `b_m->infinity`.  If `b_m<=a_m-2N`, it factors through
the claimed descendant with full mass.  This proves that descent itself has
no scalar contraction and completes the scope audit.
