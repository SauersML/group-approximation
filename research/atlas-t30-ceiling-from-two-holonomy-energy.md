---
rg: 2
id: atlas-t30-ceiling-from-two-holonomy-energy
kind: route
title: Use spherical curvature on the core-reflection conjugacy
target: atlas-a4-t30-energy-ceiling-below-q14-wall
requires:
  - atlas-t30-is-one-parabolic-c3-bridge
  - atlas-a4-two-holonomy-reflection-energy-ceiling
  - unitary-products-obey-the-spherical-chord-bound
---

Apply the cocycle identity to

```text
t30=c^-1 a c.
```

The resulting three unitary factors have chord lengths

```text
delta_n(c), delta_n(a), delta_n(c).
```

For `f(s)=asin(sqrt(s)/2)`, concavity on `[0,2]` and weighted Jensen with
weights `(2,1)` give

```text
2f(delta_n(c)^2)+f(delta_n(a)^2)
 <=3f(E_2HOL(U_n)/3)
 <=3 asin(1/6)+o(1).                                  (1)
```

The spherical chord theorem and the involutivity of `t30` imply

```text
limsup_n x30(U_n)^2
 <=2 sin^2(3 asin(1/6)).                               (2)
```

If `theta=asin(1/6)`, the triple-angle identity gives

```text
sin(3theta)=3/6-4/6^3=13/27.
```

Therefore the right side of `(2)` is

```text
2(13/27)^2=338/729<1/2,
```

which proves `(T30-CEIL)` with the explicit margin `53/1458`.
