---
rg: 2
id: atlas-t30-ceiling-from-parabolic-c3-energy
kind: route
title: Telescope the shortest P-C3-P word to the q14 transverse threshold
target: atlas-a4-t30-energy-ceiling-below-q14-wall
requires:
  - atlas-t30-is-one-parabolic-c3-bridge
  - atlas-a4-parabolic-c3-bridge-energy-ceiling
  - unitary-products-obey-the-spherical-chord-bound
---

Telescope the covariance cocycle along the exact word

```text
t30=k^-1 h^-1 z b h k.
```

The six unitary cocycle factors have chord lengths

```text
delta_n(k),delta_n(h),delta_n(z),
delta_n(b),delta_n(h),delta_n(k).
```

Put `f(s)=asin(sqrt(s)/2)`.  Direct differentiation gives

```text
f''(s)=-(2-s)/(2(s(4-s))^(3/2)),
```

so `f` is concave on `[0,2]`.  Under `E_PC3(U_n)<=1/6+o(1)`, every squared
coordinate defect lies in `[0,1/6+o(1)]`.  Weighted Jensen, with occurrence
weights `(2,2,1,1)` of total weight six, gives

```text
sum_occurrences asin(delta_n(g)/2)
 <=6 asin(sqrt(E_PC3(U_n)/6)/2)
 <=6 asin(1/12)+o(1).                                 (1)
```

Apply `(SPH-CHORD-2)` to the six cocycle factors.  Since `t30` is an
involution,

```text
limsup_n x30(U_n)^2
 =limsup_n delta_n(t30)^2/2
 <=2 sin^2(6 asin(1/12)).                              (2)
```

Strict concavity of `sin` on `[0,pi/2]` gives
`sin(pi/36)>1/12` by comparing its graph with the chord from `0` to
`pi/6`.  Therefore `6 asin(1/12)<pi/6`, and `(2)` is strictly below
`2 sin^2(pi/6)=1/2`.  This is exactly `(T30-CEIL)`.
