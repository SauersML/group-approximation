---
rg: 2
id: steinberg-p-three-zero-marginal-proof
kind: route
title: Collapse the three a-fibers using the propagated zeros and one plane marginal
target: steinberg-zero-marginal-recurrence-is-zero-at-p-three
requires:
  - steinberg-y-propagates-matching-to-zero-families
---

Work in `F_3`, where

```text
1/2=2,              -1/2=1,              -1/4=2.      (SP3Z1)
```

The matching zeros `(SXTS3)` kill `f(2,b,1)` for every `b`, while `(SYZ1)`
kills `f(2,b,2)`.  The full point fiber `(SYZ2)` kills `f(2,0,c)` for every
`c`.  Finally the second source identity `(SXTS2)`, specialized to `a=2`,
is

```text
f(2,b,1)=f(2,b+1,0).                                  (SP3Z2)
```

As `b` varies, `(SP3Z2)` kills the remaining `c=0` values.  Hence

```text
f(2,b,c)=0                                             (SP3Z3)
```

for all `b,c`.

The first source identity identifies the other two point-coordinate fibers:

```text
f(1,b,c)=f(0,b,c).                                    (SP3Z4)
```

Fix `c` and write `g_c(b)=f(0,b,c)`.  For each `d`, the zero plane marginal
is

```text
0=H(c,d)=sum_(a in F_3) f(a,ac-d,c)
          =g_c(-d)+g_c(c-d),                          (SP3Z5)
```

where `(SP3Z3)--(SP3Z4)` were used.  If `c=0`, `(SP3Z5)` is
`2g_0(-d)=0`, hence `g_0=0`.  If `c!=0`, it says

```text
g_c(b+c)=-g_c(b).
```

Iterating three times returns to `b` with the opposite sign.  Thus
`2g_c(b)=0`; since `2` is nonzero in `F_3`, again `g_c=0`.  Equations
`(SP3Z3)--(SP3Z4)` now give `f=0`.
