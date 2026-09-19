---
rg: 2
id: steinberg-y-boundary-mode-proof
kind: route
title: Complete the exceptional r-orbit and expose its scalar survivor
target: steinberg-y-anchor-leaves-one-boundary-mode
requires:
  - steinberg-fox-marginal-pushes-are-explicit
---

Put `eta=1/2` and

```text
D(b,c)=f(-eta,b,c)-f(0,b,c).
```

Evaluating `Y` at `(-eta,b,c)`, for `b!=1`, gives

```text
D(b,c)-D(b/(1-b),c/(1-b))+R(b,c)=0,                   (SYBP1)
```

where, for `c!=-2`,

```text
R(b,c)=f(-1/4,b/4,c/2)-f((b-1)/4,b/4,c/(2+c)),
```

and at `c=-2`,

```text
R(b,-2)=f(-1/4,b/4,-1)+P((b-1)/4,b/4).
```

At `b=0` the two `D` terms cancel.  Hence

```text
f(-1/4,0,t)=f(-1/4,0,t/(1+t))        (t!=-1),
f(-1/4,0,-1)=-P(-1/4,0).                             (SYBP2)
```

Every nonzero `t` reaches `-1`, so these values equal one scalar `kappa`.
Since `p-1=-1` in `F_p`, summing the fiber and using the exceptional
identity gives

```text
P(-1/4,0)=f(-1/4,0,0)-kappa=-kappa,
```

and therefore `f(-1/4,0,0)=0`.  Direct substitution in the pushed formulas
shows that the `c=0` plane equation is `0=0`, and pointwise `Y` is zero on
every `(a,0,0)`.

For `p>=5`, define

```text
G_0(s)=f(-1/6,0,s)-f(1/3,0,s),
G_1(z)=f(-1,0,z)-f(-1,-1/2,z+1/2).
```

Exact evaluation of `X` on `(-1/4,0,t)` gives

```text
kappa 1_(t!=0)=G_0(3t/2)+G_1(t/[2(1-t)])       (t!=1),
kappa=G_0(3/2)-P(-1,0)+P(-1,-1/2)              (t=1). (SYBP3)
```

Both projective parameter maps are bijective on their displayed domains,
so `(SYBP3)` has a free local absorber.  It is a transfer equation, not a
local contradiction.
