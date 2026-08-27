---
rg: 2
id: steinberg-y-zero-family-propagation-proof
kind: route
title: Evaluate Y on the q-minus-two translate of the matching point slice
target: steinberg-y-propagates-matching-to-zero-families
requires:
  - steinberg-x-row-splits-zero-marginal-tree-sectors
  - steinberg-fox-marginal-pushes-are-explicit
---

Write

```text
Delta_q f(x)=f(x)-f(tau_q x),
Delta_r f(x)=f(x)-f(tau_r x).
```

On zero marginals every tree coefficient is zero, and the `Y` equation is

```text
Delta_q f(x)-Delta_q f(tau_u x)
                 +Delta_r f(tau_(h^(-1))x)=0.          (SYZ5)
```

Put `x=(-1/2,b,c)`.  The first identity in `(SXTS2)` makes its first term
zero.  If `b!=1`, both point and plane denominators of `tau_u` equal `1-b`
and

```text
tau_u x=(-1/2,b/(1-b),c/(1-b)),
```

so the second term also vanishes by the same identity.  If `b=1`, both `u`
evaluations are tree coefficients and are zero.  Therefore

```text
Delta_r f(-1/4,b/4,c/2)=0.                             (SYZ6)
```

Rename `B=b/4`, `t=c/2`.  For `t!=-1`, `(SYZ6)` is `(SYZ4)`.  At `t=-1`,
the `r`-image is a tree edge, so `(SYZ6)` is exactly `(SYZ1)`.

At `B=0`, `(SYZ4)` is invariance under `phi(t)=t/(1+t)`.  Every nonzero
`t` reaches `-1` under forward iteration: `phi^n(t)=t/(1+nt)` and one may
take `n=-t^(-1)-1`.  Hence `(SYZ1)` kills every nonzero value on that
fiber.  The equation `P(-1/4,0)=0` kills the remaining value at `t=0`,
proving `(SYZ2)`.

Finally sum `(SYZ4)` over `t!=-1`.  The left sum is
`P(-1/4,B)=0` by `(SYZ1)`, while `phi` bijects `F_p\{-1}` onto
`F_p\{1}`.  Thus

```text
sum_(y!=1) f(B-1/4,B,y)=0.
```

Comparing with `P(B-1/4,B)=0` forces `f(B-1/4,B,1)=0`.  Setting
`a=B-1/4` proves `(SYZ3)`.
