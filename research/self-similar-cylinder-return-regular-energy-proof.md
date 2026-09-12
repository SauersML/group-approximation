---
rg: 2
id: self-similar-cylinder-return-regular-energy-proof
kind: route
title: Minimize Haar displacement over projections of fixed trace
target: self-similar-cylinder-return-regular-energy-floor
requires: []
---

Because `w` has infinite order, so does `w^2`, and

```text
tau(u^n)=tau(lambda(w^(2n)))=0                         (SCR3)
```

for every nonzero integer `n`.  Hence `u` is a Haar unitary.  Its spectral
measure for the canonical trace is normalized Lebesgue measure on the unit
circle.

Set

```text
a=(u-1)^*(u-1)=2-u-u^*.
```

For a projection `q` of trace `alpha`, traciality gives

```text
||(u-1)q||_2^2=tau(q a q)=tau(aq).                    (SCR4)
```

Let `A=W^*(u)` and let `E_A` be the trace-preserving conditional expectation
onto `A`.  Under `A=L_infinity(S^1)`, write `f=E_A(q)`.  Then

```text
0<=f<=1,             integral f=alpha,
tau(aq)=(1/(2pi)) integral_(−pi)^pi
                  (2-2cos theta) f(theta) dtheta.      (SCR5)
```

The bathtub principle minimizes `(SCR5)` by taking `f=1` on the centered arc
`|theta|<=pi alpha` and zero off it.  Therefore

```text
tau(aq) >= (1/(2pi)) integral_(−pi alpha)^(pi alpha)
                         (2-2cos theta) dtheta
          =2 alpha-(2/pi)sin(pi alpha).                (SCR6)
```

This proves `(SCR1)`.  Equality is attained by the spectral projection of a
Haar unitary for that centered arc, so the constant is sharp.  Since
`sin x<x` for `0<x<=pi`, it is positive for `alpha>0` (with value `2` at
`alpha=1`).

Now apply any proposed trace-preserving cylinder lift to `(SCR2)`.  Its image
`q` has trace `alpha` and would satisfy `(u-1)q=0`, contradicting `(SCR1)`.
For an asymptotic family `q_n` with `liminf tau(q_n)>=alpha`, pass to any
fixed smaller density `alpha_0<alpha`; monotonicity of the same bathtub
minimum, or directly `(SCR6)`, gives a uniform positive lower bound.  Thus
neither exact nor asymptotic positive-density cylinder localization can be
identified with the canonical regular carrier.

