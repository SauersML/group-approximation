---
rg: 2
id: same-core-gauge-coercivity-proof
kind: route
title: Divide the two endpoint row values and eliminate the two transported gauge factors
target: same-core-involution-cubic-gauge-coercivity
requires: []
---

Put `A=x_0t` and `alpha=Ad(A)`.  Since `c` commutes with `t`,

```text
alpha(c)=x_0 c x_0^(-1).
```

The two relative increments in `(SCG1)` are exactly

```text
u=c alpha(c),                                          (SCG3)
v=c alpha(c) alpha^2(c).                              (SCG4)
```

Indeed, these follow by expanding `(cx_0)^2x_0^(-2)` and
`(cA)^3A^(-3)` and moving each copy of `c` past the preceding power of
`A`.  In particular,

```text
v=c alpha(u),              c=v alpha(u)^(-1).         (SCG5)
```

Therefore, using that `alpha` is a trace-preserving isometry,

```text
||c-1||_2
 =||v-alpha(u)||_2
 <=||v-1||_2+||u-1||_2.                               (SCG5')
```

Finally, for any unitaries `a,b`,

```text
||ab^(-1)-1||_2=||a-b||_2
 <=||a-1||_2+||b-1||_2.
```

Apply this to the two pairs of endpoint word values to obtain the second
line of `(SCG2)`.  This proves the pairwise theorem without differentiating,
choosing a logarithm, or assuming either endpoint is exact.

For the separate inversion-alignment estimate (labeled `(SCG6)` in the
claim), multiply the commutator on the right by `x_0` and use the
exact baseline inversion:

```text
[c,r]x_0=xr^(-1)-rx.                                  (SCG7)
```

Put `D=xrx-r^(-1)`.  Then

```text
xr^(-1)-rx
 =x(xrx-D)-rx
 =(x^2-1)rx-xD.                                       (SCG8)
```

Unitary invariance and the triangle inequality give `(SCG6)`.
