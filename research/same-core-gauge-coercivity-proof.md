---
rg: 2
id: same-core-gauge-coercivity-proof
kind: route
title: Apply the order-three automorphism to the involution defect
target: same-core-involution-cubic-gauge-coercivity
requires: []
---

Put `A=x_0 t` and `alpha=Ad(A)`.  Since `c` commutes with `t` and
`x_0^2=1`,

```text
alpha(c)=x_0 c x_0.
```

Therefore

```text
x^2=c alpha(c).                                        (SCG3)
```

Also `A^3=1`, so `alpha^3=1`, and

```text
(x t)^3=(cA)^3=c alpha(c) alpha^2(c).                  (SCG4)
```

Applying the trace-preserving isometry `alpha` to `(SCG3)` gives

```text
||alpha(c) alpha^2(c)-1||_2=||x^2-1||_2.              (SCG5)
```

By `(SCG4)--(SCG5)`,

```text
||(x t)^3-c||_2
 =||alpha(c) alpha^2(c)-1||_2
 =||x^2-1||_2.
```

The triangle inequality with the first cubic defect proves `(SCG2)`.

For `(SCG6)`, multiply the commutator on the right by `x_0` and use the
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
