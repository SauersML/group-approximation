---
rg: 2
id: same-core-gauge-coercivity-proof
kind: route
title: Apply the order-three automorphism to the involution defect
target: same-core-involution-cubic-gauge-coercivity
requires: []
---

Put `A=x_0 s^2` and `alpha=Ad(A)`.  Since `c` commutes with `s` and
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
(x s^2)^3=(cA)^3=c alpha(c) alpha^2(c).                (SCG4)
```

Applying the trace-preserving isometry `alpha` to `(SCG3)` gives

```text
||alpha(c) alpha^2(c)-1||_2=||x^2-1||_2.              (SCG5)
```

By `(SCG4)--(SCG5)`,

```text
||(x s^2)^3-c||_2
 =||alpha(c) alpha^2(c)-1||_2
 =||x^2-1||_2.
```

The triangle inequality with the first cubic defect proves `(SCG2)`.

