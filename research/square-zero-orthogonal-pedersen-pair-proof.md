---
rg: 2
id: square-zero-orthogonal-pedersen-pair-proof
kind: route
title: Read the source and range positives and reverse the norm computation
target: square-zero-cover-is-orthogonal-pedersen-pair
requires: []
---

Given a square-zero `x`, set `p=x*x`, `q=xx*`, and `z=x`.  Then

```text
pq=x* x^2 x*=0.
```

Also `Ideal(x)=Ideal(x*x)`: one inclusion is immediate, while for the other,
the image of `x*x` vanishes in the quotient by `Ideal(x*x)`, and the C-star
identity forces the image of `x` to vanish.  Hence condition 1 implies
condition 2.

Conversely, suppose condition 2 holds.  From `pq=0` we get

```text
(pz)(pz)*=pzz*p=pqp=0,
```

and therefore `pz=0`.  It follows that

```text
(z^2)*z^2=z* z* z z=z*pz=0,
```

so `z^2=0`.  The same quotient argument gives
`Ideal(z)=Ideal(z*z)=Ideal(p)`, and therefore `b in Ideal(z)`.
