---
rg: 2
id: toeplitz-head-tail-unital-self-embedding-proof
kind: route
title: Use the Toeplitz defect projection to add the missing head scalar
target: toeplitz-head-tail-unital-self-embedding
requires: []
---

Put `f=1+xy`. In characteristic two and using `yx=1`,

```text
f^2=f,             yf=0,             fx=0.                    (1)
```

Consequently

```text
sigma(a)sigma(b)
 =(xay+eps(a)f)(xby+eps(b)f)
 =x a (yx) b y+eps(a)eps(b)f
 =xaby+eps(ab)f
 =sigma(ab).
```

Additivity is immediate, and `sigma(1)=xy+f=1`. Moreover

```text
y sigma(a) x=a,                                             (2)
```

so `sigma` is injective.

To see properness without appealing to a normal-form theorem, represent `T`
on the vector space with basis `delta_0,delta_1,...`, with `x` the forward
shift and `y` the backward shift. Then `f` is the nonzero projection onto
`F_2 delta_0`, so `xy!=1`. If `xy=sigma(a)`, applying `(2)` would give
`a=y(xy)x=1`, whereas `sigma(1)=1!=xy`. Hence `xy` is not in the image.

Finally `eps(f)=0`, so `sigma(f)=xfy=e_1`; injectivity makes `e_1` nonzero,
and

```text
(xy)e_1=xyxfy=xfy=e_1.
```

In the displayed shift model, `xay` is `a` shifted past the first coordinate
and the correction `eps(a)f` supplies its scalar head. This is the asserted
head-tail interpretation.

