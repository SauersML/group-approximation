---
rg: 2
id: unitary-corner-reduction-proof
kind: route
title: Compute the two off-corner leakage blocks of a compressed unitary
target: unitary-corner-compressions-force-reduction
requires: []
---

Put `x=pup`.  Orthogonality of the two matrix corners and traciality give

```text
||(1-p)up||_2^2
 =tau(pu^*(1-p)up)
 =tau(p)-tau(pu^*pup)
 =tau(p)-||x||_2^2,                                      (1)

||pu(1-p)||_2^2
 =tau((1-p)u^*pu(1-p))
 =tau(p)-tau(pupu^*p)
 =tau(p)-||x||_2^2.                                      (2)
```

For `(2)`, cyclically move the outer `1-p` and use
`||pu^*p||_2=||pup||_2`.  Thus the two leakage blocks have equal squared
norm.

If `x` is unitary in `pMp`, then `||x||_2^2=tau(p)`, so both terms vanish.
Hence `(1-p)up=pu(1-p)=0`, which is exactly `up=pu`; this proves `(UCR1)`.

If instead `||x-v||_2<=epsilon` for a corner unitary `v`, the reverse
triangle inequality gives

```text
||x||_2 >= ||v||_2-epsilon=sqrt(tau(p))-epsilon.
```

If `epsilon<sqrt(tau(p))/2`, substitution in `(1)--(2)` yields

```text
tau(p)-||x||_2^2
 <=2 sqrt(tau(p)) epsilon-epsilon^2
 <=2 sqrt(tau(p)) epsilon.                              (3)
```

If `epsilon>=sqrt(tau(p))/2`, the same final bound follows directly from
`tau(p)-||x||_2^2<=tau(p)<=2sqrt(tau(p))epsilon`.  Thus `(3)` holds for
all `epsilon>=0`.

Finally

```text
[u,p]=(1-p)up-pu(1-p)
```

is the orthogonal sum of those two leakage blocks.  Equations `(1)--(3)`
give

```text
||[u,p]||_2^2<=4 sqrt(tau(p)) epsilon,
```

which is `(UCR2)`.  Passing to a tracial ultraproduct turns a vanishing
compression error into exact commutation.
