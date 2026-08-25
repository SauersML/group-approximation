---
rg: 2
id: almost-root-central-gauge-coercivity-proof
kind: route
title: Compare the root and endpoint transports of the relative gauge
target: almost-root-central-gauges-have-global-row-coercivity
requires: []
---

Put

```text
alpha=Ad(A),        beta=Ad(x_0),
u=x_1^2x_0^(-2),   v=(x_1t)^3(x_0t)^(-3),
u'=c alpha(c).                                           (ARP1)
```

Direct expansion gives

```text
u=c beta(c),
v=c alpha(c) alpha^2(c)=c alpha(u').                    (ARP2)
```

Moreover

```text
||u'-u||_2
 =||alpha(c)-beta(c)||_2
 =||tct^(-1)-c||_2
 =||[c,t]||_2.                                          (ARP3)
```

The second identity in `(ARP2)` gives the exact elimination

```text
c=v alpha(u')^(-1).                                     (ARP4)
```

Since `alpha` is a normalized-HS isometry, the triangle inequality yields

```text
||c-1||_2
 <=||v-1||_2+||u'-1||_2
 <=||v-1||_2+||u-1||_2+||[c,t]||_2.                    (ARP5)
```

Finally, unitary invariance gives

```text
||u-1||_2=||x_1^2-x_0^2||_2,
||v-1||_2=||(x_1t)^3-(x_0t)^3||_2.                     (ARP6)
```

Substitution proves `(ARC2)`.  If the baseline endpoint is exact, then
`x_0^2=(x_0t)^3=1`, and multiplication by `x_0` also gives
`||x_1-x_0||_2=||c-1||_2`; this proves `(ARC3)`.  Formula `(ARC5)` follows
by computing the matrix entries of `ct-tc` in a `t`-eigenbasis.

