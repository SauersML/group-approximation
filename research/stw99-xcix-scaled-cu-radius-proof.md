---
rg: 2
id: stw99-xcix-scaled-cu-radius-proof
kind: route
title: Audit the D_(5/2) complete-distance polynomial at the published radius
target: stw99-xcix-scaled-cu-radius
requires: []
---

Perera--Toms--White--Winter, Corollary 4.9 in
[The Cuntz semigroup and stability of close C*-algebras](https://arxiv.org/abs/1210.4533),
gives property `D_k` for `A` with `k=5/2`.  In their Proposition 4.13 set

```text
beta = 1056(600 k gamma + gamma) = 1585056 gamma,
eta  = 10 gamma + 2 beta + 13200 k gamma (1+beta)
     = 3203122 gamma + 52306848000 gamma^2.
```

Write `N=6422957` and take `gamma<1/N`.  The first hypothesis of that
proposition follows from `sqrt(2)<3/2`:

```text
24(30 sqrt(2)+11) gamma < 1344/N < 1/2200,
```

where `1344*2200 = 2956800 < N`.  For its second hypothesis put

```text
s = 2 eta + 5 gamma
  = 6406249 gamma + 104613696000 gamma^2.
```

At `gamma=1/N`, exact integer arithmetic gives

```text
N^2 - 6406249 N - 104613696000 = 2701069556 > 0,
```

so `s<1`.  Proposition 4.13 therefore gives

```text
d_cb(A,B) <= 10 gamma/(1-s).
```

This is strictly below `1/42`, since the stronger exact check is

```text
N^2 - 6406669 N - 104613696000 = 3427616 > 0;
```

the extra `420` is precisely what results from clearing
`10 gamma/(1-s)<1/42`.  Theorem 3.10 of the same paper now gives the scaled-Cu
isomorphism.  This independently verifies the numerical constant printed in
Corollary 4.15 rather than relying on its much coarser intermediate
`10^11 gamma` estimate.
