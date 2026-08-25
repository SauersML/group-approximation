---
rg: 2
id: balanced-leak-weighted-rayleigh-proof
kind: route
title: Move both lattice factors off the balanced projection and center the overlap
target: balanced-leak-saturates-weighted-rayleigh-tests
requires: []
---

Write `g=lambda_1 h lambda_2` with `lambda_1,lambda_2 in Lambda`.  Since `q`
commutes with `pi(Lambda)`, traciality gives

```text
tau(q pi(g)qpi(g)^*)
 =tau(q pi(lambda_1 h)qpi(lambda_1 h)^*)
 =tau(pi(lambda_1)^*qpi(lambda_1) pi(h)qpi(h)^*)
 =tau(q pi(h)qpi(h)^*)
 =1/4.                                                   (BRP1)
```

Every summand in `H_omega` therefore has the same overlap, and summing
`(BRP1)` against `omega` proves `(BLR2)`.

Put `x=2q-I`.  It is self-adjoint, `x^2=I`, `tau(x)=0`, and hence
`||x||_2=1`.  For every `g` in the double coset, `(BRP1)` and `tau(q)=1/2`
give

```text
<x,pi(g)xpi(g)^*>
 =4 tau(q pi(g)qpi(g)^*)-2tau(q)-2tau(pi(g)qpi(g)^*)+1
 =4(1/4)-1-1+1
 =0.                                                     (BRP2)
```

Linearity proves the first identity in `(BLR3)`.  Since both `x` and every
conjugate of `x` are unit vectors,

```text
||pi(g)xpi(g)^*-x||_2^2
 =2-2 Re <x,pi(g)xpi(g)^*>
 =2.                                                     (BRP3)
```

Averaging proves the second identity.  Finally
`<x,S_(t,omega)x>=t+(1-t)0=t`.  These calculations use no representation
decomposition and no choice of weights beyond positivity and total mass one.

