---
rg: 2
id: reciprocal-basis-builds-invertible-direction-compiler
kind: route
title: Reciprocal vectors of an affine finite-field linearly independent cube give the compiler
target: invertible-direction-schur-rank-compiler
requires: []
---

Put `q=2^k`, take `K=F_q`, and let `L/K` be an extension of degree `q`.
Choose `alpha in L` of degree `q` over `K` and an `F_2`-linear isomorphism

```text
s:F_2^k -> K.
```

For `x in F_2^k` set

```text
a_x=alpha+s(x).                                           (IDP1)
```

The `q` elements `a_x^(-1)` are linearly independent over `F_2`.  Indeed,
suppose

```text
sum_(c in K) epsilon_c/(alpha+c)=0,       epsilon_c in F_2.
```

With `Q(T)=product_(c in K)(T+c)=T^q-T`, multiplication by `Q(alpha)` gives
`P(alpha)=0`, where

```text
P(T)=sum_(c in K) epsilon_c Q(T)/(T+c),       deg P<q.     (IDP2)
```

The minimal polynomial of `alpha` over `K` has degree `q`, so `P=0`.
Evaluating at `c_0 in K` gives

```text
0=P(c_0)=epsilon_(c_0) Q'(c_0)=epsilon_(c_0),            (IDP3)
```

because `Q'(T)=1` in characteristic two.  Hence every coefficient vanishes.

Regard `L` as an `N=kq` dimensional `F_2` vector space.  Let `U_k(x)` be the
matrix of multiplication by `a_x`.  It is affine in `x`; its coefficient in
any nonzero direction `v` is multiplication by the nonzero field element
`s(v)`.
This proves `(IDS1)--(IDS2)`.

Given `f`, linear independence permits an `F_2`-linear functional
`ell_f:L->F_2` with

```text
ell_f(a_x^(-1))=f(x)                                     (IDP4)
```

for every `x`.  Let `v` be the coordinate column of `1 in L` and `u_f` the
row of `ell_f`.  Then

```text
u_f U_k(x)^(-1) v=f(x).                                  (IDP5)
```

The Schur-complement rank formula applied to `(IDS3)` gives
`rank M_f(x)=N+f(x)`.

Finally, the packet assertions follow from
`clifford-commutator-rank-is-packet-dimension`: the leading cross form has
rank `N`, and adjoining the bordered row and column changes that rank by
exactly `f(x)`.  Restriction to the leading packet therefore has multiplicity
`2^f(x)`.
