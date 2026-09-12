---
rg: 2
id: unitary-spherical-chord-proof
kind: route
title: Apply the angular metric to the partial products
target: unitary-products-obey-the-spherical-chord-bound
requires: []
---

Regard `L^2(M,tau)` as a real Hilbert space with inner product

```text
<x,y>_R=Re tau(y^*x).
```

Every unitary has `2`-norm one.  For unit vectors `x,y`, their angular
distance

```text
theta(x,y)=arccos <x,y>_R
```

is the standard spherical metric and satisfies the triangle inequality.
Moreover,

```text
||x-y||_2^2=2-2<x,y>_R,
theta(x,y)=2 asin(||x-y||_2/2).                        (1)
```

Let `P_0=1` and `P_j=A_1...A_j`.  Left multiplication by `P_(j-1)^*`
is an isometry, so

```text
||P_j-P_(j-1)||_2=||A_j-1||_2=d_j.                   (2)
```

The spherical triangle inequality along
`P_0,P_1,...,P_r`, followed by `(1)--(2)`, gives

```text
2 asin(D/2)=theta(P_0,P_r)
 <=sum_j theta(P_(j-1),P_j)
 =2 sum_j asin(d_j/2).
```

Since `asin(D/2)<=pi/2`, this proves `(SPH-CHORD)`.  If the angular sum is at
most `pi/2`, applying the increasing function `2 sin` proves
`(SPH-CHORD-2)`.

