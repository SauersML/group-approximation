---
rg: 2
id: a5-carmichael-triangle-covers-involution-kernels
kind: claim
title: One Carmichael triangle covers all involution anti-invariant directions
distinct_from:
  collective-centralizer-cycles-are-free-gauge-identities: that shows scalar products of endpoint corrections around a cycle freely telescope and retain no error information; this gives the fixed finite-dimensional sum-of-squares gap which survives only when the three edge channels are kept separate.
  bounded-area-high-chromatic-conjugacy-collapse: that uses arbitrarily high chromatic number to collide conjugate matrices; this is a local spectral statement for one five-letter Carmichael triangle.
  gowers-hatami-finite-group-hs-stability: that exactifies approximate finite-group tables; this is an exact representation inequality inside one fixed copy of `A_5`.
---

In `A_5` put

```text
x_i=(i,4,5)                       (i=1,2,3),
s_12=x_1x_2=(1,4)(2,5),
s_23=x_2x_3=(2,4)(3,5),
s_31=x_3x_1=(3,4)(1,5).
```

There is a universal constant `kappa_5>0` such that every unitary
representation `pi` of `A_5` and every vector `xi` satisfy

```text
sum_(ij in {12,23,31}) ||(I+pi(s_ij))xi||^2
  >= 4 kappa_5 ||xi||^2.                                (A5K1)
```

Equivalently, the positive group-algebra element

```text
P=sum_(ij) (1+s_ij)/2
```

is invertible in `C[A_5]`, and `kappa_5` is its least eigenvalue in the
regular representation.

For one edge, put `s=b g^(-1)b g` and `w=s^2`.  Fox differentiation in the
free group on `b,g` gives

```text
partial_g(w)=(1+s)b g^(-1)(b-1).                         (A5K2)
```

Thus one edge is blind on the `(-1)`-eigenspace of its involution `s`.
Inequality `(A5K1)` says this escape cannot persist across all three edges of
a Carmichael triangle.  This does not by itself give bounded presentation
cost: the three edge errors must remain in separate Hilbert channels.
Combined as one scalar cycle product, they erase themselves by
`collective-centralizer-cycles-are-free-gauge-identities`.

Nor does simply storing those three endpoint-correction loops in orthogonal
channels close the presentation problem:
`orthogonal-centralizer-channels-retain-area-properness` shows that every
fixed-channel direct sum retains the twisted-Schreier area lower bound.  The
surviving use of `(A5K1)` must therefore act directly on combined Carmichael
edge errors supplied by a new bounded local chart, rather than on separately
filled centralizer commutators.
