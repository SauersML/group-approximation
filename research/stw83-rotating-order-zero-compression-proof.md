---
rg: 2
id: stw83-rotating-order-zero-compression-proof
kind: route
title: Rotate a matrix state around an inscribed polygon and close the unitary lift
target: stw83-rotating-order-zero-compression-escapes-circle-gap
requires:
  - stw83-circle-unitary-order-zero-plus-constants-gap
  - stw83-plateau-buffer-recolouring-hinge
---

Fix `epsilon>0`.  Choose `m>=2` so large that

```text
2 sin(pi/m)<epsilon,
```

and put

```text
lambda_j=exp(2 pi i j/m),  0<=j<m.
```

We first construct a continuous loop of unit vectors whose vector states on
the diagonal unitary with eigenvalues `lambda_j` trace the inscribed regular
polygon.

Write `t=exp(i theta)`.  When

```text
2 pi j/m <= theta <= 2 pi (j+1)/m,
```

put `s=m theta/(2 pi)-j` and define

```text
r(t)=sqrt(1-s) e_j+sqrt(s) e_(j+1),                     (2)
```

where the last interval uses `e_m=e_0`.  Formula (2) agrees at every
endpoint and at `theta=0,2 pi`, so `r:T->C^m` is a continuous unit-vector
loop.  For

```text
u=diag(lambda_0,...,lambda_(m-1))
```

we have

```text
< u r(t),r(t) >
 =(1-s)lambda_j+s lambda_(j+1).                         (3)
```

Both endpoints of the relevant polygon edge are within
`2 sin(pi/m)` of `t`.  Convexity and (3) therefore give

```text
abs(<u r(t),r(t)>-t) <= 2 sin(pi/m)<epsilon             (4)
```

uniformly on the circle.

It remains to realize these vector states as compressions of one
star-homomorphic colour.  The map

```text
q:U(m)->S^(2m-1),  q(W)=W* e_1,
```

is a locally trivial bundle with fibre the stabilizer of `e_1`, which is
isomorphic to `U(m-1)`.  Lift the loop `r` first over the interval
`[0,2 pi]`, obtaining a continuous path `W_0` with
`W_0(theta)*e_1=r(exp(i theta))`.  Its endpoints lie over the same vector.
Consequently

```text
H=W_0(0) W_0(2 pi)*
```

fixes `e_1`.  The stabilizer `U(m-1)` is path connected, so choose a path
`H_theta` inside it from the identity to `H`.  Then

```text
W(theta)=H_theta W_0(theta)
```

has the same image under `q` and satisfies `W(0)=W(2 pi)`.  It therefore
defines a continuous unitary `W in M_m(C(T))` with

```text
W(t)* e_1=r(t).                                         (5)
```

Define

```text
pi(x)(t)=W(t)xW(t)*.
```

This is a unital star homomorphism, hence a cpc order-zero map.  For the
constant projection `e=e_(11)`, equations (4)--(5) give

```text
e pi(u)(t)e=<u r(t),r(t)>e,
```

and hence (1).

Finally, `kappa(x)=e pi(x)e` is ucp because `kappa(1)=e`.  If it were
order zero, then a unital order-zero map would be a star homomorphism.  But
there is no unital star homomorphism from the simple noncommutative algebra
`M_m`, `m>=2`, to the abelian algebra
`eM_m(C(T))e=C(T)e`: a nonzero homomorphism would be injective.  Thus
`kappa` is not order zero.  Equivalently, `e` does not commute with the
range of `pi).  This failure of compression to preserve order zero is
exactly the noncommutative escape from the abelian distance-one theorem.
