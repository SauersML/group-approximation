---
rg: 2
id: stw87-diagonal-expectation-order-zero-obstruction-proof
kind: route
title: Coordinatewise orthogonality stays one-half away from the common averaged diagonal
target: stw87-diagonal-expectation-order-zero-obstruction
requires: []
---

Choose distinct `x,y ∈ X`.  The matrix units `e_ab`, for `a,b ∈ {x,y}`,
have finite propagation and belong to `C*_u(X)`.  Set

```text
p=(e_xx+e_xy+e_yx+e_yy)/2,
q=(e_xx-e_xy-e_yx+e_yy)/2.
```

They are orthogonal rank-one projections.  Sending the two minimal
projections `e_1,e_2` of `C^2` to `p,q` defines a *-homomorphism `phi`, hence
an order-zero map.  Put

```text
h=E_X(p)=E_X(q)=(e_xx+e_yy)/2.
```

Let `theta:C^2->ell^infinity(X)` be any c.p.c. order-zero map and set
`a=theta(e_1)`, `b=theta(e_2)`.  Then `a,b` are positive contractions and
`ab=0`.  Evaluating at the coordinate `x` gives `a(x)b(x)=0`; hence at least
one of the two nonnegative scalars `a(x),b(x)` is zero.  Since `h(x)=1/2`,

```text
max(norm(a-h),norm(b-h)) >= 1/2.                         (1)
```

The zero map is c.p.c. and order zero, and both distances from its two
images to `h` equal `norm(h)=1/2`.  Therefore the lower bound in (1) is
attained, proving the exact formula `(D)`.
