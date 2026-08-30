---
rg: 2
id: stw87-diagonal-expectation-order-zero-obstruction-proof
kind: route
title: Orthogonal rank-one projections acquire the same nonorthogonal diagonal
target: stw87-diagonal-expectation-order-zero-obstruction
requires: []
---

Choose distinct `x,y ∈ X`.  The matrix units `e_ab`, for `a,b ∈ {x,y}`,
have finite propagation and belong to `C*_u(X)`.  Set

```text
p=(e_xx+e_xy+e_yx+e_yy)/2,
q=(e_xx-e_xy-e_yx+e_yy)/2.
```

They are orthogonal rank-one projections.  Sending the two minimal projections
of `ℂ²` to `p,q` defines a *-homomorphism `φ`, hence an order-zero map.  But
`E_X(p)=E_X(q)=(e_xx+e_yy)/2`, whose square is
`(e_xx+e_yy)/4 ≠ 0`.  Thus `E_X∘φ` does not preserve orthogonality and is
not order zero.
