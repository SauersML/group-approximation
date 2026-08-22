---
rg: 2
id: positive-density-power-dilation-proof
kind: route
title: Bound the orbit Gram matrix by a geometric off-diagonal series
target: positive-density-power-dilation-forces-finite-depth
requires: []
---

Apply `(PDD1)` to the orbit vectors `U^(jL)QH`.  Their block Gram matrix has
identity diagonal and its distance-`k` off-diagonal blocks have norm at most
`rho^(kL)`.  The elementary inequality
`2|<x,Ay>|<=||A||(||x||^2+||y||^2)` bounds the total off-diagonal form by
`2 rho^L/(1-rho^L)` times the diagonal form.  Choosing `(PDD3)` makes the
Gram matrix strictly positive, so all `N+1` copies of `QH` inject into `H`.
