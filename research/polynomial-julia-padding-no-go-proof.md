---
rg: 2
id: polynomial-julia-padding-no-go-proof
kind: route
title: A sum of polynomial squares cannot equal a decreasing affine function
target: polynomial-julia-padding-cannot-flatten-spectrum
requires: []
---

Restrict `(FPJ2)` to the scalar algebra and let `K=t`.  This gives
`(FPJ1)`.  Write each complex polynomial in real and imaginary parts.  Then

```text
sum_j |f_j(t)|^2
```

is a sum of squares of real polynomials.  If any summand is nonconstant,
the sum has positive leading coefficient and even degree at least two.  If
every summand is constant, the sum is constant.  Neither possibility equals
the degree-one polynomial `lambda-t` on an interval.  Polynomial identity
then proves the contradiction.
