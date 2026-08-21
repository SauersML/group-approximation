---
rg: 2
id: radial-cyclic-abelianization-proof
kind: route
title: Identify the abelianized radial rows with one cyclic polynomial
target: radial-only-group-needs-a-cyclic-gcd-audit
requires: []
---

Index `K^*` by `alpha^i`.  After abelianization, the translate of every
radial relation is `z^i f(z)`.  Hence the relation matrix is multiplication
by `f` on `F_2[z]/(z^m-1)`, and its cokernel has dimension the degree of
`gcd(f,z^m-1)`.  Evaluation at `1` and at every Frobenius conjugate of
`alpha` gives the stated `(n+1)`-dimensional factor.
