---
rg: 2
id: three-way-parity-cell-repair-proof
kind: route
title: Invert the even-parity tetrahedron and flip its common parity
target: three-way-parity-hole-has-one-cell-repair
requires: []
---

For an even-cell table `(x_000,x_011,x_101,x_110)`, summing the three
zero-coordinate margins counts `x_000` three times and every other cell
once.  Since the total is `N`, this gives

```text
s_0+a_0+t_0=N+2x_000.
```

The other three identities follow by symmetry and prove `(PCR3)--(PCR4)`.
They also show that cone membership is exactly nonnegativity of the four
numerators.  Differences of any two numerators are even after using the
three total-margin identities in `(PCR2)`, so their parities agree.

An odd vertex `u` has Hamming distance one from three even vertices and
distance three from the fourth.  In the numerator belonging to an even
vertex `v`, adding the margin column `A_u` changes the sum of the three
selected margins by the number of coordinates shared by `u,v`, and changes
`N` by one.  The change is therefore `2-1=1` at distance one and `0-1=-1`
at distance three.  This proves the claimed parity flip and nonnegativity,
and `(PCR4)` supplies the integral table.
