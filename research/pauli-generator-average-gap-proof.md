---
rg: 2
id: pauli-generator-average-gap-proof
kind: route
title: Diagonalize the coordinate conjugations in the Pauli basis
target: pauli-generator-average-has-inverse-linear-gap
requires: []
---

Expand

```text
Y=sum_(a in F_2^(2n)) W_a tensor Y_a
```

in the orthonormal Pauli basis of `M_(2^n)`.  The conditional expectation
keeps exactly the coefficient `a=0`.  For `a!=0`, the Pauli word `W_a`
anticommutes with at least one of the `2n` coordinate generators.  If `k(a)`
is the number of such generators, then `k(a)>=1`, and the contribution of
that coefficient to

```text
(1/(2n))sum_i(||[Y,P_i]||_2^2+||[Y,Q_i]||_2^2)
```

is exactly `(2k(a)/n)||Y_a||_2^2`.  Orthogonality and `k(a)>=1` give
`(PAG1)` after summing over `a!=0`.

For `(PAG2)`, write `y=E(y)+(y-E(y))`.  Since `x=x_0 tensor I`,

```text
tr(xE(y))=tr(x)tr(y).
```

Cauchy--Schwarz, `||x||_2<=1`, and `(PAG1)` give the estimate.  Replacing
an approximately placed `x` by its spin-factor projection changes the two
trace terms by at most `2 eta`.

