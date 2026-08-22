---
rg: 2
id: pair-sum-face-congestion-proof
kind: route
title: Assign every logical coordinate pair to one bounded face with bounded congestion
target: pair-sum-faces-control-shared-commutator-energy
requires:
  - quadratic-redundant-check-overlay-gives-uniform-face-gap
---

For every coordinate `i`, fix one original row `a(i)` containing it.  This
is possible because every column has positive degree.  Given `i,j`, write
`a=a(i)` and `b=a(j)`.  If both coordinates occur in `a` or both occur in
`b`, assign `(i,j)` to that original face.  Otherwise `i` occurs in `a` but
not `b`, and `j` occurs in `b` but not `a` (after exchanging the ordered
pair if necessary), so both occur in the symmetric-difference face `a+b`.

This assignment has congestion bounded solely in terms of row width `q`.
An original face receives at most a constant times `q^2` ordered pairs.  A
pair-sum face indexed by `(a,b)` receives at most `2q^2` ordered pairs,
because its endpoints must be chosen from the two bounded row supports.

For the assigned face `f=f(i,j)`, abbreviate
`A_i=A_(f,i), A_j=A_(f,j)`.  Since `[A_i,A_j]=0` and all four operators are
contractions,

```text
||Q_iQ_j-Q_jQ_i||_2
 <=2(||Q_i-A_i||_2+||Q_j-A_j||_2),
```

and hence

```text
||[Q_i,Q_j]||_2^2
 <=8(||Q_i-A_i||_2^2+||Q_j-A_j||_2^2).                   (PSP1)
```

Sum `(PSP1)` over logical ordered pairs and use bounded congestion.  The
number of indexed pair-sum faces is `Theta(M^2)=Theta(L^2)`, every face has
width at most `2q`, and `M/L` is bounded above and below.  Therefore
`I=Theta(L^2)`, with constants depending only on the stated LDPC parameters.
Dividing the congestion estimate by `L^2` proves `(PSC2)`.
