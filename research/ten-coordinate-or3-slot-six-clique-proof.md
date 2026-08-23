---
rg: 2
id: ten-coordinate-or3-slot-six-clique-proof
kind: route
title: The three private planes are orthogonal and six rank-one-fifth kernels do not fit
target: ten-coordinate-or3-slot-frames-have-a-six-clique-obstruction
requires:
  - edgeful-or3-balanced-private-plane-packet
---

Order the ten coordinate copies as

```text
100_1,100_2,010_1,010_2,001_1,001_2,110,101,011,111.
```

The three planes in `(OBP3)` may then be chosen as

```text
E_a={001_1,101},
E_b={100_1,110},
E_c={010_1,011}.                                        (TSOP1)
```

They use six distinct coordinate copies.  On `E_j`, the two endpoint
assignments differ in coordinate `j`, so the Hadamard conjugate of the
logical diagonal sign is off-diagonal and its root-diagonal coefficient is
zero.  Outside `E_j` the conjugate remains diagonal with coefficient
`+1` or `-1`.  Therefore the root-diagonal part `R_j` has entries zero
exactly on `E_j` and signs elsewhere.  It follows that

```text
1-R_j^2 = projection onto span(E_j).                     (TSOP2)
```

This projection has rank two, and the three projections are orthogonal by
`(TSOP1)`.  Simultaneous conjugation of the clause packet preserves ranks
and products.  Common amplification multiplies all four ranks by the same
factor, so each normalized trace remains `2/10=1/5`.

Literal root-skeleton alignment identifies the same root-diagonal element
at every occurrence of one global variable.  Polynomial identity `(TSOP2)`
therefore identifies its kernel projection as well.  If two variables occur
in one clause, their two slot kernels are conjugates of two different
members of `(TSOP1)`, so their product is zero.  In the formula containing
all twenty triples on six variables, every pair co-occurs.  Six pairwise
orthogonal rank-two projections would have total rank twelve in a
ten-dimensional space, proving the exact contradiction.

For the robust estimate, let `S=sum_i P_i`.  Positivity and normalized-trace
Cauchy--Schwarz give

```text
tr(S^2) >= tr(S)^2=(6/5)^2.                              (TSOP3)
```

On the other hand, traciality gives

```text
tr(S^2)
 =sum_i tr(P_i)+2 sum_(i<j) tr(P_i P_j)
 =6/5+2 sum_(i<j) ||P_i P_j||_2^2.                      (TSOP4)
```

Subtracting `(TSOP4)` from `(TSOP3)` yields

```text
sum_(i<j) ||P_iP_j||_2^2
 >= ((6/5)^2-6/5)/2=3/25.
```

There are fifteen pairs, so one squared overlap is at least `1/125`.

