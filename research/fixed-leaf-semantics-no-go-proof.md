---
rg: 2
id: fixed-leaf-semantics-no-go-proof
kind: route
title: Classify common-pivot transposition factorizations by support and orientation
target: fixed-leaf-semantics-forbid-mixed-r2-splice
requires: []
---

Multiplying the two equalities in `(FLS0)` by `y_1` and `y_1^*` gives
`x_0=x_1`.  For the canonical leaf words these are `(i p)` and `(j p)`, so
they are distinct elements of `V`; hence their mixed boundary has no van
Kampen filling over any presentation of `V`.

Write `A` for the two-point support of `x`.  Conjugation by `r=(p q)`
sends `x` to the transposition supported on `rA`.  A product of two distinct
transpositions is a three-cycle precisely when their supports meet in one
point, and its support is their union.  Equation `(FLS2)` therefore gives

```text
A union rA={j,p,q}.
```

The only two-point subsets of this set which are moved by `r` are
`{j,p}` and `{j,q}`.  They give `s_jt_j` and `t_js_j`, respectively.  Since
these are inverse nontrivial three-cycles, the displayed orientation in
`(FLS1)` forces `A={j,p}`, hence `(FLS3)`.

Finally `t_j=(j q)` is disjoint from `s_i=(i p)`, so
`t_j^(-1)s_it_j=s_i`.  Since `s_i` and `r` have different supports,
`(FLS4)` follows.
