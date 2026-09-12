---
rg: 2
id: matrix-corona-fixed-depth-leavitt-escape-proof
kind: route
title: Use a square-exponential ambient rank and a linear-exponential sparse rank
target: matrix-corona-rank-germs-absorb-fixed-depth-leavitt-escape
requires:
  - matrix-corona-projection-monoid-is-rank-germs
---

Take `d_n=2^(2n)` and let `p_n in M_(d_n)(C)` be a diagonal projection of
rank `r_n=2^n`.  Its constant-tail class `p=[p_n]` is nonzero because no
`p_n` is zero, and its rank germ is

```text
a=[2^n].
```

For fixed `M`, the inequality `M 2^n<=2^(2n)` holds once `n` is large
enough.  Rank-germ comparison therefore gives `M a<=[1]`.

For fixed `N`, define a projection sequence `q_(N,n)` of rank zero for
`n<N` and rank `2^(n-N)` for `n>=N`.  It represents a nonzero projection
class `b_N`, and eventual coordinate equality gives

```text
a=2^N b_N.
```

Every statement is an eventual rank calculation, so rank-germ
classification supplies the asserted Murray--von Neumann inequalities and
equalities in `V(Q_d)`.

