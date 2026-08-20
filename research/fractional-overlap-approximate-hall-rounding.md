---
rg: 2
id: fractional-overlap-approximate-hall-rounding
kind: claim
title: Small bad overlap mass gives an integral good-edge dimension matching after small loss
---

Let `(P_i)_(i in I)` and `(Q_j)_(j in J)` be orthogonal projection
partitions of `1` in `M_d`, let `U in U(d)`, and set

```text
m_(i,j)=||P_i U Q_j||_2^2.
```

Thus `d m_(i,j)` is a nonnegative real transportation plan with integer
marginals

```text
sum_j d m_(i,j)=rank(P_i),
sum_i d m_(i,j)=rank(Q_j).
```

For a bipartite set of allowed edges `G subset I x J`, suppose

```text
beta=sum_((i,j) notin G) m_(i,j).
```

Then there are nonnegative integers `x_(i,j)`, supported on `G`, such that

```text
sum_(i,j) x_(i,j) >= d-ceil(beta d),
sum_j x_(i,j) <= rank(P_i),
sum_i x_(i,j) <= rank(Q_j).
```

Equivalently, after leaving unmatched at most `ceil(beta d)` scalar dimensions
on each side, the remaining source and target dimensions admit an exact
integer matching along allowed edges.

This is only a **dimension-flow** theorem.  It does not assert that the actual
matrix blocks `P_i U Q_j` contain mutually orthogonal partial isometries of
the prescribed ranks.