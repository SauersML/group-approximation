---
rg: 2
id: binary-jacobson-no-infinite-corner-proof
kind: route
title: Kill the symbol by a split injection over the rational function field, then repeat in finite dimensions
target: binary-jacobson-matrix-rings-have-no-infinite-corner
requires:
  - jacobson-shift-representation-is-faithful
artifacts:
  - research/artifacts/fullness-corner-and-order-two-reduction-2026-09-08.md
---

## Proof

Suppose `(NIC1)` held.  Apply the entrywise symbol map of `(JSF2)` to get
matrices over `F_2[z,z^(-1)]`, then view them over the fraction field
`K = F_2(z)`.  Write `bar p` etc. for the images and put

```text
V = bar p K^d,
X : V (+) V --> V,   X(v,w) = bar x_0 v + bar x_1 w,
Y : V --> V (+) V,   Y(u) = (bar y_0 u, bar y_1 u).
```

The elements lie in the corner, so `X` and `Y` do restrict to `V`, and
`(NIC1)` gives `YX = 1` on `V (+) V`.  Hence `X` is injective and

```text
2 dim_K V <= dim_K V,
```

which forces `dim_K V = 0`, so `bar p = 0`.

By `(JSF2)` this means `p in M_d(F_2)`-supported finitary matrices, i.e.
`p in M_d(M_fin(N,F_2))`, a matrix of finite support on `d` rays.  Choose
a finite coordinate set containing that support.  Since every element of
`p M_d(J) p` has all its rows and columns inside that set, the whole
corner is a subring of a finite-dimensional matrix algebra over `F_2`,
with unit `p != 0`.

Run the same argument in that finite-dimensional algebra: `p` acts on a
nonzero finite-dimensional `F_2`-space `W = p F_2^N`, and `(NIC1)` again
gives a split injection `W (+) W -> W`, so `2 dim W <= dim W` and
`W = 0`, contradicting `p != 0`.

Hence no such certificate exists, for any finite `d`.
