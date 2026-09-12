---
rg: 2
id: central-letter-separator-averaging-proof
kind: route
title: Separate the matrix range and take a slowly growing Cesaro average under the stable letter
target: central-letter-averages-matrix-range-separators
requires: []
---

Give `direct_sum_(s in S)M_d` its real Hilbert structure

```text
<B,X>=Re sum_s tr_d(B_s^*X_s),       ||B||_2^2=sum_s||B_s||_2^2.   (CSA1)
```

The matrix range is compact and convex.  Metric projection (or ordinary
finite-dimensional Hahn--Banach separation) applied to `(CLS3)` gives a
tuple `A_n` with `||A_n||_2=1` and

```text
<A_n,X_n>-h_n(A_n)>=epsilon,
h_n(A)=sup_(Y in MR_(d_n))<A,Y>.                                  (CSA2)
```

Using the metric-projection separator explicitly, if `Y_n` is the nearest
matrix-range point and `r_n=||X_n-Y_n||_2`, then
`A_n=(X_n-Y_n)/r_n`.  Every coordinate of `X_n` and `Y_n` is a contraction,
so

```text
max_s||A_(n,s)||_op <=2/r_n<=2/epsilon.                            (CSA2a)
```

The matrix range is invariant under simultaneous unitary conjugation,
because `Phi` ucp implies `Ad_V o Phi` ucp.  Hence

```text
h_n(Ad_(T_n)^j A_n)=h_n(A_n).                                     (CSA3)
```

Put `delta_n=||Ad_(T_n)X_n-X_n||_2`.  Choose integers `K_n->infinity`
so slowly that `K_n delta_n->0`, and set

```text
C_n=(1/K_n)sum_(j=0)^(K_n-1) Ad_(T_n)^j A_n.                      (CSA4)
```

Convexity and `(CSA3)` give `h_n(C_n)<=h_n(A_n)`.  On the other hand,
unitarity and telescoping give

```text
|<C_n,X_n>-<A_n,X_n>|
 <=(1/K_n)sum_j ||Ad_(T_n)^(-j)X_n-X_n||_2
 <=K_n delta_n ->0.                                               (CSA5)
```

Thus the gap of `C_n` is at least `epsilon/2` eventually.  Since every
coordinate of both `X_n` and every matrix-range point is a contraction,
that gap is at most `2 sqrt(|S|)||C_n||_2`; consequently
`||C_n||_2>=epsilon/(4sqrt(|S|))`.  Normalize
`B_n=C_n/||C_n||_2`.  Normalization cannot decrease the positive gap, while
the telescoping endpoints in `(CSA4)` yield

```text
||Ad_(T_n)C_n-C_n||_2
 =K_n^(-1)||Ad_(T_n)^(K_n)A_n-A_n||_2 <=2/K_n.                    (CSA6)
```

The lower norm bound for `C_n` turns `(CSA6)` into `(CLS5)`, and `(CLS4)`
follows from `(CSA2)--(CSA5)`.  Cesaro averaging preserves the coordinate
operator bound `(CSA2a)`, while
`||C_n||_2>=epsilon/(4sqrt(|S|))`; after normalization this gives `(CLS6)`.

