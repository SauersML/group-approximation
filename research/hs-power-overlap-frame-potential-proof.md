---
rg: 2
id: hs-power-overlap-frame-potential-proof
kind: route
title: Apply the rank bound to the orbit frame Gram matrix
target: positive-density-hs-power-overlaps-force-finite-depth
requires: []
---

Put `r=rank(Q)` and define

```text
V:(QH)^(direct sum (N+1))->H,
V(h_0,...,h_N)=sum_(j=0)^N U^(jL)h_j.
```

Its positive Gram matrix `G=V^*V` has blocks

```text
G_(ij)=Q U^((j-i)L) Q.
```

Thus

```text
Tr(G)=(N+1)r,                                           (HPF1)
Tr(G^2)
 =(N+1)r
   +2 sum_(k=1)^N (N+1-k)||Q U^(kL)Q||_HS^2.           (HPF2)
```

Since `rank(G)<=d`, Cauchy--Schwarz on its nonzero eigenvalues gives

```text
Tr(G^2)>=(Tr G)^2/d=(N+1)^2r^2/d.                       (HPF3)
```

The hypothesis `(HPO1)` is exactly

```text
||Q U^(kL)Q||_HS^2<=r rho^(2kL).
```

Insert these bounds in `(HPF2)--(HPF3)` and divide by `(N+1)r` to get
the first inequality in `(HPO2)`.  Dropping the factors
`1-k/(N+1)` and extending the geometric sum gives the second.

For fixed `N,L`, an additive `o(1)` error in normalized Hilbert--Schmidt
square contributes only `o(d)` to each term of `(HPF2)`.  After division by
`d`, the same inequality survives in the limit.  Finally choose `N` with
`(N+1)alpha>1` by a fixed margin, then choose `L` so the geometric tail is
smaller than that margin.  This proves `(HPO3)` and the asymptotic
contradiction.

