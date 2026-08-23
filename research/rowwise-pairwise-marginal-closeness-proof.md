---
rg: 2
id: rowwise-pairwise-marginal-closeness-proof
kind: route
title: Intersect two row masks and compute the free-product distance
target: rowwise-shared-involution-forces-pairwise-marginal-closeness
requires: []
---

Let `p=q_i meet q_j` in `M`.  The codimension inequality gives

```text
tau(1-p)<=tau(1-q_i)+tau(1-q_j).                       (PIC5)
```

Both equalities in `(PIC1)` hold on `p`, so `(A_i-A_j)p=0`.  Since
`T=(A_i-A_j)/2` is a contraction,

```text
(1/4)||A_i-A_j||_2^2=||T(1-p)||_2^2
 <=tau(1-p),                                           (PIC6)
```

which proves `(PIC2)`.

For distinct free factors, write `A_k=m_k 1+A_k^0`.  The centered alternating
moment vanishes, hence `tau(A_iA_j)=m_i m_j`.  Self-adjoint unitarity gives

```text
||A_i-A_j||_2^2
=tau((A_i-A_j)^2)=2-2m_i m_j.                          (PIC7)
```

Divide by four and combine with `(PIC2)`.
