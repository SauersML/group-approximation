---
rg: 2
id: high-density-local-sectors-force-one-bcs-gram-proof
kind: route
title: Intersect the local sectors by codimension and apply the one-Gram gap
target: high-density-local-sectors-force-one-bcs-gram
requires:
  - one-gram-vector-decodes-a-finite-bcs-strategy
---

For `p=meet_c q_c`, subspace codimension gives

```text
tr(1-p)<=sum_c tr(1-q_c)=eta.
```

For every involution `B`, its two off-diagonal `p`-corners are
Hilbert--Schmidt orthogonal, so

```text
||[B,p]||_2^2<=2tr(1-p)<=2eta.
```

Since `p=q_cp`, every predicate residual and occurrence residual restricted
to `p` is bounded by its corresponding residual on `q_c`.  The identity

```text
A_(c,x)p-pB_x=(A_(c,x)-B_x)p+[B_x,p]
```

therefore bounds the one-Gram energy at `G=p` by the right side of `(HD4)`.
The established one-Gram gap lower-bounds the same energy by
`Delta tr(p)>=Delta(1-eta)`.  This proves `(HD4)` and its exact-row threshold
`(HD5)`.
