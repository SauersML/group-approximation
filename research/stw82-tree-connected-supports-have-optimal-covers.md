---
rg: 2
id: stw82-tree-connected-supports-have-optimal-covers
kind: claim
title: Compact R-tree support components admit pointwise-optimal recolouring
distinct_from:
  stw82-finite-dimensional-central-spectrum-colour-bound: that theorem uses (n+1)m colours on an n-dimensional common support spectrum, hence 2m in dimension one; this theorem uses only m on an arbitrary compact metric R-tree even when every cozero support is disconnected.
  stw82-indivisible-order-zero-reuse-is-graph-colouring: that keeps every outgoing map intact and is governed by the global support-overlap graph; this theorem splits maps over cozero components and can use fewer colours than that graph's chromatic number.
  stw82-zero-dimensional-central-supports-recolour-pointwise: that splits over clopen blocks of a zero-dimensional spectrum; this theorem works over genuine one-dimensional compact R-trees, using compactly supported Urysohn cutters inside cozero components.
  stw82-coupled-operator-partitions-merge-colours: that assumes suitable support-local cutters; this theorem constructs them from compact R-tree geometry.
artifacts:
  - research/artifacts/stw82-tree-connected-support-covers-audit-2026-08-30.md
---

Let `T` be a compact metric R-tree and let

```text
C ~= C(T) subseteq M(B) intersect (union_v phi_v(F_v))'
```

be a unital abelian C-star algebra centralizing the ranges of finitely many
c.p.c. order-zero maps

```text
phi_v:F_v->B,
```

where the `F_v` are unital.  Suppose `h_v=phi_v(1)` belongs to `C`, discard
the zero maps, and assume that the original direct-sum outgoing map

```text
phi:directSum_v F_v->B,       phi((x_v))=sum_v phi_v(x_v),
```

is c.p.c.  Equivalently, `sum_v h_v<=1`.  Put

```text
m=max_(t in T) |{v:h_v(t)>0}|.                         (T1)
```

No connectedness hypothesis is imposed on the cozero sets of the `h_v`.
For every `epsilon>0`, there are positive contractions
`c_(v,k) in C`, for `k=1,...,m`, such that

```text
sum_k c_(v,k)<=1,
norm((1-sum_k c_(v,k))h_v)<epsilon,                    (T2)
c_(v,k)c_(w,k)=0                            (v!=w).    (T3)
```

The cut maps

```text
psi_(v,k)(x)=c_(v,k)phi_v(x)
```

are c.p.c. order zero, approximate each `phi_v` by their sum within
`epsilon`, and for each fixed `k` their direct sum over `v` is c.p.c. order
zero.  The number `m` is optimal among asymptotically exact coupled covers
whose cutters lie in `C`.

If instead every cozero set `{h_v>0}` is connected, the same conclusion
holds without assuming that all of `C` centralizes the outgoing ranges: one
may use a single functional-calculus cutter for each `v`.  Thus the theorem
strictly retains the earlier connected-support result while adding arbitrary
disconnected supports under the common-centralizer hypothesis.

Consequently, if a C-star algebra `A` has arbitrarily accurate
finite-dimensional nuclear approximations whose outgoing unit supports have
this common compact-R-tree centralizing geometry and pointwise multiplicity at
most `r+1`, then

```text
dim_nuc(A)<=r.                                          (T4)
```

The component splitting can beat indivisible graph colouring.  On an
interval choose three nonzero positive contractions `a,b,c` with pairwise
disjoint cozero sets and put

```text
h_1=(a+c)/2,       h_2=(a+b)/2,       h_3=(b+c)/2.
```

The three unsplit supports have overlap graph `K_3`, but their pointwise
multiplicity is two; the theorem splits their six components and recolours
them with two labels.
