---
rg: 2
id: stw82-tree-connected-supports-have-optimal-covers
kind: claim
title: Connected supports over a finite tree have pointwise-optimal coupled covers
distinct_from:
  stw82-spectral-interval-band-depth-reuses-colours: that localizes supports in prescribed intervals arising from one functional-calculus variable and keeps the maps intact; this treats arbitrary commuting support functions on a branched finite tree and constructs support-local cutters.
  stw82-indivisible-order-zero-reuse-is-graph-colouring: that computes the global overlap-graph obstruction for fixed maps; this derives an optimal colouring from local tree depth and constructs functional-calculus cutters which discard only the vanishing boundary.
  stw82-coupled-operator-partitions-merge-colours: that assumes full-unit coupled partitions and repairs their pieces; this constructs support-local cutters directly from connected tree geometry.
artifacts:
  - research/artifacts/stw82-tree-connected-support-covers-audit-2026-08-30.md
---

Let `T` be a finite compact tree and let `C≅C(T)` be a unital abelian
C*-subalgebra of `M(B)`.  For a finite set `V`, let

```text
phi_v:F_v→B
```

be cpc order-zero maps from unital C*-algebras, with
`h_v=phi_v(1)∈C`.  Discard the zero maps and suppose every cozero support

```text
U_v={t∈T:h_v(t)>0}
```

is connected.  Put

```text
m=max_(t∈T) |{v:h_v(t)>0}|.                       (T1)
```

For every `epsilon>0` there are positive contractions
`c_(v,k)∈C`, for `k=1,...,m`, such that

```text
norm((1-sum_k c_(v,k))h_v)<epsilon,                 (T2)
[c_(v,k),phi_v(x)]=0,                               (T3)
c_(v,k)c_(w,k)=0                         (v!=w).     (T4)
```

Each `v` uses only one nonzero cutter.  The cut maps

```text
psi_(v,k)(x)=c_(v,k)phi_v(x)
```

are cpc order zero, approximate every `phi_v` within `epsilon`, and for
each fixed `k` their direct sum over `v` is cpc order zero.  Thus these
supports have an asymptotically exact support-local coupled cover with the
pointwise-optimal number `m` of labels.  Optimality here is among covers
whose cutters lie in `C`.

Consequently, if a C*-algebra `A` has arbitrarily accurate
finite-dimensional nuclear approximations whose outgoing unit supports
have this common finite-tree geometry with multiplicity at most `r+1`, then

```text
dim_nuc(A)≤r.                                        (T5)
```

For one-dimensional spectra this improves the general central-spectrum
bound from `2m` colours to `m` under a concrete connected-support
hypothesis.
