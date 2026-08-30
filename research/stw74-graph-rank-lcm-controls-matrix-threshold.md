---
rg: 2
id: stw74-graph-rank-lcm-controls-matrix-threshold
kind: claim
title: Vertex-rank least common multiples exactly control projection thresholds over finite graphs
distinct_from:
  stw74-every-matrix-descent-threshold-occurs-subhomogeneously: that computes the two-endpoint interval and realizes every single threshold; this gives the simultaneous arithmetic for any finite connected graph and any finite vertex-rank pattern.
  stw74-homogeneous-coefficient-projections-descend: that gives positive descent hypotheses and a two-endpoint boundary example; this shows that branching and cycles introduce no extra projection obstruction beyond the vertex-rank least common multiple.
artifacts:
  - research/artifacts/stw74-property-sp-cu-stability-audit-2026-08-30.md
---

Let `X` be a finite connected graph with vertices `v_1,...,v_t`.  Fix
projections `e_i in M_N(C)` of ranks `r_i>=1` and put

```text
D(X;r)={f in C(X,M_N): f(v_i) in C e_i for every i}.
```

Write

```text
L=lcm(r_1,...,r_t),
m_0=max_i L/r_i=L/min_i r_i.
```

Then, for every `k>=1`,

```text
M_k(D(X;r)) contains a nonzero projection  iff  k>=m_0.       (GL)
```

In particular, `D(X;r)` is projectionless exactly when the vertex ranks are
not all equal.  When this holds, choose a projection `P` at the first level
`m_0` and form its coefficient algebra

```text
C_P=C*(P_ab:1<=a,b<=m_0) subset D(X;r).
```

Then `C_P` is projectionless and subhomogeneous, `P` is full in
`M_(m_0)(C_P)`, `Prim(C_P)` is compact, and `m_0` remains the first matrix
level over `C_P` containing a nonzero projection.

Thus all branching and cycle data disappear from the stabilization
threshold: the complete invariant for this graph family is the least common
multiple of the constrained vertex ranks.  The interval formula is the
two-vertex special case.
