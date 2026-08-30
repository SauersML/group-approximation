---
rg: 2
id: stw74-every-matrix-descent-threshold-occurs-subhomogeneously
kind: claim
title: Every finite matrix-projection descent threshold occurs in a projectionless subhomogeneous algebra
distinct_from:
  stw74-counterexamples-have-stationary-matrix-thresholds: that proves a counterexample to LXXIV has one stationary first projection level; this constructs an explicit type-I coefficient algebra realizing every possible finite first level.
  stw74-homogeneous-coefficient-projections-descend: that gives stable and homogeneous-island hypotheses forcing descent; this proves that finite-dimensional fibres and compact primitive spectrum permit an arbitrarily prescribed failure of descent.
  stw74-minimal-projection-has-uniform-gapless-compressions: that analyzes scalar compressions of a minimal stabilized projection in a hypothetical simple counterexample; this computes the exact stabilization threshold in a concrete nonsimple subhomogeneous model.
artifacts:
  - research/artifacts/stw74-property-sp-cu-stability-audit-2026-08-30.md
---

Fix distinct integers `1<=r,s<=N`, let `e_r,e_s in M_N(C)` be projections
of ranks `r,s`, and put

```text
D_(r,s)={f in C([0,1],M_N): f(0) in C e_r, f(1) in C e_s}.
```

Write `g=gcd(r,s)` and

```text
m_0=max(r/g,s/g).
```

Then `D_(r,s)` is projectionless and, for every `k>=1`,

```text
M_k(D_(r,s)) contains a nonzero projection  iff  k>=m_0.      (DT)
```

At the first level `m_0`, one may choose a projection `P` and pass to its
coefficient algebra

```text
C_P=C*(P_ij:1<=i,j<=m_0) subset D_(r,s).
```

The algebra `C_P` is projectionless and subhomogeneous, `P` is full in
`M_(m_0)(C_P)`, `Prim(C_P)` is compact, and `m_0` is still its first matrix
level containing a nonzero projection.

Consequently every prescribed threshold `m>=2` occurs: take
`(r,s,N)=(m-1,m,m)`.  Thus no descent theorem based only on a finite bound
for irreducible dimensions, compact primitive spectrum, fullness of the
stabilized projection, or finiteness of the first stabilization level can
force a level-one projection.

The theorem `stw74-graph-rank-lcm-controls-matrix-threshold` extends the
calculation from an interval to arbitrary finite connected graphs: the exact
threshold is the least common multiple of all vertex ranks divided by the
smallest vertex rank.  Branching and cycles create no additional obstruction.
