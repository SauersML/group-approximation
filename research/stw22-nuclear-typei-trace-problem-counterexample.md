---
rg: 2
id: stw22-nuclear-typei-trace-problem-counterexample
kind: claim
title: A separable unital nuclear type-I algebra has a uniform tracial completion with a discontinuous trace
artifacts:
  - research/artifacts/stw22-trace-problem-counterexample-audit-2026-08-31.md
  - research/artifacts/stw22-chern-commutator-width-audit-2026-08-31.md
distinct_from:
  stw22-finite-dimensional-factor-bundles-have-uniform-traces: that positive theorem assumes finite covering dimension; the present counterexample has a compact metrizable Bauer extreme boundary containing CP^(s^2) for every s and therefore infinite covering dimension.
  stw22-fixed-replication-blocks-infinite-dimensional-selection: that theorem only blocks one infinite-dimensional selection strategy; the present theorem produces an actual rogue trace and therefore refutes the unrestricted trace problem.
---

There exists a separable unital nuclear type-I C-star algebra `A` with
nonempty compact trace space such that, for its uniform tracial completion

```text
M = closure^(||.||_(2,T(A))) A,
```

restriction does not identify the trace spaces and in particular

```text
T(A) proper_subset T(M).                                  (XXII-NEG)
```

More strongly, `T(A)` is Bauer and its extreme boundary is compact and
metrizable. A tracial state on `M` extending the scalar trace at the point
at infinity is not uniform-`2`-norm continuous.

Hence STW Problem XXII / the trace problem has a negative answer, including
in the nuclear case.
