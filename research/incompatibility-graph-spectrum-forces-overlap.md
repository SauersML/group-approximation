---
rg: 2
id: incompatibility-graph-spectrum-forces-overlap
kind: claim
title: The least adjacency eigenvalue of the incompatibility graph lower-bounds total pairwise overlap
artifacts:
  - research/artifacts/pauli-overlap-dichotomy-2026-08-20.md
distinct_from:
  marked-copy-collision-forces-overlap-mass: that is the complete-graph case, where every pair of copies is required to be incompatible; this weights the pairs by an arbitrary regular graph and the bound degrades gracefully through its least eigenvalue, so a bounded-degree incompatibility pattern suffices.
  bounded-overlap-syndrome-energy-accounting: that bounds a sum of local charges above by relator energy given bounded incidence; this bounds a sum of pairwise overlaps below given a spectral condition on the incidence pattern.
---

Let `(M,tau)` be a finite tracial von Neumann algebra and let `Q_1,...,Q_m` be
projections with `tau(Q_i) = beta` for every `i`.  They are **not** assumed to
commute.  Let `G` be an `r`-regular graph on `{1,...,m}` with adjacency matrix
`A` and least eigenvalue `lambda_min`.  Then

```text
sum_({i,j} in E(G)) tau(Q_i Q_j)
    >= (m/2) beta ( r beta + lambda_min (1 - beta) ).                (IGS1)
```

**Complete graph.**  With `r = m-1` and `lambda_min = -1`, `(IGS1)` becomes

```text
sum_(i<j) tau(Q_i Q_j) >= (m/2) beta (m beta - 1),                   (IGS2)
```

which is `marked-copy-collision-forces-overlap-mass` in unordered form.

**Marked instance.**  At the regular-character scale a marked word gives
`beta >= 3/7` by `marked-hs-separation-forces-spectral-density`, so `m=3`
copies already have `m beta = 9/7 > 1` and

```text
sum_(i<j) tau(Q_i Q_j) >= (3/2)(3/7)(2/7) = 9/49.                    (IGS3)
```

**Why the spectral form matters.**  `(IGS2)` requires every pair of copies to be
incompatible, which for many copies is a complete-graph condition and is
expensive to arrange in a group presentation.  `(IGS1)` says a bounded-degree
incompatibility pattern suffices as long as its least eigenvalue is not too
negative: for a `d`-regular Ramanujan-type graph, `lambda_min` is close to
`-2 sqrt(d-1)` and `(IGS1)` is positive once `beta > 2 sqrt(d-1) / (d + 2 sqrt(d-1))`.
So the construction problem is a bounded-degree one, which is the regime
`bounded-overlap-syndrome-energy-accounting` is designed to consume.
