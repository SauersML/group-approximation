---
rg: 2
id: atomic-serre-measures-equal-weight-proof
kind: route
title: Kill the other orbits with their minimal polynomials and test against the units of Z[alpha]
target: atomic-serre-measures-are-equal-weight-real-orbits
requires: []
artifacts:
  - research/artifacts/determinant-conjecture-serre-class-2026-09-11.md
---

Sufficiency: a nonvanishing `Q` contributes `w log|N(Q(alpha))| >= 0` per
orbit. Necessity: multiply the minimal polynomials of the other orbits by
`R_k` with `R_k(alpha)=u^k` for a unit `u` of `Z[alpha]`, and let `k` range
over `Z`. The weights annihilate the logarithmic unit lattice, which spans the
trace-zero hyperplane by Dirichlet. So they are constant, and zero whenever
there is a complex place.
