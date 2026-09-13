---
rg: 2
id: determinant-counterexample-from-heavy-eigenvalue
kind: route
title: A heavy or transcendental eigenvalue of an integral self-adjoint matrix yields a determinant violation
target: determinant-conjecture-counterexample-exists
requires:
  - integral-matrix-eigenvalue-exceeds-degree-bound
  - heavy-eigenvalue-gives-determinant-counterexample
artifacts:
  - research/artifacts/determinant-spectral-atoms-2026-09-12.md
---

Let `A in M_n(Z[G])` be self-adjoint with an eigenvalue `lambda` of multiplicity
`m > n / deg(lambda)` (`integral-matrix-eigenvalue-exceeds-degree-bound`).
By `heavy-eigenvalue-gives-determinant-counterexample`, the box-principle
polynomial `Q` of degree below `deg(lambda)` satisfies
`det_(N(G)) r_(Q(A)) < 1`. So `G` and `Q(A)` witness
`determinant-conjecture-counterexample-exists`, and `G` is nonsofic.
