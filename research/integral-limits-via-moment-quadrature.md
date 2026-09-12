---
rg: 2
id: integral-limits-via-moment-quadrature
kind: route
title: Approximate each group-ring spectrum by integer Jacobi-matrix quadratures built from its moments
target: integral-group-ring-spectra-are-integral-limits
requires: []
artifacts:
  - research/artifacts/determinant-conjecture-serre-class-2026-09-11.md
---

**Dead.** The idea: the moments of `mu_A` are integers, so truncated Gauss
quadratures have algebraic nodes, and Jacobi matrices might supply integral
approximants.

The quadrature weights need not be Galois-equal. The Jacobi matrices have
non-integral entries, and their counting measures do not converge to `mu_A`.
Worse, any scheme that uses only the moments must fail: the integer-moment
Fibonacci measure is its own two-node quadrature and violates the Serre
inequalities (`integer-moment-measure-with-negative-log-determinant`). A viable
scheme has to use the group, or Galois equidistribution of spectral mass.
