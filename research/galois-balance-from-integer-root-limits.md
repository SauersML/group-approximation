---
rg: 2
id: galois-balance-from-integer-root-limits
kind: route
title: Limits of integer-matrix spectra have balanced totally real integral atoms, so integer approximation of every spectrum gives Galois balance
target: integral-group-ring-eigenvalues-are-galois-balanced
requires:
  - integral-group-ring-spectra-are-integer-root-limits
  - integer-root-limits-are-galois-balanced-serre-measures
artifacts:
  - research/artifacts/determinant-integer-root-limits-2026-09-12.md
---

Let `A in M_n(Z[G])` be self-adjoint with eigenvalue `lambda`, of multiplicity
`m`. Then `mu_A({lambda}) = m/n`. If `mu_A` is an integer root limit, Section 2.2
of the artifact (`integer-root-limits-are-galois-balanced-serre-measures`) makes
`lambda` a totally real algebraic integer whose conjugates carry the same mass
`m/n`. So every conjugate is an eigenvalue of the same multiplicity.
