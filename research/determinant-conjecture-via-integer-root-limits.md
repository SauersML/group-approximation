---
rg: 2
id: determinant-conjecture-via-integer-root-limits
kind: route
title: Integer-matrix approximation of each group-ring spectrum, symmetric or not, forces every Serre inequality
target: determinant-conjecture
requires:
  - integral-group-ring-spectra-are-integer-root-limits
  - integer-root-limits-are-galois-balanced-serre-measures
  - determinant-conjecture-iff-serre-class-spectra
artifacts:
  - research/artifacts/determinant-integer-root-limits-2026-09-12.md
---

If every self-adjoint integral spectrum `mu_A` is a limit of eigenvalue
distributions of integer matrices with real spectrum, then
`integer-root-limits-are-galois-balanced-serre-measures` puts `mu_A` in the Serre
class, and `determinant-conjecture-iff-serre-class-spectra` gives
`det_(N(G))(B) >= 1` for every integral matrix `B`.

This weakens the prerequisite of `determinant-conjecture-via-integral-spectral-approximation`:
the approximants need integral characteristic polynomials and real spectrum, not
symmetry. The cycle with `integer-root-limits-from-determinant-and-galois-balance`
is intended.
