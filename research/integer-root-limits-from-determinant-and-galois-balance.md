---
rg: 2
id: integer-root-limits-from-determinant-and-galois-balance
kind: route
title: The determinant conjecture puts each spectrum in the Serre class, balance adds balanced atoms, and the characterization makes it an integer root limit
target: integral-group-ring-spectra-are-integer-root-limits
requires:
  - determinant-conjecture
  - integral-group-ring-eigenvalues-are-galois-balanced
  - integer-root-limits-are-galois-balanced-serre-measures
  - determinant-conjecture-iff-serre-class-spectra
artifacts:
  - research/artifacts/determinant-integer-root-limits-2026-09-12.md
---

Let `A in M_n(Z[G])` be self-adjoint.
1. **Serre class.** `determinant-conjecture` puts `mu_A` in the Serre class
   (`determinant-conjecture-iff-serre-class-spectra`).
2. **Balance.** The atoms of `mu_A` are the eigenvalues of `r_A`, with masses
   `dim ker / n`. `integral-group-ring-eigenvalues-are-galois-balanced` makes
   them balanced totally real algebraic integers.
3. **Characterization.** By `integer-root-limits-are-galois-balanced-serre-measures`,
   `mu_A` is a limit of eigenvalue distributions of integer matrices with real
   spectrum in a fixed interval.

With `determinant-conjecture-via-integer-root-limits` this forms an intended
equivalence cycle.
