---
rg: 2
id: atomic-serre-measures-are-equal-weight-real-orbits
kind: claim
title: A purely atomic Serre-class measure on algebraic integers is equal weight on totally real Galois orbits
distinct_from:
  integer-moment-measure-with-negative-log-determinant: that exhibits one measure with integer moments that fails the Serre inequalities; this characterizes every purely atomic measure that satisfies them
  integral-spectral-limits-satisfy-serre-inequalities: that proves the Serre inequalities for limits of integer matrix spectra, with any continuous part; this is an exact characterization of the purely atomic members of the Serre class
artifacts:
  - research/artifacts/determinant-conjecture-serre-class-2026-09-11.md
---

**ESTABLISHED (written proof, artifact Section 5).** Let `mu` be a
probability measure on `R` supported on finitely many algebraic integers.
Then `integral_{Q!=0} log|Q| d mu >= 0` for every nonzero `Q in Z[x]` if and
only if every atom is totally real and each Galois orbit carries equal mass
on its conjugates.

Consequence for the determinant conjecture: if `A in M_n(Z[G])` is
self-adjoint with purely atomic spectrum at algebraic integers, then `G`
satisfies the conjecture for `A` exactly when those atoms are totally real
and Galois-equidistributed. A violation with purely atomic spectrum is one
atom whose von Neumann multiplicity differs from a conjugate's.
