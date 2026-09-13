---
rg: 2
id: serre-class-measures-are-integral-spectral-limits
kind: claim
title: Every Serre-class probability measure on an interval is a weak limit of symmetric integer matrix spectra
refuted_by:
  - serre-class-admits-non-integral-atoms
distinct_from:
  integral-spectral-limits-satisfy-serre-inequalities: that is the proved direction, limits obey the inequalities; this is the converse, that obeying them suffices
  integral-group-ring-spectra-are-integral-limits: that concerns spectra of integral group-ring elements only; this is a statement about arbitrary measures, with no group in it
artifacts:
  - research/artifacts/determinant-conjecture-serre-class-2026-09-11.md
  - research/artifacts/determinant-integer-root-limits-2026-09-12.md
---

**REFUTED** by `serre-class-admits-non-integral-atoms` (2026-09-12). The measure
`1/2 delta_(1/2) + 1/2 arcsine[-4,4]` obeys every Serre inequality. It has an atom
at a non-integer, which no weak limit of integer matrix spectra has, symmetric or
not. The corrected converse is `integer-root-limits-are-galois-balanced-serre-measures`:
the integer-matrix limits are exactly the Serre-class measures whose algebraic
atoms are totally real algebraic integers with equal conjugate masses.

Original statement: for every compact interval `I` and every probability measure
`mu` on `I` with `integral_{Q!=0} log|Q| d mu >= 0` for all nonzero
`Q in Z[x]`, there are symmetric integer matrices of bounded norm whose
normalized eigenvalue counting measures converge weakly to `mu`.

With `determinant-conjecture-iff-serre-class-spectra`, this would have made
`integral-group-ring-spectra-are-integral-limits` equivalent to the determinant
conjecture. The refutation shows what the gap is: Galois balance of eigenvalues
(`integral-group-ring-eigenvalues-are-galois-balanced`).

## Attempts

- **Limits of conjugate distributions.** A. Smith, arXiv:2111.12660v2,
  Theorem 1.5, now read from the PDF (`smith-serre-measures-are-conjugate-limits`).
  Its condition integrates `log|Q|` over zeros too, so it describes atomless
  limits, not the Serre class. Combined with a balance argument it gives the
  corrected converse.
- **Realizing orbits by symmetric integer matrices.** Companion matrices are
  not symmetric. Tree adjacency realizations of totally real algebraic integers
  (cited, not re-read: Salez, JCTB 2015) carry extra eigenvalues with
  uncontrolled mass. The step needed is realization with negligible extra
  spectrum. It is open here, and it is what separates the symmetric form from
  `integral-group-ring-spectra-are-integer-root-limits`.
- **Purely atomic case.** Here the Serre class is exactly equal-weight totally
  real orbits (`atomic-serre-measures-are-equal-weight-real-orbits`). What
  remains is the realization step above.
