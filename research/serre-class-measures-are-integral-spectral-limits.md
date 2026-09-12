---
rg: 2
id: serre-class-measures-are-integral-spectral-limits
kind: claim
title: Every Serre-class probability measure on an interval is a weak limit of symmetric integer matrix spectra
distinct_from:
  integral-spectral-limits-satisfy-serre-inequalities: that is the proved direction, limits obey the inequalities; this is the converse, that obeying them suffices
  integral-group-ring-spectra-are-integral-limits: that concerns spectra of integral group-ring elements only; this is a statement about arbitrary measures, with no group in it
artifacts:
  - research/artifacts/determinant-conjecture-serre-class-2026-09-11.md
---

**OPEN.** For every compact interval `I` and every probability measure `mu` on
`I` with `integral_{Q!=0} log|Q| d mu >= 0` for all nonzero `Q in Z[x]`,
there are symmetric integer matrices of bounded norm whose normalized
eigenvalue counting measures converge weakly to `mu`.

With `determinant-conjecture-iff-serre-class-spectra`, this would make
`integral-group-ring-spectra-are-integral-limits` equivalent to the
determinant conjecture, not stronger.

## Attempts

- **Limits of conjugate distributions.** A. Smith, arXiv:2111.12660, gives a
  necessary and sufficient condition for a measure on a compact set, under
  technical hypotheses, to be a limit of distributions of conjugates of
  algebraic integers. The exact condition was not re-read, so nothing is
  imported and it is not known here whether it equals the Serre inequalities
  on an interval.
- **Realizing orbits by symmetric integer matrices.** Companion matrices are
  not symmetric. Tree adjacency realizations of totally real algebraic integers
  (cited, not re-read: Salez, JCTB 2015) carry extra eigenvalues with
  uncontrolled mass. The step needed is realization with negligible extra
  spectrum. It is open here.
- **Purely atomic case.** Here the Serre class is exactly equal-weight totally
  real orbits (`atomic-serre-measures-are-equal-weight-real-orbits`). What
  remains is the realization step above.
