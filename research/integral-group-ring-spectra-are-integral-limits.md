---
rg: 2
id: integral-group-ring-spectra-are-integral-limits
kind: claim
title: Every self-adjoint integral group-ring spectrum is a weak limit of symmetric integer matrix spectra
distinct_from:
  determinant-conjecture-iff-serre-class-spectra: that is an exact reformulation of the conjecture; this is an approximation property that implies it, may be strictly stronger, and involves no approximation of the group
  integral-spectral-limits-satisfy-serre-inequalities: that proves the limit measures obey the Serre inequalities; this asks that group-ring spectra actually be such limits
artifacts:
  - research/artifacts/determinant-conjecture-serre-class-2026-09-11.md
---

**OPEN.** For every group `G`, every `n`, and every self-adjoint
`A in M_n(Z[G])`, the spectral measure `mu_A` is a weak limit of normalized
eigenvalue counting measures of symmetric integer matrices of uniformly
bounded norm.

Soficity gives this for `G` sofic (models of `A` are integer matrices). The
property itself is one-variable: the approximants need not come from any
action or approximation of `G`, only from integer matrices whose spectra
imitate one measure.

It implies the determinant conjecture through
`integral-spectral-limits-satisfy-serre-inequalities`. It may be strictly
stronger. The converse would need a characterization of the Serre class as
limits of totally real Galois orbits, plus realizing those orbits by symmetric
integer matrices. Neither is established here.

## Attempts

- **Sofic models.** Give the claim exactly for sofic groups, and cannot
  reach the binary Leavitt unit group, the Kun--Thom wreaths, or Fournier-Facio's
  group.
- **Finite quotients of a Kun--Thom wreath.** Approximate a proper quotient
  trace, not `mu_A`, because the non-normal Kazhdan subgroup is not profinitely
  closed (artifact Section 4).
- **Next attack, untried.** Build integer approximants from the spectral
  measure alone. Truncate the moment problem of `mu_A` at order `2j`, whose
  moments are integers. Realize a Gauss quadrature on `j` nodes by an integer
  Jacobi-type matrix with Galois-equidistributed eigenvalues. Then let `j` grow.
  The obstruction to watch is
  `integer-moment-measure-with-negative-log-determinant`: quadrature nodes are
  algebraic but their weights need not be Galois-equal.
