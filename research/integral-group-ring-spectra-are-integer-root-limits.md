---
rg: 2
id: integral-group-ring-spectra-are-integer-root-limits
kind: claim
title: Every self-adjoint integral group-ring spectrum is a weak limit of eigenvalue distributions of integer matrices with real spectrum
distinct_from:
  integral-group-ring-spectra-are-integral-limits: that asks for symmetric integer approximants; this allows any integer matrix with real spectrum, is implied by that, and is equivalent to the determinant conjecture together with Galois balance of eigenvalues
  determinant-conjecture: that is the Serre inequalities alone; this adds integral, Galois-balanced atoms and is equivalent to the conjunction
artifacts:
  - research/artifacts/determinant-integer-root-limits-2026-09-12.md
---

**OPEN.** For every group `G` and every self-adjoint `A in M_n(Z[G])`, there are
`C > 0` and integer matrices with real spectrum in `[-C, C]` whose normalized
eigenvalue distributions converge weakly to `mu_A`.

**Exact content.** By `integer-root-limits-are-galois-balanced-serre-measures`,
for each group `G` this holds iff
- `G` satisfies Lück's determinant conjecture, and
- `integral-group-ring-eigenvalues-are-galois-balanced` holds for `G`.

Routes:
- `integer-root-limits-from-determinant-and-galois-balance` (the conjunction
  gives this);
- `determinant-conjecture-via-integer-root-limits` and
  `galois-balance-from-integer-root-limits` (this gives each conjunct);
- `integer-root-limits-from-symmetric-integral-limits` (symmetric approximants
  give this).

The two-way routes with `determinant-conjecture` form an intended cycle
recording an equivalence. A least fixpoint establishes neither claim from the
cycle alone.

**Known case.** Sofic groups: their models of `A` are integer matrices.

## Attempts

- **Moment-only schemes.** Dead: `integral-limits-via-moment-quadrature`.
- **The Serre converse.** The whole Serre class is not reachable
  (`serre-class-admits-non-integral-atoms`). The approximants must see balanced
  integral atoms, and nothing else is needed.
