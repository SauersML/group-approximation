---
rg: 2
id: atlas-matricial-trace-separator-route
kind: route
title: Refute hyperlinearity of the explicit atlas presentation by one all-dimensions matrix inequality
target: non-hyperlinear-group
requires:
  - atlas-steinberg-rank-five-translation
  - atlas-matricial-trace-separator
artifacts:
  - research/artifacts/nonhyperlinear-random-presentation-and-matricial-separator-2026-08-18.md
---

The established atlas translation gives a completely explicit finite
presentation `Gamma_St`.  If `atlas-matricial-trace-separator` holds, every
finite-dimensional unitary tuple obeys the robust trace-polynomial inequality,
whereas the canonical group trace violates its zero-relator-defect limit by a
fixed amount `c`.

A hyperlinear embedding of `Gamma_St` would supply matrix microstates whose
relator penalties tend to zero and whose fixed trace words converge to the
canonical group trace.  Passing to the limit in the matrix inequality gives the
opposite of the certified negative canonical value.  Hence `Gamma_St` is an
explicit nonhyperlinear group.

This route uses the atlas only as a finite list of polynomial relations; none
of the existing Leavitt multiplication decoder, Pauli carrier, PVM rounding,
commutant synchronization, scale-index or stability machinery is invoked.
