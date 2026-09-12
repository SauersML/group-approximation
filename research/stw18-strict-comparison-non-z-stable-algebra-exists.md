---
rg: 2
id: stw18-strict-comparison-non-z-stable-algebra-exists
kind: claim
title: A simple separable nuclear non-elementary C*-algebra with strict comparison that is not Z-stable exists
root: true
distinct_from:
  stw99-problem-xviii-toms-winter-conjecture: that is the universal positive assertion of STW Problem XVIII; this is its negation, recorded as its own root so that counterexample routes have a target.
artifacts:
  - research/artifacts/stw18-k1-route-constraint-map-2026-09-11.md
---

**OPEN.** There is a simple, separable, nuclear, non-elementary C*-algebra
`A` with strict comparison of positive elements, with respect to a nonempty
quasitrace simplex, such that `A` is not isomorphic to `A tensor Z`.

Establishing this refutes `stw99-problem-xviii-toms-winter-conjecture`, which
lists this claim under `refuted_by`. It is the negation root of that problem,
in the same pattern as the Benjamini--Schramm and fixed-price counterexample
roots.

Known strata where no such algebra exists:

- compact finite-dimensional extreme tracial boundary
  (`stw18-finite-trace-boundary-toms-winter`);
- Lin's condition (C) boundaries
  (`lin-condition-c-boundary-strict-comparison-z-stable`);
- unital simple AH algebras (`simple-ah-strict-comparison-is-z-stable`).

## Attempts

- **K1 route.** Produce a unital witness that is not K1-injective; Jiang then
  gives non-Z-stability. Recorded as
  `stw18-counterexample-from-k1-witness` over the open claim
  `stw18-k1-witness-strict-comparison-not-k1-injective`. Its AH form, a
  strict-comparison upgrade of the LIX towers, is dead by
  `simple-ah-strict-comparison-is-k1-injective`. Any surviving witness must
  also refute the Rank Problem (`stw18-k1-witness-constraints`).
- **Uniform property Gamma.** Toms's AH algebra without uniform property Gamma
  cannot serve: it fails strict comparison
  (`toms-gamma-counterexample-fails-strict-comparison`).
- **Tracial shadow of a witness (2026-09-12).** In the unital case a witness
  lacks uniform Gamma (`uniform-gamma-algebras-satisfy-toms-winter`).  Yet by
  `strict-comparison-compares-ultrapower-projections` its uniform tracial
  ultrapower compares projections by limit traces in every matrix amplification,
  as a CPoU algebra would.
  - So no certificate of the form "projections with dominated traces that are
    not subequivalent" can exhibit a witness.  That excludes Villadsen
    Euler-class gaps and Toms's Thom--Porteous degeneracy loci in every class of
    building blocks.
  - The obstruction must be invisible to projection comparison:
    `gamma-failure-invisible-to-projection-comparison`.
  - With locally finite nuclear dimension it must also fail rank density, so its
    tracial ultrapower lacks projections of some continuous trace profile while
    comparing all the projections it has.
  See `research/artifacts/toms-winter-tracial-ultrapower-comparison-2026-09-12.md`.
