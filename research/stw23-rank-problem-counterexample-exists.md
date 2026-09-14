---
rg: 2
id: stw23-rank-problem-counterexample-exists
kind: claim
title: A unital simple separable stably finite non-elementary C*-algebra in which not all ranks occur exists
root: true
distinct_from:
  stw99-problem-xxiii-rank-problem: that is the universal assertion of STW Problem XXIII; this is its negation, recorded as its own root so that counterexample routes have a target.
artifacts:
  - research/artifacts/stw18-k1-route-constraint-map-2026-09-11.md
---

**OPEN.** There is a unital, simple, separable, stably finite,
non-elementary C*-algebra `A` and a lower semicontinuous affine function
`f: QT(A) -> (0, infinity]` such that no positive `a in A tensor K` has
`d_tau(a) = f(tau)` for every quasitrace `tau`.

Establishing this refutes `stw99-problem-xxiii-rank-problem`, which lists
this claim under `refuted_by`. The XXIII root records the known positive
cells: stable rank one, finitely many extremal quasitraces, Z-stable algebras,
and the Dadarlat--Toms compact finite-dimensional case.

## Attempts

- **Through a strict-comparison K1-witness.**
  `stw23-counterexample-from-stw18-k1-witness`: by Lin's theorem a
  strict-comparison algebra that is not K1-injective has a non-surjective rank
  map. This makes the XVIII K1 route and this root share one hard open
  prerequisite, `stw18-k1-witness-strict-comparison-not-k1-injective`. No
  candidate is known.
