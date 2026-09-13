---
rg: 2
id: zaremsky-2-08-infinite-dim-torsion-free-f-infinity-without-f
kind: claim
title: "Zaremsky Problem 2.8 resolved: is there an infinite-dimensional torsion-free group of type F_infinity with no copy of Thompson's group F?"
root: true
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 2, Problem 8, verbatim:
"Find an infinite dimensional torsion-free group of type F∞ that does not
contain F."

This claim is the question. It is established only through an answer route:

- **Construction**: `zaremsky-2-08-by-construction` requires
  `some-torsion-free-f-infinity-group-of-infinite-cd-omits-f`.
- **Nonexistence**: `zaremsky-2-08-by-nonexistence` requires
  `every-torsion-free-f-infinity-group-of-infinite-cd-contains-f`.

Never write a `requires: []` route into this claim.

## Reading

- **Type F_∞**: some K(G,1) has finitely many cells in each dimension.
- **Infinite dimensional**: no finite-dimensional K(G,1). For a torsion-free
  group this means `cd G = ∞`. A K(G,1) of dimension `d` gives `cd G <= d`.
  Conversely, by Eilenberg–Ganea, `cd G = n` gives a K(G,1) of dimension
  `max(n, 3)`. The Wall finiteness obstruction concerns *finite* complexes, not
  finite-dimensional ones, so it plays no role in this reading. This region uses
  `cd G = ∞`.
- **Does not contain F**: no subgroup of `G` is isomorphic to Thompson's group `F`.

## Calibration

- `F` is torsion-free, of type F_∞, and has infinite cohomological dimension
  (Brown–Geoghegan, Invent. Math. 77 (1984)). It satisfies everything except the
  last clause.
- `Z^n` is torsion-free, of type F, and omits `F`, but it is finite-dimensional.

So the problem asks for a torsion-free infinite-dimensional F_∞ group that does
not come from Thompson-like groups, all of which contain `F`.

## Where an answer cannot live (survey, import statements pending verification)

- Kropholler (J. Pure Appl. Algebra 90 (1993)): torsion-free groups of type
  FP_∞ in his class LH𝔉 have finite cohomological dimension. `F` is the standard
  example outside LH𝔉. So an answer lies outside LH𝔉. In particular it is not
  elementary amenable, and it admits no action on a finite-dimensional
  contractible complex with LH𝔉 stabilizers.
- A subgroup of `F` answering the problem would be a non-elementary-amenable
  subgroup of `F` without a copy of `F`. That is a counterexample to the
  Brin–Sapir conjecture (Problem 2.3).
- Residually finite groups, and groups satisfying the Tits alternative, never
  contain `F`. A residually finite answer, or one satisfying the Tits
  alternative, therefore needs no separate proof of the last clause.

## Attempts

- 2026-09-13 (lane z2-08-tf-finf-no-f): region opened. Dead candidate classes:
  - Thompson-like groups, including braided, cloning-system, Stein, Lodha–Moore,
    Monod and Brin–Thompson variants, all contain `F`.
  - Elementary amenable groups have finite cd once they are of type FP_∞.
  - `SL_n(Z[t])` has torsion-free finite-index subgroups of infinite
    cohomological dimension, but it is not of type FP_{n−1}
    (Bux–Mohammadi–Wortman, Comment. Math. Helv. 2010).

  Reductions (residual finiteness, Tits alternative) and the obstruction table
  are being written up.
